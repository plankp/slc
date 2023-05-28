(* This (confusingly named) module turns HIR to LIR plus a few things:
 * -  global names are prefixed as necessary
 * -  constants are allocated as globals if possible
 *)

open Hir
open Lir
open Printf

module M = Map.Make (Int)

let mangle_globl_name ?(prefix="slmod") mname n =
  sprintf "%s_%s_%s" prefix mname n

let rec lower_value id prog mname sv sk contk conth instrs = function
  | LetExtn (v, extn, n, e) ->
    let id, t1 = Z.succ id, Z.to_string id in
    let name = mangle_globl_name extn n in
    Cnode.add_before instrs [ILoad (t1, Globl name)];
    lower_value id prog mname (M.add v (Local t1) sv) sk contk conth instrs !e

  | LetPack (v, [], e) ->
    lower_value id prog mname (M.add v (Int64 0L) sv) sk contk conth instrs !e

  | LetPack (v, elts, e) ->
    let (constant, elts) = List.fold_left (fun (constant, acc) (flag, e) ->
      let e = M.find e sv in
      let constant = match flag, e with
        | true, _ | _, Local _ -> (* has mutable fields or uses a local *)
          false
        | _ -> constant in
      (constant, e :: acc)) (true, []) elts in
    let elts = List.rev elts in

    let id, t1 = Z.succ id, Z.to_string id in
    if constant then begin
      (* allocate it as a global constant *)
      let name = mangle_globl_name ~prefix:"gval" mname t1 in
      let prog = Lir.M.add name (Tuple elts) prog in
      lower_value id prog mname (M.add v (Globl name) sv) sk contk conth instrs !e
    end else begin
      (* register the value as a local computation *)
      Cnode.add_before instrs [IPack (t1, elts)];
      lower_value id prog mname (M.add v (Local t1) sv) sk contk conth instrs !e
    end

  | LetCons (v, i, elts, e) ->
    let (constant, elts) = List.fold_left (fun (constant, acc) e ->
      let e = M.find e sv in
      let constant = match e with
        | Local _ -> false
        | _ -> constant in
      (constant, e :: acc)) (true, []) elts in
    let elts = Int64 (Int64.of_int i) :: List.rev elts in

    let id, t1 = Z.succ id, Z.to_string id in
    if constant then begin
      let name = mangle_globl_name ~prefix:"gval" mname t1 in
      let prog = Lir.M.add name (Tuple elts) prog in
      lower_value id prog mname (M.add v (Globl name) sv) sk contk conth instrs !e
    end else begin
      Cnode.add_before instrs [IPack (t1, elts)];
      lower_value id prog mname (M.add v (Local t1) sv) sk contk conth instrs !e
    end

  | LetProj (v, i, t, e) ->
    let id, t1 = Z.succ id, Z.to_string id in
    let id, t2 = Z.succ id, Z.to_string id in
      Cnode.add_before instrs
        [ IOffs (t1, M.find t sv, Int64.of_int i)
        ; ILoad (t2, Local (t1))
        ];
      lower_value id prog mname (M.add v (Local t2) sv) sk contk conth instrs !e

  | Export xs ->
    let prog = List.fold_left (fun prog (n, v) ->
      let name = mangle_globl_name mname n in
      match M.find v sv with
        | Local _ as v ->
          Cnode.add_before instrs [IStore (v, Globl name)];
          prog
        | v -> Lir.M.add name v prog) prog xs in
    Cnode.add_before instrs [KRetv (Tuple [])];
    (id, prog, Lir.M.empty)

  | Mutate (mem, i, elt, k) ->
    let id, t1 = Z.succ id, Z.to_string id in
    Cnode.add_before instrs
      [ IOffs (t1, M.find mem sv, Int64.of_int i)
      ; IStore (M.find elt sv, Local t1)
      ; KJump (string_of_int k, [])
      ];
    (id, prog, Lir.M.empty)

  | Jmp (j, [v]) when Some j = contk ->
    Cnode.add_before instrs [KRetv (M.find v sv)];
    (id, prog, Lir.M.empty)

  | Jmp (j, [v]) when Some j = conth ->
    Cnode.add_before instrs [KThrow (M.find v sv)];
    (id, prog, Lir.M.empty)

  | Jmp (j, args) ->
    let args = List.map (fun v -> M.find v sv) args in
    Cnode.add_before instrs [KJump (string_of_int j, args)];
    (id, prog, Lir.M.empty)

  | App (f, args, k, h) when Some k = contk && Some h = conth ->
    let args = List.map (fun v -> M.find v sv) args in
    Cnode.add_before instrs [KCall (M.find f sv, args)];
    (id, prog, Lir.M.empty)

  | App (f, args, k, h) when Some h = conth ->
    let id, t1 = Z.succ id, Z.to_string id in
    let args = List.map (fun v -> M.find v sv) args in
    Cnode.add_before instrs
      [ ICall (t1, M.find f sv, args)
      ; KJump (string_of_int k, [Local t1])
      ];
    (id, prog, Lir.M.empty)

  | App (f, args, k, h) ->
    let args = List.map (fun v -> M.find v sv) args in
    let k = if Some k = contk then "exit" else string_of_int k in
    let h = string_of_int h in
    Cnode.add_before instrs [KCatch (M.find f sv, k, h, args)];
    (id, prog, Lir.M.empty)

  | LetCont (bs, e) ->
    let sk = List.fold_left (fun sk (k, args, _) ->
      M.add k (List.length args) sk) sk bs in

    let (id, prog, m) = lower_value id prog mname sv sk contk conth instrs !e in
    let (id, prog, m) = List.fold_left (fun (id, prog, m) (k, args, e) ->
      let k = string_of_int k in
      let (id, sv, args) = List.fold_left (fun (id, sv, acc) arg ->
        let id, n = Z.succ id, Z.to_string id in
        (id, M.add arg (Local n) sv, n :: acc)) (id, sv, []) args in
      let instrs = Cnode.new_node KDead in
      let (id, prog, m') = lower_value id prog mname sv sk contk conth instrs !e in
      let instrs =
        let next = instrs.next in
        Cnode.unlink instrs;
        next in
      let m = Lir.M.fold Lir.M.add m' m in
      (id, prog, Lir.M.add k (List.rev args, instrs) m)) (id, prog, m) bs in
    (id, prog, m)

  | LetFun ((f, args, k', h', body), e) ->
    let id, t1 = Z.succ id, Z.to_string id in
    let name = mangle_globl_name mname t1 in
    let (id, prog) = lower_function id prog mname sv name args (Some k') (Some h') body in
    lower_value id prog mname (M.add f (Globl name) sv) sk contk conth instrs !e

  | LetRec (bs, e) ->
    let (id, sv) = List.fold_left (fun (id, sv) (f, _, _, _, _) ->
      let f' = id |> Z.to_string |> mangle_globl_name mname in
      (Z.succ id, M.add f (Globl f') sv)) (id, sv) bs in

    let (id, prog) = List.fold_left (fun (id, prog) (f, args, k', h', body) ->
      let name = match M.find f sv with
        | Globl n -> n
        | _ -> failwith "INVALID STATE" in
      lower_function id prog mname sv name args (Some k') (Some h') body) (id, prog) bs in
    lower_value id prog mname sv sk contk conth instrs !e

  | Case (v, cases) ->
    let id, t1 = Z.succ id, Z.to_string id in
    let id, t2 = Z.succ id, Z.to_string id in
    let scrutinee = M.find v sv in

    (* synthesize the intermediate blocks for unpacking fields *)
    let tmp = id in
    let (id, m, tbl) = Hir.M.fold (fun k v (id, m, tbl) ->
      match k with
        | None -> (id, m, tbl)  (* ignore default case for now *)
        | Some k ->
          let j = Printf.sprintf "case%a.%u" Z.sprint tmp k in
          let instrs = Cnode.new_node KDead in
          let id =
            if Some v = contk then begin
              let id, t1 = Z.succ id, Z.to_string id in
              let id, t2 = Z.succ id, Z.to_string id in
              Cnode.add_before instrs
                [ IOffs (t1, scrutinee, Int64.one)
                ; ILoad (t2, Local t1)
                ; KRetv (Local t2)
                ];
              id
            end else if Some v = conth then begin
              let id, t1 = Z.succ id, Z.to_string id in
              let id, t2 = Z.succ id, Z.to_string id in
              Cnode.add_before instrs
                [ IOffs (t1, scrutinee, Int64.one)
                ; ILoad (t2, Local t1)
                ; KThrow (Local t2)
                ];
              id
            end else begin
              let rec loop id offs args arity =
                if arity = 0 then begin
                  Cnode.add_before instrs [KJump (string_of_int v, List.rev args)];
                  id
                end else
                  let id, t1 = Z.succ id, Z.to_string id in
                  let id, t2 = Z.succ id, Z.to_string id in
                  Cnode.add_before instrs
                    [ IOffs (t1, scrutinee, offs)
                    ; ILoad (t2, Local t1)
                    ];
                  loop id (Int64.succ offs) (Local t2 :: args) (arity - 1) in
              loop id Int64.one [] (M.find v sk)
            end in
          let instrs =
            let next = instrs.next in
            Cnode.unlink instrs;
            next in
          (id, Lir.M.add j ([], instrs) m, (Int64.of_int k, j) :: tbl)
      ) cases (id, Lir.M.empty, []) in

    let default_case = match Hir.M.find_opt None cases with
      | None -> "dead"
      | Some k -> string_of_int k in
    Cnode.add_before instrs
      [ IOffs (t1, scrutinee, Int64.zero)
      ; ILoad (t2, Local t1)
      ; KCase (Local t2, default_case, tbl)
      ];
    (id, prog, m)

  | _ -> failwith "Unsupported lowering"

and lower_function id prog mname sv f args k h e =
  let (id, sv, args) = List.fold_left (fun (id, sv, acc) arg ->
    let id, n = Z.succ id, Z.to_string id in
    (id, M.add arg (Local n) sv, n :: acc)) (id, sv, []) args in

  let instrs = Cnode.new_node KDead in
  let (id, prog, m) = lower_value id prog mname sv M.empty k h instrs !e in

  (* at this point, we have KDead followed by the real instructions.
   * we drop the dummy KDead node *)
  let instrs =
    let next = instrs.next in
    Cnode.unlink instrs;
    next in
  let m = Lir.M.add "entry" ([], instrs) m in
  let n = Z.to_string id in
  let m = Lir.M.add "exit" ([n], Cnode.new_node (KRetv (Local n))) m in
  let m = Lir.M.add "dead" ([], Cnode.new_node KDead) m in
  (id, Lir.M.add f (Label (List.rev args, "entry", m)) prog)

let lower mname e =
  let _ = PassReindex.reindex e in
  match e with
    | Module (v, h, m) ->
      (* we start off by assuming all globals are initialized by runtime,
       * so we assign null slots *)
      let prog = List.fold_left (fun prog v ->
        let name = mangle_globl_name mname v in
        Lir.M.add name (Int64 0L) prog) Lir.M.empty v in
      (* then we lower the initializer, which will gradually replace constant
       * globals with the desired initializer *)
      let name = mangle_globl_name mname "INIT" in
      let (_, prog) = lower_function Z.zero prog mname M.empty name [] None (Some !h) m in
      prog
    | _ -> failwith "INVALID TERM ANCHOR"
