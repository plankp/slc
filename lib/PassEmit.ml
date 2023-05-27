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

let rec lower_value id prog mname sv sk contk conth = function
  | LetExtn (v, extn, n, e) ->
    let id, t1 = Z.succ id, Z.to_string id in
    let (id, prog, m, instrs, tail) = lower_value id prog mname (M.add v (Local t1) sv) sk contk conth !e in
    let name = mangle_globl_name extn n in
    (id, prog, m, ILoad (t1, Globl name) :: instrs, tail)

  | LetPack (v, [], e) ->
    lower_value id prog mname (M.add v (Int64 0L) sv) sk contk conth !e

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
      lower_value id prog mname (M.add v (Globl name) sv) sk contk conth !e
    end else begin
      (* register the value as a local computation *)
      let (id, prog, m, instrs, tail) = lower_value id prog mname (M.add v (Local t1) sv) sk contk conth !e in
      (id, prog, m, IPack (t1, elts) :: instrs, tail)
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
      lower_value id prog mname (M.add v (Globl name) sv) sk contk conth !e
    end else begin
      let (id, prog, m, instrs, tail) = lower_value id prog mname (M.add v (Local t1) sv) sk contk conth !e in
      (id, prog, m, IPack (t1, elts) :: instrs, tail)
    end

  | LetProj (v, i, t, e) ->
    let id, t1 = Z.succ id, Z.to_string id in
    let id, t2 = Z.succ id, Z.to_string id in
    let (id, prog, m, instrs, tail) = lower_value id prog mname (M.add v (Local t2) sv) sk contk conth !e in
    let instrs = IOffs (t1, M.find t sv, Int64.of_int i)
      :: ILoad (t2, Local (t1))
      :: instrs in
    (id, prog, m, instrs, tail)

  | Export xs ->
    let (prog, instrs) = List.fold_left (fun (prog, buf) (n, v) ->
      let name = mangle_globl_name mname n in
      match M.find v sv with
        | Local _ as v -> (prog, IStore (v, Globl name) :: buf)
        | v -> (Lir.M.add name v prog, buf)) (prog, []) xs in
    (id, prog, Lir.M.empty, instrs, KRetv (Tuple []))

  | Mutate (mem, i, elt, k) ->
    let id, t1 = Z.succ id, Z.to_string id in
    let instrs =
      [ IOffs (t1, M.find mem sv, Int64.of_int i)
      ; IStore (M.find elt sv, Local t1)
      ] in
    (id, prog, Lir.M.empty, instrs, KJump (string_of_int k, []))

  | Jmp (j, [v]) when Some j = contk ->
    (id, prog, Lir.M.empty, [], KRetv (M.find v sv))

  | Jmp (j, [v]) when Some j = conth ->
    (id, prog, Lir.M.empty, [], KRetv (M.find v sv))

  | Jmp (j, args) ->
    let args = List.map (fun v -> M.find v sv) args in
    (id, prog, Lir.M.empty, [], KJump (string_of_int j, args))

  | App (f, args, k, h) when Some k = contk && Some h = conth ->
    let args = List.map (fun v -> M.find v sv) args in
    (id, prog, Lir.M.empty, [], KCall (M.find f sv, args))

  | App (f, args, k, h) when Some h = conth ->
    let id, t1 = Z.succ id, Z.to_string id in
    let args = List.map (fun v -> M.find v sv) args in
    let instrs = [ICall (t1, M.find f sv, args)] in
    (id, prog, Lir.M.empty, instrs, KJump (string_of_int k, [Local t1]))

  | App (f, args, k, h) ->
    let args = List.map (fun v -> M.find v sv) args in
    let k = if Some k = contk then "exit" else string_of_int k in
    let h = string_of_int h in
    (id, prog, Lir.M.empty, [], KCatch (M.find f sv, k, h, args))

  | LetCont (bs, e) ->
    let sk = List.fold_left (fun sk (k, args, _) ->
      M.add k (List.length args) sk) sk bs in

    let (id, prog, m, instrs, tail) = lower_value id prog mname sv sk contk conth !e in
    let (id, prog, m) = List.fold_left (fun (id, prog, m) (k, args, e) ->
      let k = string_of_int k in
      let (id, sv, args) = List.fold_left (fun (id, sv, acc) arg ->
        let id, n = Z.succ id, Z.to_string id in
        (id, M.add arg (Local n) sv, n :: acc)) (id, sv, []) args in
      let (id, prog, m', instrs, tail) = lower_value id prog mname sv sk contk conth !e in
      let block = (List.rev args, instrs, tail) in
      let m = Lir.M.fold Lir.M.add m' m in
      (id, prog, Lir.M.add k block m)) (id, prog, m) bs in
    (id, prog, m, instrs, tail)

  | LetFun ((f, args, k', h', body), e) ->
    let id, t1 = Z.succ id, Z.to_string id in
    let name = mangle_globl_name mname t1 in
    let (id, prog) = lower_function id prog mname sv name args (Some k') (Some h') body in
    lower_value id prog mname (M.add f (Globl name) sv) sk contk conth !e

  | LetRec (bs, e) ->
    let (id, sv) = List.fold_left (fun (id, sv) (f, _, _, _, _) ->
      let f' = id |> Z.to_string |> mangle_globl_name mname in
      (Z.succ id, M.add f (Globl f') sv)) (id, sv) bs in

    let (id, prog) = List.fold_left (fun (id, prog) (f, args, k', h', body) ->
      let name = match M.find f sv with
        | Globl n -> n
        | _ -> failwith "INVALID STATE" in
      lower_function id prog mname sv name args (Some k') (Some h') body) (id, prog) bs in
    lower_value id prog mname sv sk contk conth !e

  | Case (v, cases) ->
    let id, t1 = Z.succ id, Z.to_string id in
    let id, t2 = Z.succ id, Z.to_string id in
    let scrutinee = M.find v sv in
    let instrs =
      [ IOffs (t1, scrutinee, Int64.zero)
      ; ILoad (t2, Local t1)
      ] in

    (* synthesize the intermediate blocks for unpacking fields *)
    let tmp = id in
    let (id, m, tbl) = Hir.M.fold (fun k v (id, m, tbl) ->
      match k with
        | None -> (id, m, tbl)  (* ignore default case for now *)
        | Some k ->
          let j = Printf.sprintf "case%a.%u" Z.sprint tmp k in
          let (id, block) =
            if Some v = contk then begin
              let id, t1 = Z.succ id, Z.to_string id in
              let id, t2 = Z.succ id, Z.to_string id in
              (id, ([], [ IOffs (t1, scrutinee, Int64.one)
                        ; ILoad (t2, Local t1)
                        ], KRetv (Local t2)))
            end else if Some v = conth then begin
              let id, t1 = Z.succ id, Z.to_string id in
              let id, t2 = Z.succ id, Z.to_string id in
              (id, ([], [ IOffs (t1, scrutinee, Int64.one)
                        ; ILoad (t2, Local t1)
                        ], KThrow (Local t2)))
            end else begin
              let rec loop id offs instrs args arity =
                if arity = 0 then
                  (id, ([], instrs, KJump (string_of_int v, List.rev args)))
                else
                  let id, t1 = Z.succ id, Z.to_string id in
                  let id, t2 = Z.succ id, Z.to_string id in
                  let instrs = IOffs (t1, scrutinee, offs)
                    :: ILoad (t2, Local t1)
                    :: instrs in
                  let args = Local t2 :: args in
                  loop id (Int64.succ offs) instrs args (arity - 1) in
              loop id Int64.one [] [] (M.find v sk)
            end in
          (id, Lir.M.add j block m, (Int64.of_int k, j) :: tbl)
      ) cases (id, Lir.M.empty, []) in

    let default_case = match Hir.M.find_opt None cases with
      | None -> "dead"
      | Some k -> string_of_int k in
    (id, prog, m, instrs, KCase (Local t2, default_case, tbl))

  | _ -> failwith "Unsupported lowering"

and lower_function id prog mname sv f args k h e =
  let (id, sv, args) = List.fold_left (fun (id, sv, acc) arg ->
    let id, n = Z.succ id, Z.to_string id in
    (id, M.add arg (Local n) sv, n :: acc)) (id, sv, []) args in
  let (id, prog, m, instrs, tail) = lower_value id prog mname sv M.empty k h !e in
  let m = Lir.M.add "entry" ([], instrs, tail) m in
  let n = Z.to_string id in
  let m = Lir.M.add "exit" ([n], [], KRetv (Local n)) m in
  let m = Lir.M.add "dead" ([], [], KDead) m in
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
