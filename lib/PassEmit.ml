open Hir
open Lir
open Printf

module M = Map.Make (Int)

let rec lower_value id prog sv sk contk conth = function
  | LetPack (v, [], e) ->
    lower_value id prog (M.add v (Int64 0L) sv) sk contk conth !e

  | LetPack (v, elts, e) ->
    let id, t1 = Z.succ id, Z.to_string id in
    let (id, prog, m, instrs, tail) = lower_value id prog (M.add v (Local t1) sv) sk contk conth !e in
    let elts = List.map (fun (_, e) -> M.find e sv) elts in
    (id, prog, m, IPack (t1, elts) :: instrs, tail)

  | LetProj (v, i, t, e) ->
    let id, t1 = Z.succ id, Z.to_string id in
    let id, t2 = Z.succ id, Z.to_string id in
    let (id, prog, m, instrs, tail) = lower_value id prog (M.add v (Local t2) sv) sk contk conth !e in
    let instrs = IOffs (t1, M.find t sv, Int64.of_int i)
      :: ILoad (t2, Local (t1))
      :: instrs in
    (id, prog, m, instrs, tail)

  | LetCons (v, i, elts, e) ->
    let id, t1 = Z.succ id, Z.to_string id in
    let (id, prog, m, instrs, tail) = lower_value id prog (M.add v (Local t1) sv) sk contk conth !e in
    let elts = List.map (fun e -> M.find e sv) elts in
    let elts = Int64 (Int64.of_int i) :: elts in
    (id, prog, m, IPack (t1, elts) :: instrs, tail)

  | Export xs ->
    let instrs = List.fold_left (fun buf (n, v) ->
      IStore (M.find v sv, Globl (sprintf "G_%s" n)) :: buf) [] xs in
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

    let (id, prog, m, instrs, tail) = lower_value id prog sv sk contk conth !e in
    let (id, prog, m) = List.fold_left (fun (id, prog, m) (k, args, e) ->
      let k = string_of_int k in
      let (id, sv, args) = List.fold_left (fun (id, sv, acc) arg ->
        let id, n = Z.succ id, Z.to_string id in
        (id, M.add arg (Local n) sv, n :: acc)) (id, sv, []) args in
      let (id, prog, m', instrs, tail) = lower_value id prog sv sk contk conth !e in
      let block = (List.rev args, instrs, tail) in
      let m = Lir.M.fold Lir.M.add m' m in
      (id, prog, Lir.M.add k block m)) (id, prog, m) bs in
    (id, prog, m, instrs, tail)

  | LetFun ((f, args, k', h', body), e) ->
    let id, t1 = Z.succ id, Z.to_string id in
    let (id, prog, m, instrs, tail) = lower_value id prog (M.add f (Globl t1) sv) sk contk conth !e in
    let (id, prog) = lower_function id prog t1 args (Some k') (Some h') body in
    (id, prog, m, instrs, tail)

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

and lower_function id prog f args k h e =
  let (id, sv, args) = List.fold_left (fun (id, sv, acc) arg ->
    let id, n = Z.succ id, Z.to_string id in
    (id, M.add arg (Local n) sv, n :: acc)) (id, M.empty, []) args in
  let (id, prog, m, instrs, tail) = lower_value id prog sv M.empty k h !e in
  let m = Lir.M.add "entry" ([], instrs, tail) m in
  let n = Z.to_string id in
  let m = Lir.M.add "exit" ([n], [], KRetv (Local n)) m in
  let m = Lir.M.add "dead" ([], [], KDead) m in
  (id, Lir.M.add f (Label (List.rev args, "entry", m)) prog)

let lower e =
  let _ = PassReindex.reindex e in
  match e with
    | Module (v, h, m) ->
      let (_, prog) = lower_function Z.zero Lir.M.empty "INIT" [] None (Some !h) m in
      let prog = List.fold_left (fun prog v ->
        Lir.M.add (sprintf "G_%s" v) (Int64 0L) prog) prog v in
      prog
    | _ -> failwith "INVALID TERM ANCHOR"
