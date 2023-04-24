open Ast

module S = Set.Make (Int)

let rec cc r id =
  match !r with
    | Module _ ->
      failwith "INVALID NESTED MODULE"

    | Export xs ->
      (id, List.fold_left (fun s (_, v) -> S.add v s) S.empty xs)

    | LetCont (bs, e) ->
      (* continuations cannot escape, so no need to closure convert.
       * just propagate the FVs *)
      let (id, esc) = cc e id in
      List.fold_left (fun (id, esc) (_, args, body) ->
        let (id, p) = cc body id in
        let p = List.fold_left (fun p a -> S.remove a p) p args in
        (id, S.union p esc)) (id, esc) bs

    | LetFun (f, args, k, h, body, e) ->
      let (id, esc) = cc body id in
      let esc = List.fold_left (fun esc a -> S.remove a esc) esc args in

      (* whatever is escaping needs to captured inside the envptr
       * and unpacked as soon as we enter the function *)
      let id_pack, id = id, id + 1 in
      let id_envp, id = id, id + 1 in

      let _ = S.fold (fun esc slot ->
        body := LetProj (esc, slot, id_envp, ref (!body));
        slot + 1) esc 0 in

      r := LetPack (id_pack, S.elements esc, ref (
            LetFun (f, args @ [id_envp], k, h, body, ref (
              LetPack (f, [f; id_pack], e)))));

      (* LetFun is NOT recursive *)
      let (id, fv2) = cc e id in
      (id, fv2 |> S.remove f |> S.union esc)

    | LetRec (bs, e) ->
      (* Provided that bs = [(f1, p1..., k1); ...], we translate as follows:
       *
       *  let f1_ptr p1... envp k1 =
       *    let f1 = { envp#0, envp } in
       *    let f2 = { envp#1, envp } in
       *    ...
       *    let esc... = envp#... in
       *    ... in
       *  ...
       *  let envp = { f1_ptr, f2_ptr, ..., esc... } in
       *  let f1 = { f1_ptr, envp } in
       *  let f2 = { f2_ptr, envp } in
       *  ...
       *)

      let (id, esc) = List.fold_left (fun (id, total) (_, args, _, _, body) ->
        let (id, esc) = cc body id in
        let esc = List.fold_left (fun esc a -> S.remove a esc) esc args in
        (id, S.union esc total)) (id, S.empty) bs in

      (* we will always capture the recursive bindings at the beginning,
       * so drop them here to avoid capturing them twice. *)
      let esc = List.fold_left (fun esc (f, _, _, _, _) -> S.remove f esc) esc bs in

      let id_pack, id = id, id + 1 in
      let id_envp, id = id, id + 1 in

      let bs = List.map (fun (f, args, k, h, body) ->
        let (new_body, slot) = List.fold_left (fun (body, slot) (f, _, _, _, _) ->
          (ref (LetProj (f, slot, id_envp,
            ref (LetPack (f, [f; id_envp], body)))), slot + 1)) (body, 0) bs in
        let _ = S.fold (fun esc slot ->
          body := LetProj (esc, slot, id_envp, ref (!body));
          slot + 1) esc slot in
        (f, args @ [id_envp], k, h, new_body)) bs in

      let fat_env = esc
        |> S.elements
        |> List.fold_right (fun (f, _, _, _, _) xs -> f :: xs) bs in
      let tail = List.fold_left (fun e (f, _, _, _, _) ->
        ref (LetPack (f, [f; id_pack], e))) e bs in
      r := List.fold_right (fun (f, args, k, h, body) tail ->
        LetFun (f, args, k, h, body, ref tail)) bs (LetPack (id_pack, fat_env, tail));

      let (id, fv2) = cc e id in
      let fv2 = List.fold_left (fun fv2 (f, _, _, _, _) -> S.remove f fv2) fv2 bs in
      (id, S.union esc fv2)

    | Jmp (_, args) ->
      (* ignore continuation k since these cannot escape by definition *)
      (id, List.fold_left (fun s v -> S.add v s) S.empty args)

    | App (f, args, k, h) ->
      (* ignore continuation k as above,
       * but we need to recover the function and env pointer from the tuple *)
      let id_envp, id = id, id + 1 in
      let id_fptr, id = id, id + 1 in
      r := LetProj (id_fptr, 0, f, ref (
            LetProj (id_envp, 1, f, ref (
              App (id_fptr, args @ [id_envp], k, h)))));

      (id, List.fold_left (fun s v -> S.add v s) (S.singleton f) args)

    | _ -> failwith "TODO"

let transform e =
  let id = PassReindex.reindex e in
  match e with
    | Module (_, r) ->
      let (_, s) = cc r id in
      if not (S.is_empty s) then
        failwith "INVALID ESCAPING FV"
    | _ -> failwith "INVALID TERM ANCHOR"
