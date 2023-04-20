open Ast

module M = Map.Make (Int)

let rec reindex' r s id =
  match !r with
    | Module _ ->
      failwith "INVALID NESTED MODULE"

    | Export xs ->
      r := Export (List.map (fun (n, i) -> (n, M.find i s)) xs);
      id

    | LetCont (j, args, body, e) ->
      let j, id, s = id, id + 1, M.add j id s in
      let args, id, s' = List.fold_left (fun (xs, id, s') a ->
        (id :: xs, id + 1, M.add a id s')) ([], id, s) args in

      r := LetCont (j, List.rev args, body, e);
      id |> reindex' body s' |> reindex' e s

    | LetFun (f, args, k, body, e) ->
      (* LetFun is NOT recursive, so don't augment s here *)
      let f', id = id, id + 1 in
      (* the args only affect the binder body *)
      let args, id, s' = List.fold_left (fun (xs, id, s') a ->
        (id :: xs, id + 1, M.add a id s')) ([], id, s) args in
      let k, id, s' = id, id + 1, M.add k id s' in

      r := LetFun (f', List.rev args, k, body, e);
      id |> reindex' body s' |> reindex' e (M.add f f' s)

    | LetRec (bs, e) ->
      (* we need to augment s with all recursive binders first *)
      let bs, id, s = List.fold_left (fun (xs, id, s) (f, args, k, body) ->
        ((id, args, k, body) :: xs, id + 1, M.add f id s)) ([], id, s) bs in

      (* then reindex binder body *)
      let bs, id = List.fold_left (fun (xs, id) (f, args, k, body) ->
        let args, id, s = List.fold_left (fun (xs, id, s) a ->
          (id :: xs, id + 1, M.add a id s)) ([], id, s) args in
        let k, id, s = id, id + 1, M.add k id s in
        ((f, List.rev args, k, body) :: xs, reindex' body s id)) ([], id) bs in

      r := LetRec (bs, e);
      reindex' e s id

    | Jmp (k, xs) ->
      r := Jmp (M.find k s, List.map (fun i -> M.find i s) xs);
      id

    | App (f, xs, k) ->
      r := App (M.find f s, List.map (fun i -> M.find i s) xs, M.find k s);
      id

    | LetPack (v, elts, e) ->
      let elts = List.map (fun i -> M.find i s) elts in
      let v, id, s = id, id + 1, M.add v id s in

      r := LetPack (v, elts, e);
      reindex' e s id

    | LetProj (v, i, p, e) ->
      let p = M.find p s in
      let v, id, s = id, id + 1, M.add v id s in

      r := LetProj (v, i, p, e);
      reindex' e s id

let reindex = function
  | Module r -> reindex' r M.empty 0
  | _ -> failwith "INVALID TERM ANCHOR"
