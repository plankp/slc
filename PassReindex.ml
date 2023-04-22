open Ast

module M = Map.Make (Int)

let rec reindex' r sv sk id = match !r with
  | Module _ ->
    failwith "INVALID NESTED MODULE"

  | Export xs ->
    r := Export (List.map (fun (n, i) -> (n, M.find i sv)) xs);
    id

  | LetCont (bs, e) ->
    (* we need to augment sk with all recursive binders first *)
    let bs, id, sk = List.fold_left (fun (xs, id, sk) (k, args, body) ->
      ((id, args, body) :: xs, id + 1, M.add k id sk)) ([], id, sk) bs in

    (* then reindex binder body *)
    let bs, id = List.fold_left (fun (xs, id) (k, args, body) ->
      let args, id, sv = List.fold_left (fun (xs, id, sv) a ->
        (id :: xs, id + 1, M.add a id sv)) ([], id, sv) args in
      ((k, List.rev args, body) :: xs, reindex' body sv sk id)) ([], id) bs in

    r := LetCont (bs, e);
    reindex' e sv sk id

  | LetFun (f, args, k, body, e) ->
    (* LetFun is NOT recursive, so don't augment sv here *)
    let f', id = id, id + 1 in
    (* the args only affect the binder body *)
    let args, id, sv' = List.fold_left (fun (xs, id, sv') a ->
      (id :: xs, id + 1, M.add a id sv')) ([], id, sv) args in
    let k, id, sk' = id, id + 1, M.add k id sk in

    r := LetFun (f', List.rev args, k, body, e);
    id |> reindex' body sv' sk' |> reindex' e (M.add f f' sv) sk

  | LetRec (bs, e) ->
    (* we need to augment sv with all recursive binders first *)
    let bs, id, sv = List.fold_left (fun (xs, id, sv) (f, args, k, body) ->
      ((id, args, k, body) :: xs, id + 1, M.add f id sv)) ([], id, sv) bs in

    (* then reindex binder body *)
    let bs, id = List.fold_left (fun (xs, id) (f, args, k, body) ->
      let args, id, sv = List.fold_left (fun (xs, id, sv) a ->
        (id :: xs, id + 1, M.add a id sv)) ([], id, sv) args in
      let k, id, sk = id, id + 1, M.add k id sk in
      ((f, List.rev args, k, body) :: xs, reindex' body sv sk id)) ([], id) bs in

    r := LetRec (bs, e);
    reindex' e sv sk id

  | Jmp (k, xs) ->
    r := Jmp (M.find k sk, List.map (fun i -> M.find i sv) xs);
    id

  | App (f, xs, k) ->
    r := App (M.find f sv, List.map (fun i -> M.find i sv) xs, M.find k sk);
    id

  | LetPack (v, elts, e) ->
    let elts = List.map (fun i -> M.find i sv) elts in
    let v, id, sv = id, id + 1, M.add v id sv in

    r := LetPack (v, elts, e);
    reindex' e sv sk id

  | LetProj (v, i, p, e) ->
    let p = M.find p sv in
    let v, id, sv = id, id + 1, M.add v id sv in

    r := LetProj (v, i, p, e);
    reindex' e sv sk id

let reindex = function
  | Module r -> reindex' r M.empty M.empty 0
  | _ -> failwith "INVALID TERM ANCHOR"
