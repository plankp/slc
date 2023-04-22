open Ast

module M = Map.Make (Int)

let merge r s1 s2 =
  M.union (fun _ a b ->
    match a, b with
      | Some (k1, _, t1), Some (k2, _, t2) when k1 = k2 ->
        Some (Some (k1, r, List.rev_append t1 t2))
      | _ -> Some (None)) s1 s2

let rec contify r = match !r with
  | Module _ ->
    failwith "INVALID NESTED MODULE"

  | Export xs ->
    List.fold_left (fun s (_, v) -> M.add v None s) M.empty xs

  | Jmp (_, args) ->
    List.fold_left (fun s v -> M.add v None s) M.empty args

  | App (f, args, k) ->
    let s = List.fold_left (fun s v -> M.add v None s) M.empty args in
    M.update f (function
      | None -> Some (Some (k, r, [r]))
      | _ -> Some (None)) s

  | LetPack (v, elts, r) ->
    let s = contify r in
    let s = M.remove v s in
    List.fold_left (fun s v -> M.add v None s) s elts

  | LetProj (v, _, t, r) ->
    contify r |> M.remove v |> M.add t None

  | LetCont (bs, next) ->
    let s = contify next in
    List.fold_left (fun s (_, args, body) ->
      let s' = contify body in
      let s' = List.fold_left (fun s' v -> M.remove v s') s' args in
      merge r s' s) s bs

  | LetFun (f, args, j, body, next) -> begin
    let s1 = contify next in
    match M.find_opt f s1 with
      | None ->
        (* binding is dead *)
        r := !next;
        s1
      | Some v ->
        let () = match v with
          | None -> ()
          | Some (k, new_anchor, sites) ->
            (* rewrite the App nodes into Jmp nodes *)
            List.iter (function
              | { contents = App (_, args, _) } as r -> r := Jmp (f, args)
              | _ -> failwith "INVALID APP NODE") sites;
            (* relocate the contified f to the new location *)
            r := !next;
            new_anchor := LetCont ([f, args, body], ref (!new_anchor));
            (* also remap the argument k and parameter j *)
            new_anchor := LetCont ([j, [k], ref (Jmp (k, [k]))], ref (!new_anchor)) in

        let s1 = M.remove f s1 in
        let s2 = contify body in
        let s2 = List.fold_left (fun s v -> M.remove v s) s2 args in

        merge r s1 s2
  end

  | LetRec (bs, e) ->
    (* TODO: Handle recursive contification *)
    let s = contify e in
    let s = List.fold_left (fun s (_, args, _, body) ->
      let s' = contify body in
      let s' = List.fold_left (fun s v -> M.remove v s) s' args in
      merge r s' s) s bs in

    List.fold_left (fun s (f, _, _, _) -> M.remove f s) s bs

(* this unfolds the letcont j v = k v that are synthesized during the
 * contification step. note that doing this as a separate step is done to
 * ensure the correctness of the other transformation *)
let rec fold_cont s r flag = match !r with
  | Module _ ->
    failwith "INVALID NESTED MODULE"

  | Export _ -> flag

  | Jmp (j, args) -> begin
    match M.find_opt j s with
      | None -> flag
      | Some j ->
        r := Jmp (j, args);
        true
  end

  | App (f, args, j) -> begin
    match M.find_opt j s with
      | None -> flag
      | Some j ->
        r := App (f, args, j);
        true
  end

  | LetCont (bs, next) -> begin
    let s = List.fold_left (fun s (j, _, _) ->
      M.remove j s) s bs in
    let flag = List.fold_left (fun flag (_, _, body) ->
      fold_cont s body flag) flag bs in

    let s, next = match bs with
      | [j1, [p1], { contents = Jmp (j2, [a1]) }] when j1 <> j2 && p1 = a1 ->
        r := !next;
        M.add j1 j2 s, r
      | _ -> s, next in

    fold_cont s next flag
  end

  | LetFun (_, _, j, body, r) ->
    flag |> fold_cont s r |> fold_cont (M.remove j s) body

  | LetRec (bs, r) ->
    let flag = fold_cont s r flag in
    List.fold_left (fun flag (_, _, j, body) ->
      fold_cont (M.remove j s) body flag) flag bs

  | LetPack (_, _, r)
  | LetProj (_, _, _, r) ->
    fold_cont s r flag

let rec transform e =
  let _ = PassReindex.reindex e in
  match e with
    | Module r ->
      let _ = contify r in
      if fold_cont M.empty r false then transform e
    | _ -> failwith "INVALID TERM ANCHOR"
