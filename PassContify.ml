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

  | LetCont (_, args, body, next) ->
    let s1 = contify next in
    let s2 = contify body in
    let s2 = List.fold_left (fun s v -> M.remove v s) s2 args in
    merge r s2 s1

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
            new_anchor := LetCont (f, args, body, ref (!new_anchor));
            (* also remap the argument k and parameter j *)
            new_anchor := LetCont (j, [k], ref (Jmp (k, [k])), ref (!new_anchor)) in

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

let transform e =
  let _ = PassReindex.reindex e in
  match e with
    | Module r -> contify r |> ignore
    | _ -> failwith "INVALID TERM ANCHOR"
