open Ast

let rec find_insert_point candidate r =
  let union_here t1 t2 =
    match t1, t2 with
      | Some (p, Some (k1, _)), Some (q, Some (k2, _)) when k1 = k2 ->
        Some (List.rev_append p q, Some (k1, r))
      | Some (_, None), v | v, Some (_, None) -> v
      | _ -> None in

  match !r with
    | LetCont (_, _, body, next)
    | LetFun (_, _, _, body, next) ->
      let l = find_insert_point candidate body in
      let r = find_insert_point candidate next in
      union_here l r

    | LetRec (bs, next) ->
      let rec loop = function
        | None, _ -> None
        | t1, [] -> t1
        | t1, (_, _, _, x) :: xs ->
          let t1 = union_here (find_insert_point candidate x) t1 in
          loop (t1, xs) in
      loop (find_insert_point candidate next, bs)

    | LetPack (_, elts, next) when not (List.mem candidate elts) ->
      find_insert_point candidate next

    | LetProj (_, _, v, next) when v <> candidate ->
      find_insert_point candidate next

    | App (f, args, k) when not (List.mem candidate args) ->
      if f = candidate then Some ([r], Some (k, r))
      else Some ([], None)

    | Jmp (_, args) when not (List.mem candidate args) ->
      Some ([], None)

    | Export xs when List.for_all (fun (_, v) -> v <> candidate) xs ->
      Some ([], None)

    | _ -> None

let rec contify r =
  match !r with
    | LetPack (_, _, r)
    | LetProj (_, _, _, r) ->
      contify r

    | LetCont (_, _, body, r) ->
      contify body;
      contify r

    | LetFun (f, args, j, body, next) -> begin
      contify body;
      contify next;
      match find_insert_point f next with
        | None -> ()
        | Some (_, None) -> r := !next
        | Some (sites, Some (k, new_anchor)) ->
          (* rewrite the App nodes into Jmp nodes *)
          List.iter (function
            | { contents = App (_, args, _) } as r -> r := Jmp (f, args)
            | _ -> failwith "INVALID APP NODE") sites;
          (* relocate the contified f to the new location *)
          r := !next;
          new_anchor := LetCont (f, args, body, ref (!new_anchor));
          (* also need to remap the argument k *)
          new_anchor := LetCont (j, [k], ref (Jmp (k, [k])), ref (!new_anchor))
    end

    | LetRec (bs, r) ->
      List.iter (fun (_, _, _, body) -> contify body) bs;
      contify r

    | _ -> ()

let transform e =
  let _ = PassReindex.reindex e in
  match e with
    | Module r -> contify r
    | _ -> failwith "INVALID TERM ANCHOR"
