open Hir

module S = Set.Make (Int)
module M = Map.Make (Int)

let merge _ p q = Some (List.rev_append p q)

let rec try_raising info sites =
  (* do the simple (stupid) thing, which is to gradually lift the arguments
   * one by one *)
  let (f, args, k, _, body) = info in

  (* check if we have the following pattern:
   * letfun f args k h = (letfun f' ... = ... in Jmp k f') *)
  match !body with
    | LetFun ((f', args', k', h', body'), { contents = Jmp (j, [v]) })
      when j = k && v = f' ->
      (* at this point, the definition-site looks good. then make sure the
       * use-site is able to lift at least once. *)
      let rec loop acc sites = function
        | (_, []) :: _ -> info
        | (r, hd :: tl) :: xs ->
          loop ((r, hd) :: acc) ((r, tl) :: sites) xs
        | [] ->
          let info = (f, args @ args', k', h', body') in
          List.iter (fun (r, (k, args')) ->
            match !r with
              | App (f, args, _, h) -> r := App (f, args @ args', k, h)
              | _ -> failwith "INVALID CAPTURED APP NODE") acc;
          try_raising info sites in
      loop [] [] sites
    | _ -> info

let rec rewrite s r = match !r with
  | Module _ ->
    failwith "INVALID NESTED MODULE"

  | LetCont ([j, [partial], { contents = App (f, args, k, h) }], next)
    when f = partial && not (k = j || h = j || List.mem f args) ->
    (* We matched the following pattern:
     * letcont j f = App f args k h in ... *)

    (* compute the longest possible tail (we might raise 2+ arguments) *)
    let tail = match M.find_opt k s with
      | Some (h', tail) when h = h' -> (k, args) :: tail
      | _ -> [k, args] in

    let (q, fv) = rewrite (M.add j (h, tail) s) next in
    (q, List.fold_left (fun s v -> S.add v s) fv args)

  | App (f, args, k, h) -> begin
    (* check if there is a tail that is registered and usable.
     * if there isn't, then we cannot raise the arity. *)
    let fv = List.fold_left (fun s v -> S.add v s) S.empty args in
    if S.mem f fv then (M.empty, fv)
    else
      match M.find_opt k s with
        | Some (h', tail) when h = h' -> (M.singleton f [r, tail], fv)
        | _ -> (M.empty, S.add f fv)
  end

  | LetFun ((f, args, _, _, body) as info, next) ->
    let (q, fv) = rewrite s next in
    let () = match M.find_opt f q with
      | Some (_ :: _ as sites) when not (S.mem f fv) ->
        r := LetFun (try_raising info sites, next)
      | _ -> () in

    let q = M.remove f q in
    let fv = S.remove f fv in
    let (q', fv') = rewrite s body in
    let fv' = List.fold_left (fun s v -> S.add v s) fv' args in
    (M.union merge q' q, S.union fv' fv)

  | LetRec (bs, next) ->
    let (q, fv) = rewrite s next in
    let (q, fv) = List.fold_left (fun (q, fv) (_, args, _, _, next) ->
      let (q', fv') = rewrite s next in
      let fv' = List.fold_left (fun s v -> S.add v s) fv' args in
      (M.union merge q' q, S.union fv' fv)) (q, fv) bs in

    let (bs, q, fv) = List.fold_left (fun (acc, q, fv) info ->
      let (f, _, _, _, _) = info in
      let t = match M.find_opt f q with
        | Some (_ :: _ as sites) when not (S.mem f fv) ->
          try_raising info sites
        | _ -> info in
      (t :: acc, M.remove f q, S.remove f fv)) ([], q, fv) bs in
    r := LetRec (List.rev bs, next);
    (q, fv)

  | Export xs ->
    (M.empty, List.fold_left (fun s (_, v) -> S.add v s) S.empty xs)

  | Case (v, _) ->
    (M.empty, S.singleton v)

  | Jmp (_, xs) ->
    (M.empty, List.fold_left (fun s v -> S.add v s) S.empty xs)

  | LetPack (v, xs, next) ->
    let (q, fv) = rewrite s next in
    let fv = S.remove v fv in
    (q, List.fold_left (fun s (_, v) -> S.add v s) fv xs)

  | LetCons (v, _, xs, next) ->
    let (q, fv) = rewrite s next in
    let fv = S.remove v fv in
    (q, List.fold_left (fun s v -> S.add v s) fv xs)

  | LetProj (v, _, t, next) ->
    let (q, fv) = rewrite s next in
    (q, fv |> S.remove v |> S.add t)

  | LetExtn (v, _, _, next) ->
    let (q, fv) = rewrite s next in
    (q, S.remove v fv)

  | LetCont (bs, next) ->
    let (q, fv) = rewrite s next in
    List.fold_left (fun (q, fv) (_, args, next) ->
      let (q', fv') = rewrite s next in
      let fv' = List.fold_left (fun s v -> S.add v s) fv' args in
      (M.union merge q' q, S.union fv' fv)) (q, fv) bs

  | Mutate (v1, _, v2, _) ->
    (M.empty, S.of_list [v1; v2])

let transform e =
  let _ = PassReindex.reindex e in
  match e with
    | Module (_, _, r) -> rewrite M.empty r |> ignore
    | _ -> failwith "INVALID TERM ANCHOR"
