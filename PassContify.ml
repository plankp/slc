open Ast

module M = Map.Make (Int)
module S = Set.Make (Int)

type usage =
  | Unused
  | Divergent
  | Shared of int * term ref * term ref list

let merge_usage r u1 u2 =
  match u1, u2 with
    | Shared (k1, _, p), Shared (k2, _, q) when k1 = k2 ->
      Shared (k1, r, List.rev_append p q)
    | Unused, p | p, Unused -> p
    | _ -> Divergent

let rec check_same_return s r = match !r with
  | _ when S.is_empty s ->
    Unused

  | Module _ ->
    failwith "INVALID NESTED MODULE"

  | Export xs ->
    if List.exists (fun (_, v) -> S.mem v s) xs then Divergent
    else Unused

  | Jmp (_, args) ->
    if List.exists (fun v -> S.mem v s) args then Divergent
    else Unused

  | App (f, args, k) ->
    if List.exists (fun v -> S.mem v s) args then Divergent
    else if S.mem f s then Shared (k, r, [r])
    else Unused

  | LetPack (v, elts, r) ->
    if List.exists (fun v -> S.mem v s) elts then Divergent
    else check_same_return (S.remove v s) r

  | LetProj (v, _, t, r) ->
    if S.mem t s then Divergent
    else check_same_return (S.remove v s) r

  | LetCont (bs, next) ->
    let q = check_same_return s next in
    List.fold_left (fun q (_, args, body) ->
      let s' = List.fold_left (fun s v -> S.remove v s) s args in
      let q' = check_same_return s' body in
      merge_usage r q' q) q bs

  | LetFun (f, args, _, body, next) ->
    let q1 = check_same_return (S.remove f s) next in
    let s' = List.fold_left (fun s v -> S.remove v s) s args in
    let q2 = check_same_return s' body in
    merge_usage r q2 q1

  | LetRec (bs, next) ->
    let s = List.fold_left (fun s (f, _, _, _) -> S.remove f s) s bs in
    let q = check_same_return s next in
    List.fold_left (fun q (_, args, _, body) ->
      let s' = List.fold_left (fun s v -> S.remove v s) s args in
      let q' = check_same_return s' body in
      merge_usage r q' q) q bs

let rec rewrite_jmp = function
  | { contents = App (f, args, _) } as r :: xs ->
    r := Jmp (f, args);
    rewrite_jmp xs
  | [] -> ()
  | _ -> failwith "INVALID APP NODE"

(* after getting bit by updating the wrong ref cells multiple times,
 * we decide to keep it simple and traverse the tree multiple times *)
let rec contify r = match !r with
  | Module _ ->
    failwith "INVALID NESTED MODULE"

  | Export xs ->
    List.fold_left (fun s (_, v) -> S.add v s) S.empty xs

  | Jmp (_, args) ->
    List.fold_left (fun s v -> S.add v s) S.empty args

  | App (f, args, _) ->
    List.fold_left (fun s v -> S.add v s) (S.singleton f) args

  | LetPack (v, elts, r) ->
    let s = contify r |> S.remove v in
    List.fold_left (fun s v -> S.add v s) s elts

  | LetProj (v, _, t, r) ->
    contify r |> S.remove v |> S.add t

  | LetCont (bs, r) ->
    let s = contify r in
    List.fold_left (fun s (_, args, body) ->
      let q = contify body in
      let q = List.fold_left (fun q a -> S.remove a q) q args in
      S.union q s) s bs

  | LetFun (f, args, j, body, next) -> begin
    let s = contify next in
    if not (S.mem f s) then (r := !next; s)
    else begin
      let tail () =
        let q = contify body in
        let q = List.fold_left (fun q a -> S.remove a q) q args in
        s |> S.remove f |> S.union q in

      match check_same_return (S.singleton f) next with
        | Unused -> failwith "INCONSISTENT FV INFO"
        | Divergent -> tail ()
        | Shared (k, new_anchor, rewrites) ->
          rewrite_jmp rewrites;
          new_anchor :=
            LetCont ([j, [k], ref (Jmp (k, [k]))], ref (
              LetCont ([f, args, body], ref (
                !new_anchor))));
          r := !next;
          tail ()
    end
  end

  | LetRec (bs, next) -> begin
    let defset = List.fold_left (fun s (f, _, _, _) ->
      S.add f s) S.empty bs in

    let s = contify next in
    let hitset = S.inter defset s in
    if S.is_empty hitset then (r := !next; s)
    else begin
      let fv_bs = List.map (fun (_, args, _, body) ->
        let s = contify body in
        List.fold_left (fun s a -> S.remove a s) s args) bs in

      let tail () =
        let s = List.fold_left S.union s fv_bs in
        S.diff s defset in

      let default_impl () =
        (* reaching here means that we couldn't turn the entire LetRec into a
         * LetCont. we look for the case where we float-in first:
         *
         * letrec f1 p1 k1 = f2 p2 k2
         * and    f2 p2 k2 = f1 p1 k1
         * in ... only f1 is used here
         *
         * floating f2 into f1 makes it contifiable (notice f1 is still an
         * ordinary function):
         *
         * letrec f1 p1 k1 =
         *   letcont f2 p2 = f1 p1 k1
         *   in jmp f2 p2
         * in ... the rest same as before
         *)

        let offender = S.choose hitset in
        if not (S.singleton offender |> S.equal hitset) then tail ()
        else begin
          let defset = S.remove offender defset in
          let rec loop kinfo acc = function
            | [] ->
              let (k, new_anchor) = Option.get kinfo in
              List.iter rewrite_jmp acc;

              new_anchor := LetCont (List.filter_map (fun (f, args, _, body) ->
                if f = offender then None
                else Some (f, args, body)) bs, ref (!new_anchor));

              List.iter (fun (f, _, j, _) ->
                if f <> offender then
                  new_anchor :=
                    LetCont ([j, [k], ref (Jmp (k, [k]))], ref (!new_anchor))) bs;

              r := LetRec ([List.find (fun (f, _, _, _) -> f = offender) bs], next);
              tail ()
            | (f, _, _, body) :: xs when f = offender -> begin
              (* the offender can use all other functions provided that they
               * return to the same place *)
              match check_same_return defset body with
                | Shared (k, new_anchor, rewrites) ->
                  loop (Some (k, new_anchor)) (rewrites :: acc) xs
                | _ -> tail ()
            end
            | (_, _, k, body) :: xs -> begin
              (* any other function can only use each other for tail calls *)
              match check_same_return defset body with
                | Unused -> loop kinfo acc xs
                | Shared (j, _, q) when j = k -> loop kinfo (q :: acc) xs
                | _ -> tail ()
            end in
          loop None [] bs
        end in

      match check_same_return defset next with
        | Unused -> failwith "INCONSISTENT FV INFO"
        | Divergent -> default_impl ()
        | Shared (k, new_anchor, rewrites) ->
          (* the entire LetRec can be turned into a LetCont IF all binding
           * initializers only use each other for tail calls *)
          let rec loop acc = function
            | [] ->
              List.iter rewrite_jmp acc;
              new_anchor :=
                LetCont (List.map (fun (f, args, _, body) -> (f, args, body)) bs,
                  ref (!new_anchor));
              List.iter (fun (_, _, j, _) ->
                new_anchor :=
                  LetCont ([j, [k], ref (Jmp (k, [k]))],
                    ref (!new_anchor))) bs;
              r := !next;
              tail ()
            | (_, _, k, body) :: xs ->
              match check_same_return defset body with
                | Unused -> loop acc xs
                | Shared (j, _, q) when j = k -> loop (q :: acc) xs
                | _ -> default_impl () in
          loop [rewrites] bs
    end
  end

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
