open Hir

module M = Map.Make (Int)
module S = Set.Make (Int)

type usage =
  | Unused
  | Divergent
  | Shared of int * int * term ref * term ref list

let merge_usage r u1 u2 =
  match u1, u2 with
    | Shared (k1, h1, _, p), Shared (k2, h2, _, q) when k1 = k2 && h1 = h2 ->
      Shared (k1, h1, r, List.rev_append p q)
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

  | App (f, args, k, h) ->
    if List.exists (fun v -> S.mem v s) args then Divergent
    else if S.mem f s then Shared (k, h, r, [r])
    else Unused

  | LetPack (v, elts, r) | LetCons (v, _, elts, r) ->
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

  | LetFun ((f, args, _, _, body), next) ->
    let q1 = check_same_return (S.remove f s) next in
    let s' = List.fold_left (fun s v -> S.remove v s) s args in
    let q2 = check_same_return s' body in
    merge_usage r q2 q1

  | LetRec (bs, next) ->
    let s = List.fold_left (fun s (f, _, _, _, _) -> S.remove f s) s bs in
    let q = check_same_return s next in
    List.fold_left (fun q (_, args, _, _, body) ->
      let s' = List.fold_left (fun s v -> S.remove v s) s args in
      let q' = check_same_return s' body in
      merge_usage r q' q) q bs

  | Case (v, _) ->
    if S.mem v s then Divergent else Unused

let rec rewrite_jmp = function
  | { contents = App (f, args, _, _) } as r :: xs ->
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

  | App (f, args, _, _) ->
    List.fold_left (fun s v -> S.add v s) (S.singleton f) args

  | Case (v, _) ->
    S.singleton v

  | LetPack (v, elts, r) | LetCons (v, _, elts, r) ->
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

  | LetFun ((f, args, pk, ph, body), next) -> begin
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
        | Shared (k, h, new_anchor, rewrites) ->
          rewrite_jmp rewrites;
          new_anchor :=
            LetCont ([pk, [k], ref (Jmp (k, [k]))], ref (
              LetCont ([ph, [h], ref (Jmp (h, [h]))], ref (
                LetCont ([f, args, body], ref (
                  !new_anchor))))));
          r := !next;
          tail ()
    end
  end

  | LetRec (bs, next) -> begin
    let defset = List.fold_left (fun s (f, _, _, _, _) ->
      S.add f s) S.empty bs in

    let s = contify next in
    let hitset = S.inter defset s in
    if S.is_empty hitset then (r := !next; s)
    else begin
      let fv_bs = List.map (fun (_, args, _, _, body) ->
        let s = contify body in
        List.fold_left (fun s a -> S.remove a s) s args) bs in

      let tail () =
        let s = List.fold_left S.union s fv_bs in
        S.diff s defset in

      let default_impl () =
        (* reaching here means that we couldn't turn the entire LetRec into a
         * LetCont. we look for the case where we float-in first:
         *
         * letrec f1 p1 k1 h1 = f2 p1 k1 h1
         * and    f2 p2 k2 h1 = f1 p2 k2 h2
         * in ... only f1 is used here
         *
         * floating f2 into f1 makes it contifiable (notice f1 is still an
         * ordinary function):
         *
         * letrec f1 p1 k1 h1 =
         *   letcont f2 p2 = f1 p2 k1 h1
         *   in jmp f2 p1
         * in ... the rest same as before
         *)

        let offender = S.choose hitset in
        if not (S.singleton offender |> S.equal hitset) then tail ()
        else begin
          let defset = S.remove offender defset in
          let rec loop kinfo acc = function
            | [] ->
              let (k, h, new_anchor) = Option.get kinfo in
              List.iter rewrite_jmp acc;

              new_anchor := LetCont (List.filter_map (fun (f, args, _, _, body) ->
                if f = offender then None
                else Some (f, args, body)) bs, ref (!new_anchor));

              List.iter (fun (f, _, pk, ph, _) ->
                if f <> offender then
                  new_anchor :=
                    LetCont ([pk, [k], ref (Jmp (k, [k]))], ref (
                      LetCont ([ph, [h], ref (Jmp (h, [h]))], ref (
                        !new_anchor))))) bs;

              r := LetRec ([List.find (fun (f, _, _, _, _) -> f = offender) bs], next);
              tail ()
            | (f, _, _, _, body) :: xs when f = offender -> begin
              (* the offender can use all other functions provided that they
               * return to the same place *)
              match check_same_return defset body with
                | Shared (k, h, new_anchor, rewrites) ->
                  loop (Some (k, h, new_anchor)) (rewrites :: acc) xs
                | _ -> tail ()
            end
            | (_, _, pk, ph, body) :: xs -> begin
              (* any other function can only use each other for tail calls *)
              match check_same_return defset body with
                | Unused -> loop kinfo acc xs
                | Shared (k, h, _, q) when pk = k && ph = h ->
                  loop kinfo (q :: acc) xs
                | _ -> tail ()
            end in
          loop None [] bs
        end in

      match check_same_return defset next with
        | Unused -> failwith "INCONSISTENT FV INFO"
        | Divergent -> default_impl ()
        | Shared (k, h, new_anchor, rewrites) ->
          (* the entire LetRec can be turned into a LetCont IF all binding
           * initializers only use each other for tail calls *)
          let rec loop acc = function
            | [] ->
              List.iter rewrite_jmp acc;
              new_anchor :=
                LetCont (List.map (fun (f, args, _, _, body) -> (f, args, body)) bs,
                  ref (!new_anchor));
              List.iter (fun (_, _, pk, ph, _) ->
                new_anchor :=
                  LetCont ([pk, [k], ref (Jmp (k, [k]))], ref (
                    LetCont ([ph, [h], ref (Jmp (h, [h]))], ref (
                      !new_anchor))))) bs;
              r := !next;
              tail ()
            | (_, _, pk, ph, body) :: xs ->
              match check_same_return defset body with
                | Unused -> loop acc xs
                | Shared (k, h, _, q) when pk = k && ph = h ->
                  loop (q :: acc) xs
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

  | App (f, args, k, h) -> begin
    let k, h, flag = match M.find_opt k s, M.find_opt h s with
      | Some k, Some h -> k, h, true
      | Some k, None   -> k, h, true
      | None, Some h   -> k, h, true
      | _ -> k, h, flag in
    r := App (f, args, k, h);
    flag
  end

  | Case (v, cases) -> begin
    let modified = ref flag in
    r := Case (v, Hir.M.map (fun k ->
      match M.find_opt k s with
        | None -> k
        | Some k -> modified := true; k) cases);
    !modified
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

  | LetFun ((_, _, k, h, body), r) ->
    flag |> fold_cont s r |> fold_cont (s |> M.remove k |> M.remove h) body

  | LetRec (bs, r) ->
    let flag = fold_cont s r flag in
    List.fold_left (fun flag (_, _, k, h, body) ->
      fold_cont (s |> M.remove k |> M.remove h) body flag) flag bs

  | LetPack (_, _, r)
  | LetCons (_, _, _, r)
  | LetProj (_, _, _, r) ->
    fold_cont s r flag

let rec transform e =
  let _ = PassReindex.reindex e in
  match e with
    | Module (_, _, r) ->
      let _ = contify r in
      if fold_cont M.empty r false then transform e
    | _ -> failwith "INVALID TERM ANCHOR"
