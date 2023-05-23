open Hir

module M = Map.Make (Int)

type inline_hint =
  | SingleUse   (* only applicable for Jmp (X, _) and App (X, _, _, _) *)
  | Contextual
  | DontInline

let bump_use hint s v =
  M.update v (function
    | None -> Some hint
    | Some i ->
      match i, hint with
        | SingleUse, SingleUse -> Some Contextual
        | _ -> Some DontInline) s

(* we collect occurrences while dropping dead binders *)
let rec collect_occ s r = match !r with
  | Module _ ->
    failwith "INVALID NESTED MODULE"

  | Export xs ->
    List.fold_left (fun s (_, v) -> bump_use DontInline s v) s xs

  | Jmp (j, args) ->
    let s = bump_use SingleUse s j in
    List.fold_left (bump_use DontInline) s args

  | App (f, args, k, h) ->
    let s = bump_use DontInline s k in
    let s = bump_use DontInline s h in
    let s = bump_use SingleUse s f in
    List.fold_left (bump_use DontInline) s args

  | Case (v, cases) ->
    let s = bump_use DontInline s v in
    Hir.M.fold (fun _ k s -> bump_use DontInline s k) cases s

  | Mutate (v1, _, v2, k) ->
    let s = bump_use DontInline s v1 in
    let s = bump_use DontInline s v2 in
    bump_use DontInline s k

  | LetPack (v, elts, next) ->
    let s = collect_occ s next in
    if M.mem v s then
      List.fold_left (fun s (_, v) -> bump_use DontInline s v) s elts
    else begin
      r := !next; s
    end

  | LetCons (v, _, elts, next) ->
    let s = collect_occ s next in
    if M.mem v s then
      List.fold_left (bump_use DontInline) s elts
    else begin
      r := !next; s
    end

  | LetProj (v, _, t, next) ->
    let s = collect_occ s next in
    if M.mem v s then
      bump_use DontInline s t
    else begin
      r := !next; s
    end

  | LetExtn (v, _, _, next) ->
    let s = collect_occ s next in
    if not (M.mem v s) then
      r := !next;
    s

  | LetFun ((f, _, _, _, body), next) ->
    let s = collect_occ s next in
    if M.mem f s then
      collect_occ s body
    else begin
      r := !next; s
    end

  | LetRec (bs, next) ->
    let s = collect_occ s next in
    if List.exists (fun (f, _, _, _, _) -> M.mem f s) bs then
      List.fold_left (fun s (_, _, _, _, body) -> collect_occ s body) s bs
    else begin
      r := !next; s
    end

  | LetCont (bs, next) ->
    let s = collect_occ s next in
    if List.exists (fun (j, _, _) -> M.mem j s) bs then
      List.fold_left (fun s (_, _, body) -> collect_occ s body) s bs
    else begin
      r := !next; s
    end

let subst m v =
  match M.find_opt v m with
    | Some v -> v
    | _ -> v

let rec inline_single_use occs sbody svar r = match !r with
  | Module _ ->
    failwith "INVALID NESTED MODULE"

  (* in both App (Lam, ...) and Jmp (Cont, ...), we delay processing the body
   * until it is inlined *)

  | App (f, args, k, h) ->
    let f = subst svar f in
    let args = List.map (subst svar) args in
    let k = subst svar k in
    let h = subst svar h in
    r := App (f, args, k, h);

    if M.find f occs = SingleUse then begin
      match M.find_opt f sbody with
        | Some (kh_params, body) ->
          let svar = List.fold_left2 (fun svar p a ->
            M.add p a svar) svar kh_params (k :: h :: args) in
          r := !body;
          inline_single_use occs sbody svar r
        | _ -> ()
    end

  | Jmp (k, args) ->
    let k = subst svar k in
    let args = List.map (subst svar) args in
    r := Jmp (k, args);

    if M.find k occs = SingleUse then begin
      match M.find_opt k sbody with
        | Some (params, body) ->
          let svar = List.fold_left2 (fun svar p a ->
            M.add p a svar) svar params args in
          r := !body;
          inline_single_use occs sbody svar r
        | _ -> ()
    end

  | Export xs ->
    r := Export (List.map (fun (n, v) -> (n, subst svar v)) xs)

  | Case (v, cases) ->
    r := Case (subst svar v, Hir.M.map (subst svar) cases)

  | Mutate (v1, i, v2, k) ->
    r := Mutate (subst svar v1, i, subst svar v2, subst svar k)

  | LetFun ((f, params, k, h, body), next) when M.find f occs = SingleUse ->
    r := !next;
    inline_single_use occs (M.add f (k :: h :: params, body) sbody) svar r

  | LetCons (v, i, elts, next) ->
    r := LetCons (v, i, List.map (subst svar) elts, next);
    inline_single_use occs sbody svar next

  | LetPack (v, elts, next) ->
    r := LetPack (v, List.map (fun (n, v) -> (n, subst svar v)) elts, next);
    inline_single_use occs sbody svar next

  | LetProj (v, i, t, next) ->
    r := LetProj (v, i, subst svar t, next);
    inline_single_use occs sbody svar next

  | LetExtn (_, _, _, next) ->
    inline_single_use occs sbody svar next

  | LetFun ((_, _, _, _, body), next) ->
    inline_single_use occs sbody svar body;
    inline_single_use occs sbody svar next

  | LetRec (bs, next) ->
    let (sbody, bs) = List.fold_left (fun (sbody, acc) info ->
      let (f, params, k, h, body) = info in
      if M.find f occs = SingleUse then
        (M.add f (k :: h :: params, body) sbody, acc)
      else (sbody, info :: acc)) (sbody, []) bs in

    if bs = [] then begin
      r := !next;
      inline_single_use occs sbody svar r
    end else begin
      List.iter (fun (_, _, _, _, body) ->
        inline_single_use occs sbody svar body) bs;
      r := LetRec (List.rev bs, next);
      inline_single_use occs sbody svar next
    end

  | LetCont (bs, next) ->
    let (sbody, bs) = List.fold_left (fun (sbody, acc) info ->
      let (j, params, body) = info in
      if M.find j occs = SingleUse then
        (M.add j (params, body) sbody, acc)
      else (sbody, info :: acc)) (sbody, []) bs in

    if bs = [] then begin
      r := !next;
      inline_single_use occs sbody svar r
    end else begin
      List.iter (fun (_, _, body) ->
        inline_single_use occs sbody svar body) bs;
      r := LetCont (List.rev bs, next);
      inline_single_use occs sbody svar next
    end

type vinfo =
  | Term of Hir.term
  | Var of int

let subst m v =
  match M.find_opt v m with
    | Some (Var v) -> v
    | _ -> v

let rec redux env r = match !r with
  | Module _ ->
    failwith "INVALID NESTED MODULE"

  | LetProj (v, i, t, next) -> begin
    let t = subst env t in
    r := LetProj (v, i, t, next);

    let tail () = redux (M.add v (Term !r) env) next in

    match M.find_opt t env with
      | Some (Term (LetPack (_, elts, _))) -> begin
        match List.nth elts i with
          | (false, elt) ->
            r := !next;
            redux (M.add v (Var elt) env) r
          | _ -> tail ()
      end
      | _ -> tail ()
  end

  | Case (v, cases) -> begin
    let v = subst env v in
    let cases = Hir.M.map (subst env) cases in
    r := Case (v, cases);

    match M.find_opt v env with
      | Some (Term (LetCons (_, i, elts, _))) -> begin
        match Hir.M.find_opt (Some i) cases with
          | Some k -> r := Jmp (k, elts)
          | _ ->
            match Hir.M.find_opt None cases with
              | Some k -> r := Jmp (k, [])
              | _ -> r := Case (v, Hir.M.empty)
      end
      | _ -> ()
  end

  | Export xs ->
    r := Export (List.map (fun (n, v) -> (n, subst env v)) xs)

  | Jmp (k, args) ->
    r := Jmp (subst env k, List.map (subst env) args)

  | App (f, args, k, h) ->
    r := App (subst env f, List.map (subst env) args, subst env k, subst env h)

  | Mutate (v1, i, v2, k) ->
    r := Mutate (subst env v1, i, subst env v2, subst env k)

  | LetCons (v, i, elts, next) ->
    let elts = List.map (subst env) elts in
    r := LetCons (v, i, elts, next);

    redux (M.add v (Term !r) env) next

  | LetPack (v, elts, next) ->
    let elts = List.map (fun (n, v) -> (n, subst env v)) elts in
    r := LetPack (v, elts, next);

    redux (M.add v (Term !r) env) next

  | LetExtn (v, _, _, next) ->
    redux (M.add v (Term !r) env) next

  | LetFun ((_, _, _, _, body), next) ->
    redux env body;
    redux env next

  | LetRec (bs, next) ->
    List.iter (fun (_, _, _, _, next) -> redux env next) bs;
    redux env next

  | LetCont (bs, next) ->
    List.iter (fun (_, _, next) -> redux env next) bs;
    redux env next

let transform e =
  PassFixrec.transform e;
  match e with
    | Module (_, _, r) ->
      let v = collect_occ M.empty r in
      inline_single_use v M.empty M.empty r;
      redux M.empty r
    | _ -> failwith "INVALID TERM ANCHOR"
