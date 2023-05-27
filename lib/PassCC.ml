(* This module performs Closure Conversion...
 * except we add a few twists due to how the details of LIR, a SSA language.
 * we outline these special cases below:
 * ~~~
 *
 * for non-recursive functions:
 *
 *   letfun f p... k h = body
 *
 * if body only refers to its function parameters and constants, then after
 * lowering to LIR, this would be a global definition as follows:
 *
 *   def @f' = (p...) { ... }
 *   def @f  = { f', #0 }
 *
 * now that this is a (constant) global definition, any further references
 * shall not be closure captured.
 *
 * same applies to recursive functions (we assume the binding to form a scc
 * for simplicity. we know this is the case because of simplify, but not being
 * scc has no affect on correctness):
 *
 *   letrec f1 p... k1 h1 = body1
 *   and    f2 p... k2 h2 = body2
 *
 * if the only free variables of body1 and body2 aside from the respective
 * function parameters and constants are f1 or f2 (or both), then, like
 * before, we can hoist the whole thing into a global definition:
 *
 *  def @f1' = (p...) { ... }
 *  def @f2' = (p...) { ... }
 *  def @f1  = { f1', #0 }
 *  def @f2  = { f2', #0 }
 *
 * ~~~ and thus accounts for all the special cases
 *
 * otherwise, closure convert as usual.
 * we implement it using a bottom-up scheme
 *)

open Hir

module S = Set.Make (Int)

let rec cc r ignore id = match !r with
  | Module _ ->
    failwith "INVALID NESTED MODULE"

  (* logic for rewriting functions to account for escaping values *)

  | LetFun ((f, args, k, h, body), e) ->
    let (id, esc) = cc body ignore id in

    (* clearly the paramters of the function do not escape *)
    let esc = List.fold_left (fun s a -> S.remove a s) esc args in
    (* the global constants also do not escape *)
    let esc = S.diff esc ignore in

    (* whatever is escaping needs to captured inside the envptr
     * and unpacked as soon as we enter the function *)
    let id_pack, id = id, id + 1 in
    let id_envp, id = id, id + 1 in

    let _ = S.fold (fun esc slot ->
      body := LetProj (esc, slot, id_envp, ref (!body));
      slot + 1) esc 0 in

    let elts = esc |> S.elements |> List.map (fun v -> (false, v)) in
    r := LetPack (id_pack, elts, ref (
          LetFun ((f, args @ [id_envp], k, h, body), ref (
            LetPack (f, [(false, f); (false, id_pack)], e)))));

    (* if there are no free variables, then this is should be ignored *)
    let ignore = if elts = [] then S.add f ignore else ignore in
    let (id, fv2) = cc e ignore id in
    (id, fv2 |> S.remove f |> S.union esc)

  | LetRec (bs, e) ->
    let (id, esc) = List.fold_left (fun (id, total) (_, args, _, _, body) ->
      let (id, esc) = cc body ignore id in
      let esc = List.fold_left (fun s a -> S.remove a s) esc args in
      (id, S.union esc total)) (id, S.empty) bs in

    (* if it's global constant, then we don't care about the functions.
     * if it's not, then we will always capture all the functions.
     *
     * in other words, ignore the references to the functions here *)
    let esc = List.fold_left (fun s (f, _, _, _, _) -> S.remove f s) esc bs in

    (* here we need to account for the two cases separately. *)
    if S.is_empty esc then begin
      (* in effect, we want to rewrite it into something like this:
       * let rec f1' p... = ...
       * and     f2' p... = ...
       * and     f1 = (f1', ())
       * and     f2 = (f2', ())
       *
       * unfortunately, we don't support recursive values. so we do this:
       *  letrec f1' p... k h =
       *    let f1 = { f1', {} } in
       *    let f2 = { f1', {} } in ...
       *  and    f2' p... k h = ... (omitted, same idea)
       *  let f1 = { f1', {} } in
       *  let f2 = { f2', {} } in
       *
       * notice that it's still a letrec
       *)
      let (id, new_names) = List.fold_left (fun (id, acc) _ ->
        (id + 1, id :: acc)) (id, []) bs in
      let bs' = List.map2 (fun (_, args, k, h, body) f ->
        List.iter2 (fun (f, _, _, _, _) f' ->
          body := LetPack (f, [], ref (
            LetPack (f, [(false, f'); (false, f)], ref (
              !body))))) bs new_names;
        (f, args @ [id], k, h, body)) bs new_names in
      r := LetRec (bs', e);

      let ignore = List.fold_left (fun s (f, _, _, _, _) ->
        S.add f s) ignore bs in
      let (id, fv2) = cc e ignore id in
      List.iter2 (fun (f, _, _, _, _) f' ->
        e := LetPack (f, [], ref (
          LetPack (f, [(false, f'); (false, f)], ref (
            !e))))) bs new_names;

      (id, List.fold_left (fun s (f, _, _, _, _) -> S.remove f s) fv2 bs)
    end else begin
      (* if we need capturing, then all the functions share one environment.
       * translate as follows:
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

      let id_pack, id = id, id + 1 in
      let id_envp, id = id, id + 1 in

      let bs = List.map (fun (f, args, k, h, body) ->
        let (new_body, slot) = List.fold_left (fun (body, slot) (f, _, _, _, _) ->
          (ref (LetProj (f, slot, id_envp, ref (
            LetPack (f, [(false, f); (false, id_envp)], body)))), slot + 1)) (body, 0) bs in
        let _ = S.fold (fun esc slot ->
          body := LetProj (esc, slot, id_envp, ref (!body));
          slot + 1) esc slot in
        (f, args @ [id_envp], k, h, new_body)) bs in

      let fat_env = esc
        |> S.elements
        |> List.map (fun v -> (false, v))
        |> List.fold_right (fun (f, _, _, _, _) xs -> (false, f) :: xs) bs in
      let tail = List.fold_left (fun e (f, _, _, _, _) ->
        ref (LetPack (f, [(false, f); (false, id_pack)], e))) e bs in
      r := List.fold_right (fun f tail ->
        LetFun (f, ref tail)) bs (LetPack (id_pack, fat_env, tail));

      let (id, fv2) = cc e ignore id in
      let fv2 = List.fold_left (fun fv2 (f, _, _, _, _) -> S.remove f fv2) fv2 bs in
      (id, S.union esc fv2)
    end

  (* the rest is just computing free variables.
   * some of these result in constants, which can be ignored (read the logic
   * above), but we ignore them for now for simplicity *)

  | Export xs ->
    (id, List.fold_left (fun s (_, v) -> S.add v s) S.empty xs)

  | LetCont (bs, e) ->
    (* continuations cannot escape, so no need to closure convert.
     * just propagate the FVs *)
    let (id, esc) = cc e ignore id in
    List.fold_left (fun (id, esc) (_, args, body) ->
      let (id, p) = cc body ignore id in
      let p = List.fold_left (fun s a -> S.remove a s) p args in
      (id, S.union p esc)) (id, esc) bs

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

  | LetPack (v, elts, e) ->
    let (id, esc) = cc e ignore id in
    let esc = S.remove v esc in
    (id, List.fold_left (fun s (_, v) -> S.add v s) esc elts)

  | LetCons (v, _, elts, e) ->
    let (id, esc) = cc e ignore id in
    let esc = S.remove v esc in
    (id, List.fold_left (fun s v -> S.add v s) esc elts)

  | LetProj (v, _, t, e) ->
    let (id, esc) = cc e ignore id in
    let esc = S.remove v esc in
    (id, S.add t esc)

  | LetExtn (v, _, _, e) ->
    (* this is NOT a constant expression since it loads *)
    let (id, esc) = cc e ignore id in
    (id, S.remove v esc)

  | Case (v, _) ->
    (id, S.singleton v)

  | Mutate (v1, _, v2, _) ->
    (id, S.of_list [v1; v2])

let transform e =
  let id = PassReindex.reindex e in
  match e with
    | Module (_, _, r) ->
      let (_, s) = cc r S.empty id in
      if not (S.is_empty s) then
        failwith "INVALID ESCAPING FV"
    | _ -> failwith "INVALID TERM ANCHOR"
