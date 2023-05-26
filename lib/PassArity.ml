(* This module changes the arity of functions.
 *
 * There are many different ways to change the arity, but the only one done at
 * the moment is raising the arity through uncurrying. Steps are as follows:
 *
 * 1.  uncurry all functions (into multiarg functions), leaving the original
 *     curried form to call these new uncurried variants
 * 2.  look at all usages of the curried forms, rewrite them to using the
 *     uncurried variants if arity matches / call site is saturated.
 *
 * Note that it is highly likely that running this pass alone results in
 * redundant functions. Therefore, it is highly recommended to run
 * simplification after this transformation.
 *)

open Hir

module M = Map.Make (Int)

(* Turns [[a; b; c]; [d; e; g]; [g; h; i]]
 * into [g; h; i; d; e; g; a; b; c] *)
let rev_concat = function
  | [] -> []
  | x :: xs ->
    let rec loop acc = function
      | [] -> acc
      | x :: xs -> loop (x @ acc) xs in
    loop x xs

let rec squash_terms id ((_, args, k, h, body) : funval) =
  let rec unravel levels k h = function
    | LetFun ((f', args', k', h', body'), { contents = Jmp (j, [v]) })
      when j = k && v = f' ->
      let (info, partial, id) = unravel (args' :: levels) k' h' !body' in
      (info, LetFun ((f', args', k', h', ref partial), ref (Jmp (k, [f']))), id)
    | e ->
      let all_args = rev_concat levels in
      let name = id in
      let new_body = ref e in
      let id = raise_def_site (id + 1) new_body in
      ((name, all_args, k, h, new_body), App (name, all_args, k, h), id) in
  unravel [args] k h !body

and raise_def_site id r = match !r with
  | Module _ ->
    failwith "INVALID NESTED MODULE"

  | LetFun (info, next) ->
    let (f, args, k, h, _) = info in
    let (new_info, partial, id) = squash_terms id info in
    let new_body = ref partial in

    r := LetFun (new_info, ref (LetFun ((f, args, k, h, new_body), next)));
    raise_def_site id next

  | LetRec (bs, next) ->
    let (bs, id) = List.fold_left (fun (acc, id) info ->
      let (f, args, k, h, _) = info in
      let (new_info, partial, id) = squash_terms id info in
      let new_body = ref partial in
      ((f, args, k, h, new_body) :: new_info :: acc, id)) ([], id) bs in

    r := LetRec (bs, next);
    raise_def_site id next

  | LetCont (bs, e) ->
    let id = List.fold_left (fun id info ->
      let (_, _, body) = info in
      raise_def_site id body) id bs in
    raise_def_site id e

  | LetCons (_, _, _, e)
  | LetPack (_, _, e)
  | LetProj (_, _, _, e)
  | LetExtn (_, _, _, e) ->
    raise_def_site id e

  | _ -> id

let rec raise_call_site sv sk r = match !r with
  | Module _ ->
    failwith "INVALID NESTED MODULE"

  | LetCont ([j, [partial], { contents = App (f, args, k, h) }], e)
    when f = partial && not (k = j || h = j || List.mem f args) ->
    (* we matched the following pattern:
     * letcont j f = App f args k h in ... *)

    (* compute the longest possible tail *)
    let tail = match M.find_opt k sk with
      | Some (h', tail) when h = h' -> (k, args) :: tail
      | _ -> [k, args] in

    raise_call_site sv (M.add j (h, tail) sk) e

  | App (f, args, k, h) -> begin
    (* see if we can raise the arity, and if we can, do so only if we can
     * saturate the definition. example:
     *
     * cannot raise this one: def site has higher arity (\z -> ...)
     * let f = \w -> \x -> \y -> \z -> f' w x y z in f a b c
     *
     * can raise this one: use site has same or higher arity
     * let f = \w -> \x -> \y -> f' w x y in f a b c d *)

    match M.find_opt k sk with
      | Some (h', tail) when h = h' -> begin
        match M.find_opt f sv with
          | Some info ->
            let rec loop acc info = function
              | [] -> ()  (* def site has higher arity *)
              | (retk, args) :: xs ->
                let (_, params, k, _, body) = info in
                match !body with
                  | LetFun ((f', _, _, _, _) as info', { contents = Jmp (j, [v] )})
                    when j = k && v = f' ->
                    let acc = List.fold_left2 (fun m p a ->
                      M.add p a m) acc params args in
                    loop acc info' xs
                  | App (f, args', _, _) ->
                    let acc = List.fold_left2 (fun m p a ->
                      M.add p a m) acc params args in
                    let args' = List.map (fun old ->
                      acc |> M.find_opt old |> Option.value ~default:old) args' in
                    r := App (f, args', retk, h)
                  | _ -> () (* the def site is not a chain of lambdas *) in
            loop M.empty info ((k, args) :: tail)

          | _ -> ()
      end
      | _ -> ()
  end

  | LetFun (info, e) ->
    let (f, _, _, _, body) = info in
    raise_call_site sv sk body;
    raise_call_site (M.add f info sv) sk e

  | LetRec (bs, e) ->
    let sv = List.fold_left (fun sv info ->
      let (f, _, _, _, _) = info in
      M.add f info sv) sv bs in
    List.iter (fun info ->
      let (_, _, _, _, body) = info in
      raise_call_site sv sk body) bs;
    raise_call_site sv sk e

  | LetCont (bs, e) ->
    List.iter (fun info ->
      let (_, _, body) = info in
      raise_call_site sv sk body) bs;
    raise_call_site sv sk e

  | LetCons (_, _, _, e)
  | LetPack (_, _, e)
  | LetProj (_, _, _, e)
  | LetExtn (_, _, _, e) ->
    raise_call_site sv sk e

  | _ -> ()

let transform e =
  let i = PassReindex.reindex e in
  match e with
    | Module (_, _, r) ->
      let _ = raise_def_site i r in
      let _ = PassReindex.reindex in
      let _ = raise_call_site M.empty M.empty r in
      ()
    | _ -> failwith "INVALID TERM ANCHOR"
