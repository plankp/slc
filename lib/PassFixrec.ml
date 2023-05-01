open Hir

module S = Set.Make (Int)
module M = Map.Make (Int)

type 'a vertex =
  { info : 'a
  ; deps : S.t
  ; mutable index : int option
  ; mutable lowlink : int
  ; mutable onstack : bool
  }

let compute_levels (g : 'a vertex M.t) : 'a vertex list list =
  (* use Tarjan's scc *)
  let index = ref 0 in
  let stack = ref [] in
  let rebuild = ref [] in

  let rec connect v =
    v.index <- Some !index;
    v.lowlink <- !index;
    v.onstack <- true;
    index := !index + 1;
    stack := v :: !stack;

    S.iter (fun w ->
      let w = M.find w g in
      match w.index with
        | None ->
          connect w;
          v.lowlink <- min v.lowlink w.lowlink
        | Some w_index ->
          if w.onstack then
            v.lowlink <- min v.lowlink w_index) v.deps;

    if Some v.lowlink = v.index then begin
      let rec loop scc =
        match !stack with
          | [] -> failwith "INVALID STATE"
          | w :: xs ->
            stack := xs;
            w.onstack <- false;
            let scc = w :: scc in
            if w != v then loop scc
            else rebuild := scc :: !rebuild in
      loop []
    end in

  M.iter (fun _ v -> if v.index = None then connect v) g;
  !rebuild

let rec transform r = match !r with
  | Module _ ->
    failwith "INVALID NESTED MODULE"

  | Export xs ->
    List.fold_left (fun s (_, v) -> S.add v s) S.empty xs

  | LetCont (bs, e) ->
    (* we only care about functions due to their capturing semantics *)
    let s = transform e in
    List.fold_left (fun s (_, args, body) ->
      let p = transform body in
      let p = List.fold_left (fun p v -> S.remove v p) p args in
      S.union p s) s bs

  | LetFun ((f, args, _, _, body), e) ->
    (* we only care about recursive ones *)
    let s = transform body in
    let s = List.fold_left (fun s v -> S.remove v s) s args in
    transform e |> S.remove f |> S.union s

  | Jmp (_, args) ->
    List.fold_left (fun s v -> S.add v s) S.empty args

  | App (f, args, _, _) ->
    List.fold_left (fun s v -> S.add v s) S.empty (f :: args)

  | Case (v, _) ->
    S.singleton v

  | LetPack (v, elts, e) | LetCons (v, _, elts, e) ->
    let s = transform e in
    let s = S.remove v s in
    List.fold_left (fun s v -> S.add v s) s elts

  | LetProj (v, _, t, e) ->
    transform e |> S.remove v |> S.add t

  | LetRec (bs, e) ->
    let fvs = List.map (fun (_, args, _, _, body) ->
      let s = transform body in
      List.fold_left (fun s v -> S.remove v s) s args) bs in

    let defs = List.fold_left (fun s (f, _, _, _, _) ->
      S.add f s) S.empty bs in

    (* build the dependency graph of the letrec bindings *)
    let g = List.fold_left2 (fun g ((f, _, _, _, _) as info) deps ->
      let v =
        { info; deps = S.inter deps defs
        ; index = None; lowlink = ~-1; onstack = false } in
      M.add f v g) M.empty bs fvs in

    let s = transform e in
    let s = List.fold_left S.union s fvs in
    let s = S.diff s defs in

    (* here we do the rewrite inside out *)
    let rebuild = compute_levels g in
    r := List.fold_left (fun e scc ->
      match scc with
        | [{ info = (f, _, _, _, _) as fv; deps; _ }] when not (S.mem f deps) ->
          LetFun (fv, ref e)
        | _ ->
          LetRec (List.map (fun v -> v.info) scc, ref e)) !e rebuild;
    s

let transform e =
  let _ = PassReindex.reindex e in
  match e with
    | Module (_, _, r) -> transform r |> ignore
    | _ -> failwith "INVALID TERM ANCHOR"
