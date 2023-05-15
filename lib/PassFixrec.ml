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

let rec transform s r = match !r with
  | Module _ ->
    failwith "INVALID NESTED MODULE"

  | Export xs ->
    List.fold_left (fun s (_, v) -> S.add v s) s xs

  | Jmp (k, args) ->
    List.fold_left (fun s v -> S.add v s) s (k :: args)

  | App (f, args, k, h) ->
    List.fold_left (fun s v -> S.add v s) s (f :: k :: h :: args)

  | Case (v, cases) ->
    s |> S.add v |> Hir.M.fold (fun _ -> S.add) cases

  | Mutate (v1, _, v2, k) ->
    s |> S.add v1 |> S.add v2 |> S.add k

  | LetFun ((f, _, _, _, body), next) ->
    let s = transform s next in
    if S.mem f s then
      transform s body
    else begin
      r := !next; s
    end

  | LetPack (v, elts, next) ->
    let s = transform s next in
    if S.mem v s then
      List.fold_left (fun s (_, v) -> S.add v s) s elts
    else begin
      r := !next; s
    end

  | LetCons (v, _, elts, next) ->
    let s = transform s next in
    if S.mem v s then
      List.fold_left (fun s v -> S.add v s) s elts
    else begin
      r := !next; s
    end

  | LetProj (v, _, t, next) ->
    let s = transform s next in
    if S.mem v s then
      S.add t s
    else begin
      r := !next; s
    end

  | LetRec (bs, next) ->
    let (defs, fvs) = List.fold_left (fun (defs, xs) info ->
      let (f, _, _, _, next) = info in
      let s = transform S.empty next in
      (S.add f defs, (info, s) :: xs)) (S.empty, []) bs in

    (* build the dependency graph of the bindings *)
    let g = List.fold_left (fun g (info, fvs) ->
      let (f, _, _, _, _) = info in
      let v =
        { info = (info, fvs); deps = S.inter fvs defs
        ; index = None; lowlink = ~-1; onstack = false } in
      M.add f v g) M.empty fvs in

    let s = transform s next in
    let rebuild = compute_levels g in
    let (s, e) = List.fold_left (fun (s, e) scc ->
      let is_dead = not @@ List.exists (fun { info = (info, _); _ } ->
        let (f, _, _, _, _) = info in S.mem f s) scc in
      if is_dead then (s, e)
      else begin
        match scc with
          | [{ info = ((f, _, _, _, _) as info, fv); deps; _ }]
            when not (S.mem f deps) ->
            (S.union fv s, LetFun (info, ref e))
          | _ ->
            let (s, bs) = List.fold_left (fun (s, xs) { info; _ } ->
              let (info, fv) = info in
              (S.union fv s, info :: xs)) (s, []) scc in
            (s, LetRec (bs, ref e))
      end) (s, !next) rebuild in
    r := e;
    s

  | LetCont (bs, next) ->
    let (defs, fvs) = List.fold_left (fun (defs, xs) info ->
      let (j, _, next) = info in
      let s = transform S.empty next in
      (S.add j defs, (info, s) :: xs)) (S.empty, []) bs in

    (* build the dependency graph of the bindings *)
    let g = List.fold_left (fun g (info, fvs) ->
      let (j, _, _) = info in
      let v =
        { info = (info, fvs); deps = S.inter fvs defs
        ; index = None; lowlink = ~-1; onstack = false } in
      M.add j v g) M.empty fvs in

    let s = transform s next in
    let rebuild = compute_levels g in
    let (s, e) = List.fold_left (fun (s, e) scc ->
      let is_dead = not @@ List.exists (fun { info = (info, _); _ } ->
        let (j, _, _) = info in S.mem j s) scc in
      if is_dead then (s, e)
      else begin
        let (s, bs) = List.fold_left (fun (s, xs) { info; _ } ->
          let (info, fv) = info in
          (S.union fv s, info :: xs)) (s, []) scc in
        (s, LetCont (bs, ref e))
      end) (s, !next) rebuild in
    r := e;
    s

let transform e =
  let _ = PassReindex.reindex e in
  match e with
    | Module (_, _, r) -> transform S.empty r |> ignore
    | _ -> failwith "INVALID TERM ANCHOR"
