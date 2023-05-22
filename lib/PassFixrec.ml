open Hir

module S = Set.Make (Int)
module M = Map.Make (Int)

let fetch_or_new g f =
  match Hashtbl.find_opt g f with
    | Some v -> v
    | None ->
      let v = Tarjan.new_vertex None in
      Hashtbl.add g f v;
      v

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
    let g = Hashtbl.create 32 in
    List.iter (fun (info, fvs) ->
      let (f, _, _, _, _) = info in
      let v = fetch_or_new g f in
      Tarjan.set_info v (Some (info, fvs));
      let deps = S.inter fvs defs in
      S.iter (fun n ->
        Tarjan.add_edge v (fetch_or_new g n)) deps) fvs;

    let s = transform s next in
    let rebuild = g |> Hashtbl.to_seq_values |> Tarjan.compute_scc in
    let (s, e) = List.fold_left (fun (s, e) scc ->
      let is_dead = not @@ List.exists (fun node ->
        let ((f, _, _, _, _), _) = node |> Tarjan.get_info |> Option.get in
        S.mem f s) scc in
      if is_dead then (s, e)
      else begin
        match scc with
          | [node] when not (Tarjan.has_edge node node) ->
            let (info, fv) = node |> Tarjan.get_info |> Option.get in
            (S.union fv s, LetFun (info, ref e))
          | _ ->
            let (s, bs) = List.fold_left (fun (s, xs) node ->
              let (info, fv) = node |> Tarjan.get_info |> Option.get in
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
    let g = Hashtbl.create 32 in
    List.iter (fun (info, fvs) ->
      let (j, _, _) = info in
      let v = fetch_or_new g j in
      Tarjan.set_info v (Some (info, fvs));
      let deps = S.inter fvs defs in
      S.iter (fun n ->
        Tarjan.add_edge v (fetch_or_new g n)) deps) fvs;

    let s = transform s next in
    let rebuild = g |> Hashtbl.to_seq_values |> Tarjan.compute_scc in
    let (s, e) = List.fold_left (fun (s, e) scc ->
      let is_dead = not @@ List.exists (fun node ->
        let ((j, _, _), _) = node |> Tarjan.get_info |> Option.get in
        S.mem j s) scc in
      if is_dead then (s, e)
      else begin
        let (s, bs) = List.fold_left (fun (s, xs) node ->
          let (info, fv) = node |> Tarjan.get_info |> Option.get in
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
