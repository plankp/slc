(* This module type checks the surface syntax and lowers it into Hir *)

open Hir

module M = Map.Make (String)

let datadef_table = Hashtbl.create 64
let register_ctors (d : Type.datadef) : unit =
  let (_, _, q) = d in
  Hashtbl.iter (fun k (_, args) ->
    Hashtbl.add datadef_table k (d, args)) q

let datadef_List =
  let open Type in
  let m = Hashtbl.create 2 in
  let self = ("List", [Z.zero], m) in
  Hashtbl.add m "[]" (0, []);
  Hashtbl.add m "::" (1, [TyPly Z.zero; (TyDat (self, [TyPly Z.zero]))]);
  register_ctors self;
  self

let env_collect_free (s : Type.t M.t) =
  M.fold (fun _ -> Type.collect_free) s Type.IdMap.empty

let gen s t =
  Type.gen (env_collect_free s) t

let rec check' s = function
  | Ast.EVar n -> begin
    match M.find_opt n s with
      | None -> failwith ("Name " ^ n ^ " not found")
      | Some t -> Type.inst t
  end

  | Ast.ETup xs ->
    TyTup (List.map (check' s) xs)

  | Ast.ECons (k, dinfo, args) ->
    let (d, params) = match Hashtbl.find_opt datadef_table k with
      | Some q -> q
      | None -> failwith ("Unrecognized data constructor " ^ k) in

    let (_, polys, _) = d in
    let (targs, penv) = List.fold_right (fun p (xs, penv) ->
      let t = Type.new_tyvar () in
      (t :: xs, Type.IdMap.add p t penv)) polys ([], Type.IdMap.empty) in

    let rec loop s = function
      | [], [] ->
        dinfo := d;
        Type.TyDat (d, targs)
      | param :: xs, arg :: ys ->
        let arg = check' s arg in
        let param = Type.subst penv param in
        Type.unify arg param;
        loop s (xs, ys)
      | _ -> failwith "Data constructor argument length mismatch" in
    loop s (params, args)

  | Ast.ELam ([], _) ->
    failwith "INVALID ELAM NODE"

  | Ast.ELam (ps, e) ->
    let (env, args) = List.fold_left (fun (s, acc) p ->
      let (s, p) = check_pat' s p in
      (s, p :: acc)) (M.empty, []) ps in
    let s = M.union (fun _ _ v -> Some v) s env in
    let ty = check' s e in
    List.fold_left (fun r a -> Type.TyArr (a, r)) ty args

  | Ast.ELamCase xs ->
    let valty = Type.new_tyvar () in
    let resty = Type.new_tyvar () in
    List.iter (fun (p, e) ->
      let (binds, ty) = check_pat p in
      Type.unify valty ty;
      let s = M.union (fun _ _ t -> Some t) s binds in
      let ty = check' s e in
      Type.unify resty ty) xs;
    TyArr (valty, resty)

  | Ast.EApp (f, xs) ->
    let funty = check' s f in
    List.fold_left (fun funty a ->
      let argty = check' s a in
      let resty = Type.new_tyvar () in
      Type.unify funty (TyArr (argty, resty));
      resty) funty xs

  | Ast.ELet (b, e) ->
    let mapping = Hashtbl.create 16 in
    let s = b
      |> List.map (fun (n, i) ->
          if Hashtbl.mem mapping n then
            failwith "Illegal duplicate binding in same level";
          Hashtbl.add mapping n ();
          (n, check' s i))
      |> List.fold_left (fun s' (n, t) -> M.add n (gen s t) s') s in
    check' s e

  | Ast.ERec (b, e) ->
    let mapping = Hashtbl.create 16 in
    let s' = List.fold_left (fun s' (n, _) ->
      if Hashtbl.mem mapping n then
        failwith "Illegal duplicate binding in same level";
      let recty = Type.new_tyvar () in
      Hashtbl.add mapping n recty;
      M.add n recty s') s b in
    let s = b
      |> List.map (fun (n, i) ->
          let t1 = check' s' i in
          let t2 = Hashtbl.find mapping n in
          Type.unify t1 t2;
          (n, t1))
      |> List.fold_left (fun s' (n, t) -> M.add n (gen s t) s') s in
    check' s e

  | Ast.ECase (e, xs) ->
    let valty = check' s e in
    let resty = Type.new_tyvar () in
    List.iter (fun (p, e) ->
      let (binds, ty) = check_pat p in
      Type.unify valty ty;
      let s = M.union (fun _ _ t -> Some t) s binds in
      let ty = check' s e in
      Type.unify resty ty) xs;
    resty

and check_pat' s = function
  | Ast.PIgn -> (s, Type.new_tyvar ())

  | Ast.PVar (n, p) -> begin
    let (s, ty) = check_pat' s p in
    match M.find_opt n s with
      | Some _ -> failwith "Illegal duplicate binding in the same pattern"
      | None -> (M.add n ty s, ty)
  end

  | Ast.PTup xs ->
    let (s, xs) = List.fold_left (fun (s, acc) p ->
      let (s, p) = check_pat' s p in
      (s, p :: acc)) (s, []) xs in
    (s, TyTup (List.rev xs))

  | Ast.PDecons (k, dinfo, args) ->
    let (d, params) = match Hashtbl.find_opt datadef_table k with
      | Some q -> q
      | None -> failwith ("Unrecognized data constructor " ^ k) in

    let (_, polys, _) = d in
    let (targs, penv) = List.fold_right (fun p (xs, penv) ->
      let t = Type.new_tyvar () in
      (t :: xs, Type.IdMap.add p t penv)) polys ([], Type.IdMap.empty) in

    let rec loop s = function
      | [], [] ->
        dinfo := d;
        (s, Type.TyDat (d, targs))
      | param :: xs, arg :: ys ->
        let (s, arg) = check_pat' s arg in
        let param = Type.subst penv param in
        Type.unify arg param;
        loop s (xs, ys)
      | _ -> failwith "Data constructor argument length mismatch" in
    loop s (params, args)

and check_pat p =
  check_pat' M.empty p

let check e =
  try
    Ok (check' M.empty e)
  with Failure e -> Error e

let rec lower_funk e id s h k =
  match e with
    | Ast.EVar n -> k id (M.find n s)

    | Ast.ELet (b, e) ->
      let rec beval id s' = function
        | (n, i) :: xs ->
          lower_funk i id s h (fun id i -> beval id (M.add n i s') xs)
        | [] ->
          lower_funk e id s' h k in
      beval id s b

    | Ast.ERec (bs, e) ->
      let (id, s, bs) = List.fold_left (fun (id, s, bs) (n, i) ->
        (id + 1, M.add n id s, (id, i) :: bs)) (id, s, []) bs in
      let (id, bs) = List.fold_left (fun (id, bs) (slot, i) ->
        let (id, term) = lower_funk i id s h (fun id v ->
          (id, Jmp (slot, [v]))) in
        match term with
          | LetFun ((f, args, k, h, r), { contents = Jmp (m1, [m2]) })
            when m1 = slot && m2 = f -> (id, (slot, args, k, h, r) :: bs)
          | _ -> failwith "Recursive bindings cannot have initializers of this form") (id, []) bs in
      let (id, term) = lower_funk e id s h k in
      (id, LetRec (bs, ref term))

    | Ast.ETup xs ->
      let rec loop id acc = function
        | x :: xs ->
          lower_funk x id s h (fun id x -> loop id (x :: acc) xs)
        | [] ->
          let name = id in
          let id, tail = k (id + 1) name in
          (id, LetPack (name, List.rev acc, ref tail)) in
      loop id [] xs

    | Ast.ECons (ctor, { contents = (_, _, mapping) }, args) ->
      let rec loop id acc = function
        | x :: xs ->
          lower_funk x id s h (fun id x -> loop id (x :: acc) xs)
        | [] ->
          let name, id = id, id + 1 in
          let id, tail = k id name in
          let (slot, _) = Hashtbl.find mapping ctor in
          (id, LetCons (name, slot, List.rev acc, ref tail)) in
      loop id [] args

    | Ast.EApp (f, xs) ->
      let rec loop id acc = function
        | x :: xs ->
          lower_funk x id s h (fun id x -> loop id (x :: acc) xs)
        | [] ->
          lower_funk f id s h (fun id f ->
            let rec unfold_args = function
              | [] -> failwith "INVALID EApp NODE"
              | [x] -> (id, App (f, [x], id, h))
              | x :: xs ->
                let (id, term) = unfold_args xs in
                let k = id + 1 in
                (k, LetCont ([id, [id], ref (App (id, [x], k, h))], ref term)) in
            let (id, term) = unfold_args acc in
            let name = id in
            let (id, tail) = k (id + 1) id in
            (id, LetCont ([name, [name], ref tail], ref term))) in
      loop id [] xs

    | Ast.ELam (row, e) ->
      lower_generalized_lambda id [row, s, e] k

    | Ast.ELamCase xs ->
      lower_generalized_lambda id (List.map (fun (p, e) -> ([p], s, e)) xs) k

    | Ast.ECase (e, xs) ->
      lower_funk e id s h (fun id e ->
        let end_k = id in
        let cases = List.map (fun (p, e) -> ([p], s, e)) xs in
        let (id, term) = lower_case [e] (id + 1) cases h (fun id v ->
          (id, Jmp (end_k, [v]))) in
        let (id, tail) = k id end_k in
        (id, LetCont ([end_k, [end_k], ref tail], ref term)))

and lower_generalized_lambda id cases k =
  (* since this is a generalized lambda, the non-empty pattern matrix would
   * have N columns, where each column (from left-to-right) represents one
   * extra level a simple lambda:
   *
   *   GEN_LAM { p1, p2, ... -> e1 } ~~>
   *
   *   \n1 -> \n2 -> ... ->
   *     case { n1, n2, ... } of { p1, p2, ... -> e1 } *)
  match cases with
    | (_ :: cols, _, _) :: _ ->
      let rec unfold_args scruts id = function
        | [] ->
          (* emit the inner most function + case here *)
          let p, id = id, id + 1 in
          let k, id = id, id + 1 in
          let h, id = id, id + 1 in
          let scruts = List.rev_append scruts [p] in
          let (id, term) = lower_case scruts id cases h (fun id v ->
            (id, Jmp (k, [v]))) in
          let tmp, id = id, id + 1 in
          let tail = ref (Export []) in
          (id, tmp, tail, LetFun ((tmp, [p], k, h, ref term), tail))
        | _ :: xs ->
          (* emit an intermediate function that returns an inner function *)
          let p, id = id, id + 1 in
          let k, id = id, id + 1 in
          let h, id = id, id + 1 in
          let (id, inner, tail, term) = unfold_args (p :: scruts) id xs in
          let tmp, id = id, id + 1 in
          tail := Jmp (k, [inner]);
          let tail = ref (Export []) in
          (id, tmp, tail, LetFun ((tmp, [p], k, h, ref term), tail)) in
      let (id, inner, tail, term) = unfold_args [] id cols in
      let (id, outer) = k id inner in
      tail := outer;
      (id, term)
    | _ -> failwith "INVALID GENERALIZED LAMBDA PATTERN MATRIX SHAPE"

and lower_case v id cases h k =
  (* check if the pattern row is all irrefutable atoms *)
  let rec is_simple_capture s = function
    | _ :: vs, Ast.PIgn :: ps ->
      is_simple_capture s (vs, ps)
    | v :: vs, Ast.PVar (n, p) :: ps ->
      is_simple_capture (M.add n v s) (v :: vs, p :: ps)
    | [], [] -> Some s
    | _ -> None in

  (* expands the scrutinee and the pattern matrix by a decons pattern *)
  let expand v = function
    | [] -> failwith "PATTERN MATRIX DIMENSION MISMATCH"
    | ((p, s, e) :: xs) as rows ->
      (* currently expands by the left-most decons term on the first row *)
      let rec loop vinit pinit s = function
        | v :: vs, Ast.PTup elts :: ps ->
          (* Transform:
           *   case v of { p1, p2, ... } -> e
           * to:
           *   case v#0, v#1, ... of p1, p2, ... -> e *)
          let start = id in
          let scrut = v in
          let rec spec id vmid fill pmid = function
            | e :: elts ->
              spec (id + 1) (id :: vmid) (Ast.PIgn :: fill) (e :: pmid) elts
            | [] ->
              let xs = List.map (fun (p, s, e) ->
                let rec coiter pinit s = function
                  | [], Ast.PIgn :: ps ->
                    (ps |> List.rev_append fill |> List.rev_append pinit, s, e)
                  | [], Ast.PTup elts :: ps ->
                    (List.rev_append pinit (elts @ ps), s, e)
                  | [], Ast.PVar (n, p) :: ps ->
                    coiter pinit (M.add n v s) ([], p :: ps)
                  | _ :: xs, p :: ps ->
                    coiter (p :: pinit) s (xs, ps)
                  | _ -> failwith "PATTERN MATRIX DIMENSION MISMATCH" in
                coiter [] s (vinit, p)) xs in
              let v = vs |> List.rev_append vmid |> List.rev_append vinit in
              let p = ps |> List.rev_append pmid |> List.rev_append pinit in
              let (id, term) = lower_case v id ((p, s, e) :: xs) h k in
              let (_, term) = List.fold_left (fun (i, term) _ ->
                (i + 1, LetProj (start + i, i, scrut, ref term))) (0, term) elts in
              (id, term) in
          spec id [] [] [] elts
        | v :: vs, Ast.PDecons (_, { contents = (_, _, max_ctors) }, _) :: _ ->
          (* assume the variant type has data constructors k1 to kN, then
           * what we in essence is specialize the case over every possible
           * constructor.
           *
           * in practice, we specialize over every constructor that appears
           * in this column. if there are cases not covered, then we emit a
           * default case. *)
          let partitions = Hashtbl.create 32 in
          let split_rows = List.map (fun (p, s, e) ->
            let rec coiter pinit s = function
              | [], (Ast.PIgn :: _ as ps) ->
                (pinit, ps, s, e)
              | [], (Ast.PDecons (ctor, _, args) :: _ as ps) ->
                Hashtbl.replace partitions ctor (lazy (
                  List.rev_map (fun _ -> Ast.PIgn) args));
                (pinit, ps, s, e)
              | [], Ast.PVar (n, p) :: ps ->
                coiter pinit (M.add n v s) ([], p :: ps)
              | _ :: xs, p :: ps ->
                coiter (p :: pinit) s (xs, ps)
              | _ -> failwith "PATTERN MATRIX DIMENSION MISMATCH" in
            coiter [] s (vinit, p)) rows in

          let m =
            if Hashtbl.length partitions = Hashtbl.length max_ctors then
              Hir.M.empty
            else begin
              (* need to emit the default case *)
              let m = List.fold_right (fun (pinit, ps, s, e) acc ->
                match ps with
                  | Ast.PIgn :: ps -> (List.rev_append pinit ps, s, e) :: acc
                  | _ -> acc) split_rows [] in
              Hir.M.singleton None ([], m)
            end in
          let m = List.fold_right (fun (pinit, ps, s, e) m ->
            match ps with
              | Ast.PIgn :: ps ->
                Hashtbl.fold (fun ctor fill m ->
                  let (slot, _) = Hashtbl.find max_ctors ctor in
                  let args = Lazy.force fill in
                  let row = ps
                    |> List.rev_append args
                    |> List.rev_append pinit, s, e in
                  Hir.M.update (Some slot) (function
                    | None -> Some (args, [row])
                    | Some (p, xs) -> Some (p, row :: xs)) m) partitions m
              | Ast.PDecons (ctor, _, args) :: ps ->
                let (slot, _) = Hashtbl.find max_ctors ctor in
                let row = List.rev_append pinit (args @ ps), s, e in
                Hir.M.update (Some slot) (function
                  | None -> Some (args, [row])
                  | Some (p, xs) -> Some (p, row :: xs)) m
              | _ -> failwith "PATTERN MATRIX DIMENSION MISMATCH") split_rows m in

          let case_anchor = ref (Export []) in
          let (id, tail, m) = Hir.M.fold (fun slot (args, matrix) (id, tail, m) ->
            let label, id = id, id + 1 in
            let args, id = List.fold_left (fun (args, id) _ ->
              let arg, id = id, id + 1 in
              (arg :: args, id)) ([], id) args in
            let vs = vs |> List.rev_append args |> List.rev_append vinit in
            let (id, term) = lower_case vs id matrix h k in
            let tail = ref (LetCont ([label, List.rev args, ref term], tail)) in
            (id, tail, Hir.M.add slot label m)) m (id, case_anchor, Hir.M.empty) in

          case_anchor := Case (v, m);
          (id, !tail)
        | v :: vs, Ast.PVar (n, p) :: ps ->
          loop vinit pinit (M.add n v s) (v :: vs, p :: ps)
        | v :: vs, p :: ps ->
          loop (v :: vinit) (p :: pinit) s (vs, ps)
        | _ -> failwith "PATTERN MATRIX CANNOT BE EXPANDED" in
      loop [] [] s (v, p) in

  match cases with
    | [] ->
      (* we are expected to match something, but there are no patterns!
       * we synthesize code to raise an error by a jump-to-h *)
      (id + 1, LetPack (id, [], ref (Jmp (h, [id]))))
    | (p, s, e) :: _ ->
      (* if the row is a simple capture, then we're done *)
      match is_simple_capture s (v, p) with
        | Some s -> lower_funk e id s h k
        | None -> expand v cases

let lower e =
  try
    let (_, term) = lower_funk e 1 M.empty 0 (fun id v ->
      (id, Export ["_", v])) in
    Ok (Module (["_"], ref 0, ref term))
  with Failure e -> Error e
