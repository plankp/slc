(* This module type checks the surface syntax and lowers it into Hir *)

open Hir

module M = Map.Make (String)

type ('a, 'b) ventry =
  | Ctor of 'a
  | Value of 'b

let register_ctors (d : Type.datadef) s =
  let (_, _, q) = d in
  Hashtbl.fold (fun k (_, args) s ->
    M.add k (Ctor (d, args)) s) q s

let env_collect_free (s : ('a, Type.t) ventry M.t) =
  M.fold (fun _ v s ->
    match v with
      | Value v -> Type.collect_free v s
      | _ -> s) s Type.IdMap.empty

let gen s t =
  Type.gen (env_collect_free s) t

let group_binders b =
  List.fold_right (fun (n, p, e) m ->
    M.update n (function
      | None -> Some [(p, e)]
      | Some v ->
        match v, p with
          | ([], _) :: _, _ ->
            failwith "Duplicate name with binding without pattern"
          | (xs, _) :: _, ys -> begin
            let () = try
              List.iter2 (fun _ _ -> ()) xs ys
            with
              _ -> failwith "Cannot mix bindings of different argument lengths" in
            Some ((p, e) :: v)
          end
          | _ -> failwith "INVALID BINDER GROUP STATE") m) b M.empty

let rec check' s = function
  | Ast.EVar n -> begin
    match M.find_opt n s with
      | Some (Value t) -> Type.inst t
      | _ -> failwith ("Name " ^ n ^ " not found")
  end

  | Ast.ETup xs ->
    TyTup (List.map (check' s) xs)

  | Ast.ECons (k, dinfo, args) ->
    let (d, params) = match M.find_opt k s with
      | Some (Ctor q) -> q
      | _ -> failwith ("Unrecognized data constructor " ^ k) in

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
    check_generalized_lambda s [ps, e]

  | Ast.ELamCase xs ->
    xs |> List.map (fun (p, e) -> ([p], e)) |> check_generalized_lambda s

  | Ast.EApp (f, xs) ->
    let funty = check' s f in
    List.fold_left (fun funty a ->
      let argty = check' s a in
      let resty = Type.new_tyvar () in
      Type.unify funty (TyArr (argty, resty));
      resty) funty xs

  | Ast.ELet (b, e) ->
    let s = check_let_binder s b in
    check' s e

  | Ast.ERec (b, e) ->
    let s = check_rec_binder s b in
    check' s e

  | Ast.ECase (e, xs) ->
    let valty = check' s e in
    let resty = Type.new_tyvar () in
    List.iter (fun (p, e) ->
      let (binds, ty) = check_pat M.empty s p in
      Type.unify valty ty;
      let s = M.union (fun _ _ t -> Some t) s binds in
      let ty = check' s e in
      Type.unify resty ty) xs;
    resty

and check_generalized_lambda s cases =
  let rowty = Type.new_tyvar () in
  List.iter (fun (ps, e) ->
    let (env, args) = List.fold_left (fun (env, acc) p ->
      let (env, p) = check_pat env s p in
      (env, p :: acc)) (M.empty, []) ps in
    let s = M.union (fun _ _ v -> Some v) s env in
    let ty = check' s e in
    let ty = List.fold_left (fun r a -> Type.TyArr (a, r)) ty args in
    Type.unify ty rowty) cases;
  Type.unwrap_shallow rowty

and check_let_binder s b =
  let g = group_binders b in
  let g = M.map (check_generalized_lambda s) g in
  M.fold (fun n t s' -> M.add n (Value (gen s t)) s') g s

and check_rec_binder s b =
  let mapping = Hashtbl.create 16 in
  let g = group_binders b in
  let s' = M.fold (fun n _ s' ->
    let recty = Type.new_tyvar () in
    Hashtbl.add mapping n recty;
    M.add n (Value recty) s') g s in
  let g = M.mapi (fun n mat ->
    let t1 = check_generalized_lambda s' mat in
    let t2 = Hashtbl.find mapping n in
    Type.unify t1 t2;
    t1) g in
  M.fold (fun n t s' -> M.add n (Value (gen s t)) s') g s

and check_pat acc s = function
  | Ast.PIgn -> (acc, Type.new_tyvar ())

  | Ast.PVar (n, p) -> begin
    let (acc, ty) = check_pat acc s p in
    match M.find_opt n acc with
      | None -> (M.add n (Value ty) acc, ty)
      | _ -> failwith "Illegal duplicate binding in the same pattern"
  end

  | Ast.PTup xs ->
    let (acc, xs) = List.fold_left (fun (acc, xs) p ->
      let (acc, p) = check_pat acc s p in
      (acc, p :: xs)) (acc, []) xs in
    (acc, TyTup (List.rev xs))

  | Ast.PDecons (k, dinfo, args) ->
    let (d, params) = match M.find_opt k s with
      | Some (Ctor q) -> q
      | _ -> failwith ("Unrecognized data constructor " ^ k) in

    let (_, polys, _) = d in
    let (targs, penv) = List.fold_right (fun p (xs, penv) ->
      let t = Type.new_tyvar () in
      (t :: xs, Type.IdMap.add p t penv)) polys ([], Type.IdMap.empty) in

    let rec loop acc = function
      | [], [] ->
        dinfo := d;
        (acc, Type.TyDat (d, targs))
      | param :: xs, arg :: ys ->
        let (acc, arg) = check_pat acc s arg in
        let param = Type.subst penv param in
        Type.unify arg param;
        loop acc (xs, ys)
      | _ -> failwith "Data constructor argument length mismatch" in
    loop acc (params, args)

and eval_texpr s = function
  | Ast.TEVar n -> begin
    match M.find_opt n s with
      | Some (Value t) -> t
      | _ -> failwith ("Type variable " ^ n ^ " not found")
  end

  | Ast.TEArr (a, r) ->
    Type.TyArr (eval_texpr s a, eval_texpr s r)

  | Ast.TETup elts ->
    Type.TyTup (List.map (eval_texpr s) elts)

  | Ast.TECons (k, args) ->
    match M.find_opt k s with
      | Some (Ctor info) ->
        let (_, params, _) = info in
        let args = try
          List.fold_left2 (fun xs a _ -> eval_texpr s a :: xs) [] args params
        with _ -> failwith ("Type constructor argument length mismatch") in
        Type.TyDat (info, List.rev args)
      | _ -> failwith ("Type constructor " ^ k ^ " not found")

and check_data_def styp b =
  let m = Hashtbl.create 16 in
  let ctors = List.map (fun (n, targs, _) ->
    let (_, targs, env) = List.fold_left (fun (v, xs, m) a ->
      let m = M.update a (function
        | None -> Some (Value (Type.TyPly v))
        | _ -> failwith "Illegal duplicate type argument in same data definition") m in
      (Z.succ v, v :: xs, m)) (Z.zero, [], M.empty) targs in

    let mapping = Hashtbl.create 16 in
    let self = (n, List.rev targs, mapping) in
    if Hashtbl.mem m n then
      failwith "Illegal duplicate data name in same block";
    Hashtbl.add m n (mapping, env);
    self) b in

  let styp = List.fold_left (fun styp self ->
    let (n, _, _) = self in
    M.add n (Ctor self) styp) styp ctors in

  List.iter (fun (n, _, cases) ->
    let (m, env) = Hashtbl.find m n in
    let styp = M.union (fun _ _ v -> Some v) styp env in
    List.iteri (fun i (k, args) ->
      if Hashtbl.mem m k then
        failwith "Illegal duplicate constrructor in same data definition";
      Hashtbl.add m k (i, List.map (eval_texpr styp) args)) cases) b;

  ctors

let check (exports, m) =
  let rec check_module sval styp = function
    | [] -> (sval, styp)
    | Ast.RExpr e :: xs ->
      let _ = check' sval e in
      check_module sval styp xs
    | Ast.RLet b :: xs ->
      let sval = check_let_binder sval b in
      check_module sval styp xs
    | Ast.RRec b :: xs ->
      let sval = check_rec_binder sval b in
      check_module sval styp xs
    | Ast.RData b :: xs ->
      let ctors = check_data_def styp b in
      let (sval, styp) = List.fold_left (fun (sval, styp) ctor ->
        let (n, _, _) = ctor in
        (register_ctors ctor sval, M.add n (Ctor ctor) styp)) (sval, styp) ctors in
      check_module sval styp xs in

  let sval = register_ctors Type.datadef_List M.empty in
  let styp = M.singleton "[]" (Ctor Type.datadef_List) in
  try
    let (sval, _) = check_module sval styp m in
    List.iter (fun n ->
      if not (M.mem n sval) then
        failwith ("Cannot export non existent " ^ n)) exports;
    Ok ()
  with Failure e -> Error e

let rec lower_funk e id s h k =
  match e with
    | Ast.EVar n -> k id (M.find n s)

    | Ast.ELet (b, e) ->
      lower_let_binder b id s h (fun id s ->
        lower_funk e id s h k)

    | Ast.ERec (b, e) ->
      lower_rec_binder b id s h (fun id s ->
        lower_funk e id s h k)

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

and lower_let_binder b id s h k =
  let rec loop id s' n = match n () with
    | Seq.Cons ((n, ([], i) :: _), xs) ->
      lower_funk i id s h (fun id i -> loop id (M.add n i s') xs)
    | Seq.Cons ((n, mat), xs) ->
      let mat = List.map (fun (p, e) -> (p, s, e)) mat in
      lower_generalized_lambda id mat (fun id i -> loop id (M.add n i s') xs)
    | Seq.Nil ->
      k id s' in
  b |> group_binders |> M.to_seq |> loop id s

and lower_rec_binder b id s h k =
  let (id, s, b) = b
    |> group_binders
    |> M.to_seq
    |> Seq.fold_left (fun (id, s, b) (n, mat) ->
      (id + 1, M.add n id s, (id, mat) :: b)) (id, s, []) in
  let (id, b) = List.fold_left (fun (id, b) (slot, i) ->
    let (id, term) = match i with
      | ([], i) :: _ ->
        lower_funk i id s h (fun id v -> (id, Jmp (slot, [v])))
      | mat ->
        let mat = List.map (fun (p, e) -> (p, s, e)) mat in
        lower_generalized_lambda id mat (fun id v -> (id, Jmp (slot, [v]))) in
    match term with
      | LetFun ((f, args, k, h, r), { contents = Jmp (m1, [m2]) })
        when m1 = slot && m2 = f -> (id, (slot, args, k, h, r) :: b)
      | _ -> failwith "Recursive bindings cannot have initializers of this form") (id, []) b in
  let (id, term) = k id s in
  (id, LetRec (b, ref term))

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

let lower (exports, m) =
  let export_sym = ref [] in
  let rec lower_module id s = function
    | [] -> begin
      let m = Hashtbl.create 16 in
      let (list1, list2) = List.fold_left (fun (xs, ys) n ->
        if Hashtbl.mem m n then (xs, ys)
        else begin
          Hashtbl.add m n ();
          ((n, M.find n s) :: xs, n :: ys)
        end) ([], []) exports in
      export_sym := list2;
      (id, Export list1)
    end
    | Ast.RExpr e :: xs ->
      lower_funk e id s 0 (fun id _ -> lower_module id s xs)
    | Ast.RLet b :: xs ->
      lower_let_binder b id s 0 (fun id s -> lower_module id s xs)
    | Ast.RRec b :: xs ->
      lower_rec_binder b id s 0 (fun id s -> lower_module id s xs)
    | Ast.RData _ :: xs ->
      lower_module id s xs in
  try
    let (_, term) = lower_module 1 M.empty m in
    Ok (Module (!export_sym, ref 0, ref term))
  with Failure e -> Error e
