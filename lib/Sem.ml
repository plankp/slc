(* This module type checks the surface syntax and lowers it into Hir *)

open Hir

module M = Map.Make (String)
module S = Set.Make (String)

type ('a, 'b) ventry =
  | Ctor of 'a
  | Value of 'b

type typescheme_t = Type.RSet.t * Type.t
type ctorinfo_t = Type.datadef * Type.tname list * Type.t list
type styp_t = (Type.datadef, Type.t) ventry M.t
type sval_t = (ctorinfo_t, typescheme_t) ventry M.t

let register_ctors (d : Type.datadef) s =
  Hashtbl.fold (fun k (_, extn, args) s ->
    M.add k (Ctor (d, extn, args)) s) d.cases s

let group_binders b =
  let mval = Hashtbl.create 16 in
  let mtyp = Hashtbl.create 16 in
  let bump_binder = function
    | Ast.BAnnot (n, t) ->
      if Hashtbl.mem mtyp n then
        failwith ("Duplicate type annotation on binding " ^ n);
      Hashtbl.replace mtyp n t
    | Ast.BValue (n, p, e) ->
      let mat = Hashtbl.find_opt mval n |> Option.value ~default:[] in
      let mat = match mat, p with
        | [], _ -> [(p, e)]
        | ([], _) :: _, _ ->
          failwith ("Duplicate binding without pattern for " ^ n)
        | (xs, _) :: _, ys ->
          let () = try
            List.iter2 (fun _ _ -> ()) xs ys
          with
            _ -> failwith "Binding is declared with differing argument lengths" in
          (p, e) :: mat in
      Hashtbl.replace mval n mat in
  List.iter bump_binder b;

  let m = Hashtbl.fold (fun n mat s ->
    let mat = List.rev mat in
    let typ = Hashtbl.find_opt mtyp n in
    Hashtbl.remove mtyp n;
    (n, typ, mat) :: s) mval [] in

  Hashtbl.iter (fun k _ ->
    failwith ("Missing definition for binding " ^ k)) mtyp;

  m

let ( let< ) = Result.bind

type state =
  { venv : sval_t
  ; tenv : styp_t
  ; level : Type.level
  }

let rec check_texpr allow_fresh s = function
  | Ast.TEVar n -> begin
    match M.find_opt n s.tenv with
      | Some (Value t) -> Ok (s, t)
      | _ when not allow_fresh -> Error ("Type variable " ^ n ^ " not found")
      | _ ->
        let t = Type.new_tyvar s.level in
        Ok ({ s with tenv = M.add n (Value t) s.tenv }, t)
  end

  | Ast.TERef e ->
    let< (s, e) = check_texpr allow_fresh s e in
    Ok (s, Type.TyRef e)

  | Ast.TEArr (a, r) ->
    let< (s, a) = check_texpr allow_fresh s a in
    let< (s, r) = check_texpr allow_fresh s r in
    Ok (s, Type.TyArr (a, r))

  | Ast.TETup elts ->
    let rec loop s acc = function
      | [] -> Ok (s, Type.TyTup (List.rev acc))
      | x :: xs ->
        let< (s, x) = check_texpr allow_fresh s x in
        loop s (x :: acc) xs in
    loop s [] elts

  | Ast.TECons (k, args) ->
    match M.find_opt k s.tenv with
      | Some (Ctor info) ->
        let rec loop s acc = function
          | [], [] -> Ok (s, Type.TyDat (info, List.rev acc))
          | x :: xs, _ :: ys ->
            let< (s, x) = check_texpr allow_fresh s x in
            loop s (x :: acc) (xs, ys)
          | _ -> Error "Type constructor argument length mismatch" in
        loop s [] (args, info.args)

      | _ -> Error ("Type constructor " ^ k ^ " not found")

let lookup_data_ctor t s k =
  match Type.unwrap_shallow t with
    | TyDat (d, targs) -> begin
      match Hashtbl.find_opt d.cases k with
        | None -> Error ("Unrecognized data constructor " ^ k)
        | Some (_, extn, params) ->
          let penv = List.fold_left2 (fun penv (p, _) t ->
            Type.RMap.add p t penv) Type.RMap.empty d.args targs in
          Ok (d, extn, params, penv)
    end
    | _ ->
      match M.find_opt k s.venv with
        | Some (Ctor (d, extn, params)) ->
          let (targs, penv) = List.fold_right (fun (p, _) (xs, penv) ->
            let t = Type.new_tyvar s.level in
            (t :: xs, Type.RMap.add p t penv)) d.args ([], Type.RMap.empty) in
          Type.unify t (Type.TyDat (d, targs));
          Ok (d, extn, params, penv)
        | _ -> Error ("Unrecognized data constructor " ^ k)

let rec check_pat t binds s = function
  | Ast.PIgn -> Ok (binds, s)

  | Ast.PVar (n, p) ->
    if S.mem n binds then
      Error ("Binding " ^ n ^ " is not linearly bound")
    else
      let s = { s with venv = M.add n (Value (Type.RSet.empty, t)) s.venv } in
      check_pat t (S.add n binds) s p

  | Ast.PTyped (p, t') ->
    let< (s, t') = check_texpr true s t' in
    Type.unify t t';
    check_pat t' binds s p

  | Ast.PDeref p ->
    let t' = Type.new_tyvar s.level in
    Type.unify t (Type.TyRef t');
    check_pat t' binds s p

  | Ast.PTup xs ->
    let rec walk_subpat binds s = function
      | [] -> Ok (binds, s)
      | (x, t) :: xs ->
        let< (binds, s) = check_pat t binds s x in
        walk_subpat binds s xs in
    let rec fill_tyvars acc = function
      | [] ->
        Type.unify t (Type.TyTup (List.rev_map snd acc));
        walk_subpat binds s acc
      | x :: xs ->
        let t = Type.new_tyvar s.level in
        fill_tyvars ((x, t) :: acc) xs in
    fill_tyvars [] xs

  | Ast.PDecons (k, dinfo, args) ->
    let< (d, extn, params, penv) = lookup_data_ctor t s k in

    (* unlike constructing data terms, which map existentials to fresh
     * unification type variables, we map them to fresh rigid type variables.
     *
     * we do this because:
     * -  the type is opaque (can be anything)
     * -  the type must not escape *)
    let penv = List.fold_left (fun penv p ->
      let t = Type.new_poly s.level in
      Type.RMap.add p t penv) penv extn in

    (* which brings us to the issue that since we may bound existentials,
     * all subpatterns must be one level deeper. (has to do with scoped type
     * variables) *)

    let rec loop binds s = function
      | [], [] ->
        dinfo := d;
        let s = { s with level = Type.decr_level s.level } in
        Ok (binds, s)
      | param :: xs, arg :: ys ->
        let param = Type.subst penv param in
        let< (binds, s) = check_pat param binds s arg in
        loop binds s (xs, ys)
      | _ -> Error "Data constructor argument length mismatch" in
    let s = { s with level = Type.incr_level s.level } in
    loop binds s (params, args)

let rec is_value = function
  | Ast.EVar _ | Ast.ELam _ | Ast.ELamCase _ -> true
  | Ast.ETup xs | Ast.ECons (_, _, xs) -> List.for_all is_value xs
  | Ast.ETyped (e, _) -> is_value e
  | ECase (e, xs) when is_value e ->
    List.for_all (fun (_, e) -> is_value e) xs
  | Ast.ELet (bs, e) | Ast.ERec (bs, e) when is_value e ->
    List.for_all (function
      | Ast.BValue (_, [], e) -> is_value e
      | Ast.BAnnot _ | Ast.BValue _ -> true) bs
  | Ast.ESeq (x, xs) ->
    List.for_all is_value (x :: xs)
  | _ -> false

let is_value_binder_rhs = function
  | [[], e] -> is_value e
  | _ -> true

let rec check_expr s = function
  | Ast.EVar n -> begin
    match M.find_opt n s.venv with
      | Some (Value (foralls, t)) -> Ok (Type.inst foralls s.level t)
      | _ -> Error ("Name " ^ n ^ " not found")
  end

  | Ast.ECons (k, dinfo, args) -> begin
    match M.find_opt k s.venv with
      | Some (Ctor (d, extn, params)) ->
        let (targs, penv) = List.fold_right (fun (p, _) (xs, penv) ->
          let t = Type.new_tyvar s.level in
          (t :: xs, Type.RMap.add p t penv)) d.args ([], Type.RMap.empty) in

        (* when constructing, replace existentials with fresh unification type
         * variables *)
        let penv = List.fold_left (fun penv p ->
          let t = Type.new_tyvar s.level in
          Type.RMap.add p t penv) penv extn in

        let rec loop = function
          | [], [] ->
            dinfo := d;
            Ok (Type.TyDat (d, targs))
          | param :: xs, arg :: ys ->
            let< arg = check_expr s arg in
            let param = Type.subst penv param in
            Type.unify arg param;
            loop (xs, ys)
          | _ -> Error "Data constructor argument length mismatch" in
        loop (params, args)

      | _ -> Error ("Unrecognizeed data constructor " ^ k)
  end

  | Ast.ETup xs ->
    let rec loop elts = function
      | [] -> Ok (Type.TyTup (List.rev elts))
      | x :: xs ->
        let< t = check_expr s x in
        loop (t :: elts) xs in
    loop [] xs

  | Ast.ESeq (x, xs) ->
    let rec loop x = function
      | [] -> check_expr s x
      | y :: ys ->
        let< _ = check_expr s x in
        loop y ys in
    loop x xs

  | Ast.ERef e ->
    let< e = check_expr s e in
    Ok (Type.TyRef e)

  | Ast.EAssign (d, v) ->
    let< d = check_expr s d in
    let< v = check_expr s v in
    Type.unify d (Type.TyRef v);
    Ok (Type.TyTup [])

  | Ast.EDeref e ->
    let< e = check_expr s e in
    let t = Type.new_tyvar s.level in
    Type.unify e (Type.TyRef t);
    Ok t

  | Ast.EApp (f, xs) ->
    let rec loop t1 = function
      | [] -> Ok t1
      | x :: xs ->
        let< t2 = check_expr s x in
        let alpha = Type.new_tyvar s.level in
        Type.unify t1 (Type.TyArr (t2, alpha));
        loop alpha xs in
    let< t1 = check_expr s f in
    loop t1 xs

  | Ast.ETyped (e, t) ->
    let< (_, t) = check_texpr false s t in
    let< e = check_expr s e in
    Type.unify t e;
    Ok t

  | Ast.ELam (ps, e) ->
    check_binder_rhs s [ps, e]

  | Ast.ELamCase xs ->
    let valty = Type.new_tyvar s.level in
    let< resty = check_case valty s xs in
    Ok (Type.TyArr (valty, resty))

  | Ast.ECase (e, xs) ->
    let< valty = check_expr s e in
    check_case valty s xs

  | Ast.ELet (g, e) ->
    let< s = check_binders false s g in
    check_expr s e

  | Ast.ERec (g, e) ->
    let< s = check_binders true s g in
    check_expr s e

and check_case valty s xs =
  let resty = Type.new_tyvar s.level in
  let rec loop = function
    | [] -> Ok resty
    | (p, e) :: xs ->
      let< (_, s) = check_pat valty S.empty s p in
      let s = { s with level = Type.incr_level s.level } in
      let< r = check_expr s e in
      Type.unify r resty;
      loop xs in
  loop xs

and check_binder_rhs s cases =
  let rowty = Type.new_tyvar s.level in
  let rec loop = function
    | [] -> Ok rowty
    | (ps, e) :: xs ->
      let rec collect_cols binds s args = function
        | [] ->
          let s = { s with level = Type.incr_level s.level } in
          let< r = check_expr s e in
          let r = List.fold_left (fun r a -> Type.TyArr (a, r)) r args in
          Type.unify rowty r;
          loop xs
        | p :: ps ->
          let t = Type.new_tyvar s.level in
          let< (binds, s) = check_pat t binds s p in
          collect_cols binds s (t :: args) ps in
      collect_cols S.empty s [] ps in
  loop cases

and check_binders recur s g =
  let< g = try Ok (group_binders g) with Failure e -> Error e in
  let m = Hashtbl.create 32 in

  let rec gen_binders s = function
    | [] -> Ok s
    | (n, t) :: xs ->
      let (foralls, t') = Hashtbl.find m n in
      Type.unify t t';
      let t = match foralls with
        | None -> Type.gen s.level t
        | Some s -> (s, t) in
      gen_binders { s with venv = M.add n (Value t) s.venv } xs in

  let rec eval_binders acc rhs_s = function
    | [] -> gen_binders s acc
    | (n, _, mat) :: xs ->
      let s = { rhs_s with level = Type.incr_level rhs_s.level } in
      let< t = check_binder_rhs s mat in
      (* value restriction *)
      if not (is_value_binder_rhs mat) then
        Type.drop_dangerous_level rhs_s.level t;
      eval_binders ((n, t) :: acc) rhs_s xs in

  let rec fill_annots s' = function
    | [] ->
      let rhs_env = if recur then s' else s in
      eval_binders [] rhs_env g
    | (n, None, _) :: xs ->
      let t = s.level |> Type.incr_level |> Type.new_tyvar in
      fill_annots_tail s' n (None, t) xs
    | (n, Some typ, _) :: xs ->
      let s = { s with level = Type.incr_level s.level } in
      let< (_, t) = check_texpr true s typ in
      let s = { s with level = Type.decr_level s.level } in
      let (foralls, t) = Type.gen s.level t in
      fill_annots_tail s' n (Some foralls, t) xs
  and fill_annots_tail s n (foralls, t) xs =
    Hashtbl.add m n (foralls, t);
    let foralls = Option.value ~default:Type.RSet.empty foralls in
    fill_annots { s with venv = M.add n (Value (foralls, t)) s.venv } xs in

  fill_annots s g

let check_data_def s b =
  let m = Hashtbl.create 16 in
  let ctors = List.map (fun (name, targs, _) ->
    let (_, targs, env) = List.fold_left (fun (v, xs, m) (vannot, a) ->
      let info = (v, Type.null_level) in
      let m = M.update a (function
        | None -> Some (Value (Type.TyPly info))
        | _ -> failwith "Illegal duplicate type argument in same data definition") m in
      let variance = match vannot with
        | None -> Type.Invariant
        | Some true -> Type.Covariant
        | Some false -> Type.Contravariant in
      (Z.succ v, (info, variance) :: xs, m)) (Z.zero, [], M.empty) targs in

    let cases = Hashtbl.create 16 in
    let self : Type.datadef = { name; cases; args = List.rev targs } in
    if Hashtbl.mem m name then
      failwith "Illegal duplicate data name in same block";
    Hashtbl.add m name (cases, env);
    self) b in

  let s = List.fold_left (fun s self ->
    { s with tenv = M.add self.Type.name (Ctor self) s.tenv }) s ctors in

  List.iter (fun (n, _, cases) ->
    let (m, env) = Hashtbl.find m n in
    let s = { s with tenv = M.union (fun _ _ v -> Some v) s.tenv env } in
    List.iteri (fun i (k, args) ->
      if Hashtbl.mem m k then
        failwith "Illegal duplicate constructor in same data definition";
      let rec loop acc s = function
        | [] ->
          let s = { s with level = Type.decr_level s.level } in
          Ok (s, acc)
        | x :: xs ->
          let< (s, t) = check_texpr true s x in
          loop (t :: acc) s xs in
      let s = { s with level = Type.incr_level s.level } in
      match loop [] s args with
        | Error e -> failwith e
        | Ok (s, args) ->
          match Type.gen s.level (Type.TyTup (List.rev args)) with
            | (existentials, Type.TyTup args) ->
              Hashtbl.add m k (i, Type.RSet.elements existentials, args)
            | _ -> assert false) cases) b;

  List.iter Type.check_datadef_variance ctors;

  ctors

let check (exports, m) =
  let rec check_module s = function
    | [] ->
      let rec loop m = function
        | [] -> Ok m
        | x :: xs ->
          match M.find_opt x s.venv with
            | Some (Value (_, t)) when Type.has_free_tv t ->
              Error "Cannot export binder with free type variable"
            | Some (Value (_, t)) -> loop (M.add x t m) xs
            | _ -> Error ("Cannot export inexistent binder " ^ x) in
      loop M.empty exports
    | Ast.RExpr e :: xs ->
      let< _ = check_expr s e in
      check_module s xs
    | Ast.RLet g :: xs ->
      let< s = check_binders false s g in
      check_module s xs
    | Ast.RRec g :: xs ->
      let< s = check_binders true s g in
      check_module s xs
    | Ast.RData b :: xs -> begin
      try
        let ctors = check_data_def s b in
        let s = List.fold_left (fun s ctor ->
          { s with venv = register_ctors ctor s.venv
                 ; tenv = M.add ctor.name (Ctor ctor) s.tenv }) s ctors in
        check_module s xs
      with Failure e -> Error e
    end in

  let venv = register_ctors Type.datadef_List M.empty in
  let tenv = M.singleton "[]" (Ctor Type.datadef_List) in
  check_module { tenv; venv; level = Type.null_level } m

let rec lower_funk e id s h k =
  match e with
    | Ast.EVar n -> k id (M.find n s)

    | Ast.ETyped (e, _) -> lower_funk e id s h k

    | Ast.ELet (b, e) ->
      lower_let_binder b id s h (fun id s ->
        lower_funk e id s h k)

    | Ast.ERec (b, e) ->
      lower_rec_binder b id s h (fun id s ->
        lower_funk e id s h k)

    | Ast.ERef x ->
      lower_funk x id s h (fun id x ->
        let name = id in
        let id, tail = k (id + 1) name in
        (id, LetPack (name, [(true, x)], ref tail)))

    | Ast.EAssign (d, v) ->
      lower_funk v id s h (fun id v ->
        lower_funk d id s h (fun id d ->
          let name, id = id, id + 1 in
          let id, tail = k id name in
          (id, LetCont ([name, [], ref (LetPack (name, [], ref tail))], ref (
                Mutate (d, 0, v, name))))))

    | Ast.EDeref v ->
      lower_funk v id s h (fun id v ->
        let name, id = id, id + 1 in
        let id, tail = k id name in
        (id, LetProj (name, 0, v, ref tail)))

    | Ast.ESeq (x, xs) ->
      let rec loop id x = function
        | y :: ys -> lower_funk x id s h (fun id _ -> loop id y ys)
        | [] -> lower_funk x id s h k in
      loop id x xs

    | Ast.ETup xs ->
      let rec loop id acc = function
        | x :: xs ->
          lower_funk x id s h (fun id x -> loop id ((false, x) :: acc) xs)
        | [] ->
          let name = id in
          let id, tail = k (id + 1) name in
          (id, LetPack (name, List.rev acc, ref tail)) in
      loop id [] xs

    | Ast.ECons (ctor, { contents = info }, args) ->
      let rec loop id acc = function
        | x :: xs ->
          lower_funk x id s h (fun id x -> loop id (x :: acc) xs)
        | [] ->
          let name, id = id, id + 1 in
          let id, tail = k id name in
          let (slot, _, _) = Hashtbl.find info.cases ctor in
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
  let rec loop id s' = function
    | (n, _, ([], i) :: _) :: xs ->
      lower_funk i id s h (fun id i -> loop id (M.add n i s') xs)
    | (n, _, mat) :: xs ->
      let mat = List.map (fun (p, e) -> (p, s, e)) mat in
      lower_generalized_lambda id mat (fun id i -> loop id (M.add n i s') xs)
    | [] ->
      k id s' in
  b |> group_binders |> loop id s

and lower_rec_binder b id s h k =
  let (id, s, b) = b
    |> group_binders
    |> List.fold_left (fun (id, s, b) (n, _, mat) ->
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
    | (v :: _ as vs), Ast.PVar (n, p) :: ps ->
      is_simple_capture (M.add n v s) (vs, p :: ps)
    | vs, Ast.PTyped (p, _) :: ps ->
      is_simple_capture s (vs, p :: ps)
    | [], [] -> Some s
    | _ -> None in

  (* expands the scrutinee and the pattern matrix by a decons pattern *)
  let expand v = function
    | [] -> failwith "PATTERN MATRIX DIMENSION MISMATCH"
    | ((p, s, e) :: xs) as rows ->
      (* currently expands by the left-most decons term on the first row *)
      let rec loop vinit pinit s = function
        | v :: vs, Ast.PDeref u :: ps ->
          (* As far as the backend is concerned, this is no different from a
           * tuple pattern of a single element *)
          let start = id in
          let scrut = v in
          let xs = List.map (fun (p, s, e) ->
            let rec coiter pinit s = function
              | [], Ast.PIgn :: ps ->
                (List.rev_append pinit (Ast.PIgn :: ps), s, e)
              | [], Ast.PDeref v :: ps ->
                (List.rev_append pinit (v :: ps), s, e)
              | [], Ast.PVar (n, p) :: ps ->
                coiter pinit (M.add n v s) ([], p :: ps)
              | [], Ast.PTyped (p, _) :: ps ->
                coiter pinit s ([], p :: ps)
              | _ :: xs, p :: ps ->
                coiter (p :: pinit) s (xs, ps)
              | _ -> failwith "PATTERN MATRIX DIMENSION MISMATCH" in
            coiter [] s (vinit, p)) xs in
          let v = List.rev_append vinit (id :: vs) in
          let p = List.rev_append pinit (u :: ps) in
          let (id, term) = lower_case v (id + 1) ((p, s, e) :: xs) h k in
          (id, LetProj (start, 0, scrut, ref term))
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
                  | [], Ast.PTyped (p, _) :: ps ->
                    coiter pinit s ([], p :: ps)
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
        | v :: vs, Ast.PDecons (_, { contents = info }, _) :: _ ->
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
              | [], Ast.PTyped (p, _) :: ps ->
                coiter pinit s ([], p :: ps)
              | _ :: xs, p :: ps ->
                coiter (p :: pinit) s (xs, ps)
              | _ -> failwith "PATTERN MATRIX DIMENSION MISMATCH" in
            coiter [] s (vinit, p)) rows in

          let m =
            if Hashtbl.length partitions = Hashtbl.length info.cases then
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
                  let (slot, _, _) = Hashtbl.find info.cases ctor in
                  let args = Lazy.force fill in
                  let row = ps
                    |> List.rev_append args
                    |> List.rev_append pinit, s, e in
                  Hir.M.update (Some slot) (function
                    | None -> Some (args, [row])
                    | Some (p, xs) -> Some (p, row :: xs)) m) partitions m
              | Ast.PDecons (ctor, _, args) :: ps ->
                let (slot, _, _) = Hashtbl.find info.cases ctor in
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
        | (v :: _ as vs), Ast.PVar (n, p) :: ps ->
          loop vinit pinit (M.add n v s) (vs, p :: ps)
        | vs, Ast.PTyped (p, _) :: ps ->
          loop vinit pinit s (vs, p :: ps)
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
