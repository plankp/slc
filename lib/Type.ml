type level = Z.t
type tname = Z.t * level

module TName = struct
  type t = tname
  let compare = compare
end

module RMap = Map.Make (TName)
module RSet = Set.Make (TName)

type variance =
  | Covariant
  | Contravariant
  | Invariant

type t =
  | TyVar of tyvar ref
  | TyPly of tname
  | TyArr of t * t
  | TyTup of t list
  | TyDat of datadef * t list
  | TyRef of t

and tyvar =
  | Unbound of tname
  | Link of t

and datadef =
  (* each case holds a tname list for existentials *)
  { name  : string
  ; args  : (tname * variance) list
  ; cases : (string, int * tname list * t list) Hashtbl.t
  }

(* data Void = .  <-- impossible type in surface syntax *)
let datadef_Void : datadef =
  { name = "Void"
  ; args = []
  ; cases = Hashtbl.create 0
  }

(* data List +a = [] | (::) a (List a)  <-- corresponds to [a] *)
let datadef_List : datadef =
  let cases = Hashtbl.create 2 in
  let t0 = (Z.zero, Z.zero) in
  let self = { name = "List"; args = [t0, Covariant]; cases } in
  Hashtbl.add cases "[]" (0, [], []);
  Hashtbl.add cases "::" (1, [], [TyPly t0; (TyDat (self, [TyPly t0]))]);
  self

let null_level : level = Z.zero
let incr_level : level -> level = Z.succ
let decr_level : level -> level = Z.pred

let fresh_id : unit -> Z.t =
  let counter = ref Z.zero in
  fun () ->
    let id = !counter in
    counter := Z.succ id;
    id

let new_tyvar (l : level) : t =
  TyVar (ref (Unbound (fresh_id (), l)))

let new_poly (l : level) : t =
  TyPly (fresh_id (), l)

let rec unwrap_shallow : t -> t = function
  | TyVar ({ contents = Link t } as r) ->
    let t = unwrap_shallow t in
    r := Link t;
    t
  | t -> t

let rec has_free_tv : t -> bool = function
  | TyVar { contents = Link _ } as t -> t |> unwrap_shallow |> has_free_tv
  | TyVar _ -> true
  | TyPly _ -> false
  | TyRef t -> has_free_tv t
  | TyArr (a, r) -> if has_free_tv a then true else has_free_tv r
  | TyTup xs | TyDat (_, xs) -> List.exists has_free_tv xs

let rec subst (m : t RMap.t) : t -> t = function
  | t when RMap.is_empty m -> t
  | TyVar { contents = Link _ } as t -> t |> unwrap_shallow |> subst m
  | TyVar _ as t -> t
  | TyRef t -> TyRef (subst m t)
  | TyArr (a, r) -> TyArr (subst m a, subst m r)
  | TyTup xs -> TyTup (List.map (subst m) xs)
  | TyDat (k, xs) -> TyDat (k, List.map (subst m) xs)
  | TyPly n as t -> m |> RMap.find_opt n |> Option.value ~default:t

let inst (s : RSet.t) (level : level) (t : t) : t =
  let m = RSet.fold (fun n ->
    RMap.add n (new_tyvar level)) s RMap.empty in
  subst m t

let gen (level : level) (t : t) : RSet.t * t =
  (* alias, we are faced with accidental name shadowing.
   * here, we do two traversals:
   * 1.  collect problematic names and checks if generalization happens
   * 2.  rewrite the term (if generalization is needed) *)
  let rec collect (f, v) = function
    | TyVar { contents = Link _ } as t ->
      t |> unwrap_shallow |> collect (f, v)
    | TyVar { contents = Unbound (_, l) } ->
      (f || Z.compare l level > 0, v)
    | TyPly (n, l) ->
      (f, if l = level then Z.max n v else v)
    | TyRef t -> collect (f, v) t
    | TyArr (a, r) -> collect (collect (f, v) a) r
    | TyTup xs | TyDat (_, xs) -> List.fold_left collect (f, v) xs in

  let rec rewrite id env s = function
    | TyVar { contents = Link _ } as t ->
      t |> unwrap_shallow |> rewrite id env s
    | TyVar { contents = Unbound ((_, l) as key) } as t ->
      if Z.compare l level <= 0 then (t, id, env, s)
      else begin
        match RMap.find_opt key env with
          | Some t -> (t, id, env, s)
          | None ->
            let id = Z.succ id in
            let info = (id, level) in
            let t = TyPly info in
            (t, id, RMap.add key t env, RSet.add info s)
      end
    | TyPly _ as t -> (t, id, env, s)
    | TyRef t ->
      let (t, id, env, s) = rewrite id env s t in
      (TyRef t, id, env, s)
    | TyArr (a, r) ->
      let (a, id, env, s) = rewrite id env s a in
      let (r, id, env, s) = rewrite id env s r in
      (TyArr (a, r), id, env, s)
    | TyTup xs ->
      let (xs, id, env, s) = rewrite_many [] id env s xs in
      (TyTup xs, id, env, s)
    | TyDat (k, xs) ->
      let (xs, id, env, s) = rewrite_many [] id env s xs in
      (TyDat (k, xs), id, env, s)

  and rewrite_many acc id env s = function
    | [] -> (List.rev acc, id, env, s)
    | x :: xs ->
      let (x, id, env, s) = rewrite id env s x in
      rewrite_many (x :: acc) id env s xs in

  let (needs_gen, id) = collect (false, Z.zero) t in
  if not needs_gen then (RSet.empty, t)
  else
    let (t, _, _, s) = rewrite id RMap.empty RSet.empty t in
    (s, t)

let check_datadef_variance (decl : datadef) : unit =
  let enter_variance from ctx = match from, ctx with
    | Invariant, _ | _, Invariant -> Invariant
    | _, Covariant -> from
    | Covariant, Contravariant -> Contravariant
    | Contravariant, Contravariant -> Covariant in

  let m = Hashtbl.create 16 in
  let rec walk ctx = function
    | TyVar { contents = Link _ } as t ->
      t |> unwrap_shallow |> walk ctx
    | TyPly key -> begin
      match Hashtbl.find_opt m key, ctx with
        | None, _
        | Some Invariant, _
        | Some Covariant, Covariant
        | Some Contravariant, Contravariant -> ()
        | Some _, Invariant ->
          failwith "Usage requires invariant"
        | Some _, Contravariant ->
          failwith "Usage requires contravariant"
        | Some _, Covariant ->
          failwith "Usage requires covariant"
    end
    | TyVar _ -> ()
    | TyRef t -> walk Invariant t
    | TyArr (a, r) ->
      walk (enter_variance ctx Contravariant) a;
      walk ctx r
    | TyTup xs ->
      List.iter (walk ctx) xs
    | TyDat ({ args; _ }, xs) ->
      List.iter2 (fun (_, v) ->
        walk (enter_variance ctx v)) args xs in

  List.iter (fun (n, v) -> Hashtbl.add m n v) decl.args;
  Hashtbl.iter (fun _ (_, _, sites) ->
    List.iter (walk Covariant) sites) decl.cases

let rec drop_dangerous_level' (l2 : level) (dangerous : bool) : t -> unit = function
  | TyVar { contents = Link _ } as t ->
    t |> unwrap_shallow |> drop_dangerous_level' l2 dangerous
  | TyVar ({ contents = Unbound (n, l1) } as r) ->
    if dangerous && Z.compare l2 l1 < 0 then
      r := Unbound (n, l2)
  | TyPly _ -> ()
  | TyRef t ->
    drop_dangerous_level' l2 true t
  | TyArr (p, q) ->
    drop_dangerous_level' l2 true p;
    drop_dangerous_level' l2 dangerous q
  | TyTup xs ->
    List.iter (drop_dangerous_level' l2 dangerous) xs
  | TyDat ({ args; _ }, xs) ->
    List.iter2 (function
      | (_, Covariant) -> drop_dangerous_level' l2 dangerous
      | _ -> drop_dangerous_level' l2 true) args xs

let drop_dangerous_level (l2 : level) (t : t) : unit =
  drop_dangerous_level' l2 false t

let rec occurs_unify (cell : tyvar ref) (l2 : level) : t -> unit = function
  | TyVar { contents = Link _ } as t ->
    t |> unwrap_shallow |> occurs_unify cell l2
  | TyVar ({ contents = Unbound (n, l1) } as r) ->
    if r == cell then
      failwith "Illegal infinite type construction";
    (* keep the lower level *)
    r := Unbound (n, Z.min l1 l2)
  | TyPly (_, l1) ->
    if Z.compare l1 l2 >= 0 then
      failwith "Unification cause rigid type variable to escape its scope"
  | TyRef t ->
    occurs_unify cell l2 t
  | TyArr (p, q) ->
    occurs_unify cell l2 p;
    occurs_unify cell l2 q
  | TyTup xs | TyDat (_, xs) ->
    List.iter (occurs_unify cell l2) xs

let rec unify_loop : (t * t) list -> unit = function
  | [] -> ()
  | (a, b) :: xs ->
    match a, b with
      | _ when a == b ->
        unify_loop xs

      | TyVar { contents = Link _ }, _
      | _, TyVar { contents = Link _ } ->
        unify_loop ((unwrap_shallow a, unwrap_shallow b) :: xs)

      | TyVar ({ contents = Unbound (_, l1) } as r1),
        TyVar ({ contents = Unbound (_, l2) } as r2) ->
        if r1 != r2 then begin
          (* we want to keep the one with the lower level *)
          if Z.compare l1 l2 < 0 then r2 := Link a
          else r1 := Link b
        end;
        unify_loop xs

      | TyVar ({ contents = Unbound (_, l)} as r), t
      | t, TyVar ({ contents = Unbound (_, l)} as r) ->
        occurs_unify r l t;
        r := Link t;
        unify_loop xs

      | TyPly a, TyPly b when a = b ->
        unify_loop xs

      | TyRef a, TyRef b ->
        unify_loop ((a, b) :: xs)

      | TyArr (a1, r1), TyArr (a2, r2) ->
        unify_loop ((a1, a2) :: (r1, r2) :: xs)

      | TyTup e1, TyTup e2 ->
        loop_tail xs e1 e2

      | TyDat (k1, e1), TyDat (k2, e2) when k1 == k2 ->
        loop_tail xs e1 e2

      | _ -> failwith "Impossible type unification"

and loop_tail acc x y =
  let rec loop acc = function
    | [], [] -> unify_loop acc
    | x :: xs, y :: ys -> loop ((x, y) :: acc) (xs, ys)
    | _ -> failwith "Impossible type unification" in
  loop acc (x, y)

let unify (a : t) (b : t) : unit =
  unify_loop [a, b]

let bprint (buf : Buffer.t) (t : t) : unit =
  let rec walk = function
    | TyVar { contents = Link _ } as t ->
      t |> unwrap_shallow |> walk
    | TyArr (a, r) ->
      walk_app a;
      Printf.bprintf buf " -> ";
      walk r
    | t -> walk_app t
  and walk_app = function
    | TyVar { contents = Link _ } as t ->
      t |> unwrap_shallow |> walk_app
    | TyDat ({ name; _ }, (_ :: _ as xs)) ->
      Printf.bprintf buf "%s" name;
      List.iter (fun x -> Printf.bprintf buf " "; walk_atom x) xs;
    | TyRef t ->
      Printf.bprintf buf "ref ";
      walk_atom t
    | t -> walk_atom t
  and walk_atom = function
    | TyVar { contents = Link _ } as t ->
      t |> unwrap_shallow |> walk_atom
    | TyVar { contents = Unbound (id, _) } ->
      Printf.bprintf buf "$%a" Z.bprint id
    | TyPly (n, l) when Z.zero = l ->
      Printf.bprintf buf "t%a" Z.bprint n
    | TyPly (n, l) ->
      Printf.bprintf buf "t%a_%a" Z.bprint n Z.bprint l
    | TyTup [] ->
      Printf.bprintf buf "{}"
    | TyTup (x :: xs) ->
      Printf.bprintf buf "{ ";
      walk x;
      List.iter (fun x -> Printf.bprintf buf ", "; walk x) xs;
      Printf.bprintf buf " }"
    | TyDat ({ name; _ }, []) ->
      Buffer.add_string buf name
    | t ->
      Printf.bprintf buf "(";
      walk t;
      Printf.bprintf buf ")" in
  walk t

let to_string (t : t) : string =
  let buf = Buffer.create 32 in
  bprint buf t;
  Buffer.contents buf
