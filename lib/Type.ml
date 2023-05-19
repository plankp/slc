module IdMap = Map.Make (Z)

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

and tname =
  Z.t * level

and level =
  Z.t

and datadef =
  string * (Z.t * variance) list * (string, int * t list) Hashtbl.t

and variance =
  | Covariant
  | Contravariant
  | Invariant

let datadef_Void : datadef =
  ("Void", [], Hashtbl.create 0)

let datadef_List : datadef =
  let m = Hashtbl.create 2 in
  let self = ("List", [Z.zero, Covariant], m) in
  let t0 = TyPly (Z.zero, Z.zero) in
  Hashtbl.add m "[]" (0, []);
  Hashtbl.add m "::" (1, [t0; (TyDat (self, [t0]))]);
  self

let null_level : level = Z.zero
let incr_level : level -> level = Z.succ
let decr_level : level -> level = Z.pred

let new_tyvar : level -> t =
  let fresh_id = ref Z.zero in
  fun level ->
    let id = !fresh_id in
    let t = TyVar (ref (Unbound (id, level))) in
    fresh_id := Z.succ id;
    t

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

let inst (level : level) (t : t) : t =
  let map = Hashtbl.create 16 in
  let rec walk = function
    | TyVar { contents = Link _ } as t -> t |> unwrap_shallow |> walk
    | TyVar _ as t -> t
    | TyRef t -> TyRef (walk t)
    | TyArr (a, r) -> TyArr (walk a, walk r)
    | TyTup xs -> TyTup (List.map walk xs)
    | TyDat (k, xs) -> TyDat (k, List.map walk xs)
    | TyPly k ->
      match Hashtbl.find_opt map k with
        | Some v -> v
        | None ->
          let v = new_tyvar level in
          Hashtbl.add map k v;
          v in
  walk t

let rec subst (m : t IdMap.t) : t -> t = function
  | t when IdMap.is_empty m -> t
  | TyVar { contents = Link _ } as t -> t |> unwrap_shallow |> subst m
  | TyVar _ as t -> t
  | TyRef t -> TyRef (subst m t)
  | TyArr (a, r) -> TyArr (subst m a, subst m r)
  | TyTup xs -> TyTup (List.map (subst m) xs)
  | TyDat (k, xs) -> TyDat (k, List.map (subst m) xs)
  | TyPly (id, _) as t -> m |> IdMap.find_opt id |> Option.value ~default:t

let rec gen (level : level) : t -> t = function
  | TyVar { contents = Link _ } as t -> t |> unwrap_shallow |> gen level
  | TyPly _ -> failwith "Invalid existing polytype when generalizing"
  | TyRef t -> TyRef (gen level t)
  | TyArr (a, r) -> TyArr (gen level a, gen level r)
  | TyTup xs -> TyTup (List.map (gen level) xs)
  | TyDat (k, xs) -> TyDat (k, List.map (gen level) xs)
  | TyVar { contents = Unbound (n, l) } as t ->
    if Z.compare l level <= 0 then t
    else TyPly (n, level)

let check_datadef_variance ((_, targs, cases) : datadef) : unit =
  let enter_variance from ctx = match from, ctx with
    | Invariant, _ | _, Invariant -> Invariant
    | _, Covariant -> from
    | Covariant, Contravariant -> Contravariant
    | Contravariant, Contravariant -> Covariant in

  let m = Hashtbl.create 16 in
  let rec walk ctx = function
    | TyVar { contents = Link _ } as t ->
      t |> unwrap_shallow |> walk ctx
    | TyPly (n, v) when Z.equal Z.zero v -> begin
      match Hashtbl.find_opt m n, ctx with
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
    | TyPly _ -> ()
    | TyRef t -> walk Invariant t
    | TyArr (a, r) ->
      walk (enter_variance ctx Contravariant) a;
      walk ctx r
    | TyTup xs ->
      List.iter (walk ctx) xs
    | TyDat ((_, params, _), xs) ->
      List.iter2 (fun (_, v) ->
        walk (enter_variance ctx v)) params xs in

  List.iter (fun (n, v) -> Hashtbl.add m n v) targs;
  Hashtbl.iter (fun _ (_, sites) ->
    List.iter (walk Covariant) sites) cases

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
  | TyDat ((_, params, _), xs) ->
    List.iter2 (function
      | (_, Covariant) -> drop_dangerous_level' l2 dangerous
      | _ -> drop_dangerous_level' l2 true) params xs

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
  let map = Hashtbl.create 32 in
  let next_id = ref Z.one in
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
    | TyDat ((k, _, _), (_ :: _ as xs)) ->
      Printf.bprintf buf "%s" k;
      List.iter (fun x -> Printf.bprintf buf " "; walk_atom x) xs;
    | TyRef t ->
      Printf.bprintf buf "ref ";
      walk_atom t
    | t -> walk_atom t
  and walk_atom = function
    | TyVar { contents = Link _ } as t ->
      t |> unwrap_shallow |> walk
    | TyVar { contents = Unbound (id, _) } ->
      Printf.bprintf buf "$%a" Z.bprint id
    | TyPly n ->
      let n = match Hashtbl.find_opt map n with
        | Some n -> n
        | None ->
          let id = !next_id in
          let name = Printf.sprintf "t%a" Z.sprint id in
          Hashtbl.add map n name;
          next_id := Z.succ id;
          name in
      Printf.bprintf buf "%s" n
    | TyTup [] ->
      Printf.bprintf buf "{}"
    | TyTup (x :: xs) ->
      Printf.bprintf buf "{ ";
      walk x;
      List.iter (fun x -> Printf.bprintf buf ", "; walk x) xs;
      Printf.bprintf buf " }"
    | TyDat ((k, _, _), []) ->
      Buffer.add_string buf k
    | t ->
      Printf.bprintf buf "(";
      walk t;
      Printf.bprintf buf ")" in
  walk t

let to_string (t : t) : string =
  let buf = Buffer.create 32 in
  bprint buf t;
  Buffer.contents buf
