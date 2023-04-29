module IdMap = Map.Make (Z)

type t =
  | TyVar of tyvar
  | TyPly of Z.t
  | TyArr of t * t
  | TyTup of t list
  | TyDat of datadef * t list

and tyvar =
  Z.t * t ref

and datadef =
  string * Z.t list * (string, int * t list) Hashtbl.t

type fvmap = t ref IdMap.t

let datadef_Void : datadef =
  ("Void", [], Hashtbl.create 0)

let new_tyvar : unit -> t =
  let fresh_id = ref Z.zero in
  fun () ->
    let rec t = TyVar (!fresh_id, ref t) in
    fresh_id := Z.succ !fresh_id;
    t

let rec unwrap_shallow : t -> t = function
  | TyVar (_, r) as t when !r != t ->
    let t = unwrap_shallow !r in
    r := t;
    t
  | t -> t

let inst (t : t) : t =
  let map = Hashtbl.create 16 in
  let rec walk t =
    match unwrap_shallow t with
      | TyVar _ as t -> t
      | TyArr (a, r) -> TyArr (walk a, walk r)
      | TyTup xs -> TyTup (List.map walk xs)
      | TyDat (k, xs) -> TyDat (k, List.map walk xs)
      | TyPly k ->
        match Hashtbl.find_opt map k with
          | Some v -> v
          | None ->
            let v = new_tyvar () in
            Hashtbl.add map k v;
            v in
  walk t

let rec subst (m : t IdMap.t) (t : t) : t =
  let t = unwrap_shallow t in
  match t with
    | _ when IdMap.is_empty m -> t
    | TyVar _ -> t
    | TyArr (a, r) -> TyArr (subst m a, subst m r)
    | TyTup xs -> TyTup (List.map (subst m) xs)
    | TyDat (k, xs) -> TyDat (k, List.map (subst m) xs)
    | TyPly id ->
      match IdMap.find_opt id m with
        | Some t -> t
        | None -> t

let rec collect_free (t : t) (m : fvmap) : fvmap =
  match unwrap_shallow t with
    | TyVar (id, r) ->
      IdMap.add id r m
    | TyPly _ ->
      m
    | TyArr (a, r) ->
      m |> collect_free a |> collect_free r
    | TyTup xs | TyDat (_, xs) ->
      List.fold_left (fun m t -> collect_free t m) m xs

let gen (mono : 'a IdMap.t) (t : t) : t =
  let map = Hashtbl.create 16 in
  let rec walk next_id t =
    match unwrap_shallow t with
      | TyPly _ -> failwith "Invalid existing poly type when generalizing"
      | TyArr (a, r) ->
        let (next_id, a) = walk next_id a in
        let (next_id, r) = walk next_id r in
        (next_id, TyArr (a, r))
      | TyTup xs ->
        let (next_id, xs) = List.fold_left (fun (next_id, acc) t ->
          let (next_id, t) = walk next_id t in
          (next_id, t :: acc)) (next_id, []) xs in
        (next_id, TyTup (List.rev xs))
      | TyDat (k, xs) ->
        let (next_id, xs) = List.fold_left (fun (next_id, acc) t ->
          let (next_id, t) = walk next_id t in
          (next_id, t :: acc)) (next_id, []) xs in
        (next_id, TyDat (k, List.rev xs))
      | TyVar (id, _) ->
        if IdMap.mem id mono then
          (* this one stays monomorphic *)
          (next_id, t)
        else
          match Hashtbl.find_opt map id with
            | Some t -> (next_id, t)
            | _ ->
              let t = TyPly next_id in
              Hashtbl.add map id t;
              (Z.succ next_id, t) in
  t |> walk Z.zero |> snd

let get_tvid (t : t) : Z.t option =
  match unwrap_shallow t with
    | TyVar (v, _) -> Some v
    | _ -> None

let tvid_occurs_id (id : Z.t) (t : t) : bool =
  let rec walk = function
    | [] -> false
    | x :: xs ->
      match unwrap_shallow x with
        | TyVar (q, _) ->
          if Z.equal q id then true else walk xs
        | TyPly _ -> walk xs
        | TyArr (p, q) -> walk (p :: q :: xs)
        | TyTup ys | TyDat (_, ys) ->
          if walk ys then true else walk xs in
  walk [t]

let rec unify_loop : (t * t) list -> unit = function
  | [] -> ()
  | (a, b) :: xs ->
    match unwrap_shallow a, unwrap_shallow b with
      | TyVar (p, r), TyVar (q, _) ->
        if not (Z.equal p q) then r := b;
        unify_loop xs

      | TyVar (p, r), t
      | t, TyVar (p, r) ->
        if tvid_occurs_id p t then failwith "Illegal infinite type construction";
        r := t;
        unify_loop xs

      | TyPly a, TyPly b when Z.equal a b ->
        unify_loop xs

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

let rec bprint (buf : Buffer.t) (t : t) : unit =
  let rec walk t =
    match unwrap_shallow t with
      | TyVar (id, _) ->
        Printf.bprintf buf "$%a" Z.bprint id
      | TyPly id ->
        Printf.bprintf buf "%a" Z.bprint id
      | TyArr (a, r) ->
        Printf.bprintf buf "(%a -> %a)" bprint a bprint r
      | TyTup [] ->
        Printf.bprintf buf "{}"
      | TyTup (x :: xs) ->
        Printf.bprintf buf "{ ";
        walk x;
        List.iter (Printf.bprintf buf ", %a" bprint) xs;
        Printf.bprintf buf " }"
      | TyDat ((k, _, _), []) ->
        Buffer.add_string buf k
      | TyDat ((k, _, _), xs) ->
        Printf.bprintf buf "(%s" k;
        List.iter (Printf.bprintf buf " %a" bprint) xs;
        Printf.bprintf buf ")" in
  walk t

let to_string (t : t) : string =
  let buf = Buffer.create 32 in
  bprint buf t;
  Buffer.contents buf
