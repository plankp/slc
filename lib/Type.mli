type level
type tname = Z.t * level

module RMap : Map.S with type key = tname
module RSet : Set.S with type elt = tname

type variance =
  | Covariant
  | Contravariant
  | Invariant

type tyvar
type t =
  | TyVar of tyvar ref
  | TyPly of tname
  | TyArr of t * t
  | TyTup of t list
  | TyDat of datadef * t list
  | TyRef of t

and datadef =
  (* each case holds a tname list for existentials *)
  { name  : string
  ; args  : (tname * variance) list
  ; cases : (string, int * tname list * t list) Hashtbl.t
  }

val datadef_Void : datadef
val datadef_List : datadef

val null_level : level
val incr_level : level -> level
val decr_level : level -> level

val new_tyvar : level -> t
val new_poly : level -> t

val unwrap_shallow : t -> t

val has_free_tv : t -> bool

val subst : t RMap.t -> t -> t

val inst : RSet.t -> level -> t -> t

val gen : level -> t -> (RSet.t * t)

val check_datadef_variance : datadef -> unit

val drop_dangerous_level : level -> t -> unit

val unify : t -> t -> unit

val bprint : Buffer.t -> t -> unit
val to_string : t -> string
