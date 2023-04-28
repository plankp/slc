type expr =
  | EVar of string
  | ETup of expr list
  | EApp of expr * expr list
  | ELam of pat list * expr
  | ELamCase of (pat * expr) list
  | ELet of (string * expr) list * expr
  | ERec of (string * expr) list * expr
  | ECase of expr * (pat * expr) list

and pat =
  | PIgn
  | PVar of string * pat
  | PTup of pat list
