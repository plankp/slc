type prog =
  string list * root list

and root =
  | RLet of binder list
  | RRec of binder list
  | RData of datadef list
  | RExpr of expr

and datadef =
  string * string list * (string * texpr list) list

and expr =
  | EVar of string
  | ETup of expr list
  | ERef of expr
  | ECons of string * Type.datadef ref * expr list
  | EApp of expr * expr list
  | ELam of pat list * expr
  | ELamCase of (pat * expr) list
  | ELet of binder list * expr
  | ERec of binder list * expr
  | ECase of expr * (pat * expr) list
  | ETyped of expr * texpr
  | EAssign of expr * expr
  | EDeref of expr

and binder =
  | BValue of string * pat list * expr
  | BAnnot of string * texpr

and pat =
  | PIgn
  | PVar of string * pat
  | PTup of pat list
  | PDeref of pat
  | PDecons of string * Type.datadef ref * pat list
  | PTyped of pat * texpr

and texpr =
  | TEVar of string
  | TETup of texpr list
  | TERef of texpr
  | TECons of string * texpr list
  | TEArr of texpr * texpr
