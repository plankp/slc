%{
open Ast
%}

%token LPAREN RPAREN COMMA
%token LSQUARE RSQUARE
%token SLASH ARROW
%token LET REC SET IN
%token CASE OF IGNORE BIND
%token <string> IDENT
%token EOF

%start <expr option> prog

%%

prog:
  | EOF { None }
  | e = expr; EOF { Some e }

expr:
  | SLASH p = pattern+ ARROW e = expr { ELam (p, e) }
  | SLASH CASE k = cases { ELamCase k }
  | LET b = binders IN e = expr { ELet (b, e) }
  | REC b = binders IN e = expr { ERec (b, e) }
  | CASE e = expr OF k = cases { ECase (e, k) }
  | e = expr_app { e }

binders:
  | x = binder; COMMA; xs = binders { x :: xs }
  | x = binder { [x] }

binder:
  | n = IDENT SET i = expr { (n, i) }

cases:
  | x = case; COMMA; xs = cases { x :: xs }
  | x = case { [x] }

case:
  | p = pattern ARROW e = expr { (p, e) }

pattern:
  | LPAREN; e = pattern; RPAREN { e }
  | LSQUARE; e = patterns; RSQUARE { PTup e }
  | IGNORE { PIgn }
  | n = IDENT { PVar (n, PIgn) }
  | n = IDENT; BIND; p = pattern { PVar (n, p) }

patterns:
  | x = pattern; COMMA; xs = patterns { x :: xs }
  | x = pattern { [x] }
  | { [] }

expr_app:
  | f = expr_atom; a = expr_atom+ { EApp (f, a) }
  | e = expr_atom { e }

expr_atom:
  | LPAREN; e = expr; RPAREN { e }
  | LSQUARE; e = exprs; RSQUARE { ETup e }
  | e = IDENT { EVar e }

exprs:
  | x = expr; COMMA; xs = exprs { x :: xs }
  | x = expr { [x] }
  | { [] }
