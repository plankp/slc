%{
open Ast
%}

%token LPAREN RPAREN COMMA
%token LSQUARE RSQUARE CONS
%token LCURLY RCURLY
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
  | e = expr_cons { e }

expr_cons:
  | hd = expr_app; CONS; tl = expr_cons {
    ECons ("::", ref Type.datadef_Void, [hd; tl])
  }
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
  | hd = pattern_atom; CONS; tl = pattern {
    PDecons ("::", ref Type.datadef_Void, [hd; tl])
  }
  | p = pattern_atom { p }

pattern_atom:
  | LPAREN; e = pattern; RPAREN { e }
  | LCURLY; e = patterns; RCURLY { PTup e }
  | LSQUARE; e = patterns; RSQUARE {
    let tl = PDecons ("[]", ref Type.datadef_Void, []) in
    List.fold_right (fun hd tl ->
      PDecons ("::", ref Type.datadef_Void, [hd; tl])) e tl
  }
  | IGNORE { PIgn }
  | n = IDENT { PVar (n, PIgn) }
  | n = IDENT; BIND; p = pattern_atom { PVar (n, p) }

patterns:
  | x = pattern; COMMA; xs = patterns { x :: xs }
  | x = pattern { [x] }
  | { [] }

expr_app:
  | f = expr_atom; a = expr_atom+ { EApp (f, a) }
  | e = expr_atom { e }

expr_atom:
  | LPAREN; e = expr; RPAREN { e }
  | LCURLY; e = exprs; RCURLY { ETup e }
  | LSQUARE; e = exprs; RSQUARE {
    let tl = ECons ("[]", ref Type.datadef_Void, []) in
    List.fold_right (fun hd tl ->
      ECons ("::", ref Type.datadef_Void, [hd; tl])) e tl
  }
  | e = IDENT { EVar e }

exprs:
  | x = expr; COMMA; xs = exprs { x :: xs }
  | x = expr { [x] }
  | { [] }
