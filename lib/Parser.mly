%{
open Ast
%}

%token LPAREN RPAREN COMMA SEMI
%token LSQUARE RSQUARE CONS
%token LCURLY RCURLY
%token SLASH ARROW
%token DATA BAR
%token REF ST LD
%token ADD SUB
%token LET REC SET IN AND
%token CASE OF IGNORE BIND
%token COLON
%token EXPORT
%token <string> LNAME UNAME
%token EOF

%start <prog> prog

%%

prog:
  | e = exportdef r = root { (e, r) }
  | r = root { ([], r) }

exportdef:
  | EXPORT n = names { n }

names:
  | x = LNAME COMMA xs = names { x :: xs }
  | x = LNAME { [x] }

root:
  | DATA; b = datadefs; xs = root { RData b :: xs }
  | LET; b = binders; xs = root { RLet b :: xs }
  | REC; b = binders; xs = root { RRec b :: xs }
  | LET; IGNORE; SET; e = expr; xs = root { RExpr e :: xs }
  | EOF { [] }

datadefs:
  | x = datadef; AND; xs = datadefs { x :: xs }
  | x = datadef { [x] }

datadef:
  | n = UNAME; a = datapoly*; SET; BAR?; xs = data_entries { (n, a, xs) }

datapoly:
  | ADD a = LNAME { (Some true, a) }
  | SUB a = LNAME { (Some false, a) }
  | a = LNAME { (None, a) }

data_entries:
  | x = data_entry; BAR; xs = data_entries { x :: xs }
  | x = data_entry { [x] }

data_entry:
  | n = UNAME; a = texpr_atom* { (n, a) }

texpr:
  | a = texpr_app; ARROW; r = texpr { TEArr (a, r) }
  | e = texpr_app { e }

texpr_app:
  | REF a = texpr_atom { TERef a }
  | k = UNAME a = texpr_atom+ { TECons (k, a) }
  | e = texpr_atom { e }

texpr_atom:
  | LPAREN; e = texpr; RPAREN { e }
  | LCURLY; e = texprs; RCURLY { TETup e }
  | LSQUARE; e = texpr; RSQUARE { TECons ("[]", [e]) }
  | n = LNAME { TEVar n }
  | n = UNAME { TECons (n, []) }

texprs:
  | x = texpr; COMMA; xs = texprs { x :: xs }
  | x = texpr { [x] }
  | { [] }

expr:
  | SLASH p = pattern+ ARROW e = expr { ELam (p, e) }
  | SLASH CASE k = cases { ELamCase k }
  | LET b = binders IN e = expr { ELet (b, e) }
  | REC b = binders IN e = expr { ERec (b, e) }
  | CASE e = expr OF k = cases { ECase (e, k) }
  | e = expr_cons COLON t = texpr { ETyped (e, t) }
  | l = expr_cons ST r = expr { EAssign (l, r) }
  | e = expr_cons { e }

expr_cons:
  | hd = expr_app; CONS; tl = expr_cons {
    ECons ("::", ref Type.datadef_Void, [hd; tl])
  }
  | e = expr_app { e }

binders:
  | x = binder; AND; xs = binders { x :: xs }
  | x = binder { [x] }

binder:
  | n = LNAME p = pattern* SET i = expr { BValue (n, p, i) }
  | n = LNAME COLON t = texpr { BAnnot (n, t) }

cases:
  | x = case; COMMA; xs = cases { x :: xs }
  | x = case { [x] }

case:
  | p = pattern ARROW e = expr { (p, e) }

pattern:
  | e = pattern_cons COLON t = texpr { PTyped (e, t) }
  | e = pattern_cons { e }

pattern_cons:
  | hd = pattern_app; CONS; tl = pattern {
    PDecons ("::", ref Type.datadef_Void, [hd; tl])
  }
  | p = pattern_app { p }

pattern_app:
  | REF a = pattern_atom { PDeref a }
  | k = UNAME; a = pattern_atom+ { PDecons (k, ref Type.datadef_Void, a) }
  | e = pattern_atom { e }

pattern_atom:
  | LPAREN e = pattern RPAREN { e }
  | LCURLY e = patterns RCURLY { PTup e }
  | LSQUARE e = patterns RSQUARE {
    let tl = PDecons ("[]", ref Type.datadef_Void, []) in
    List.fold_right (fun hd tl ->
      PDecons ("::", ref Type.datadef_Void, [hd; tl])) e tl
  }
  | IGNORE { PIgn }
  | n = UNAME { PDecons (n, ref Type.datadef_Void, []) }
  | n = LNAME { PVar (n, PIgn) }
  | n = LNAME; BIND; p = pattern_atom { PVar (n, p) }

patterns:
  | x = pattern; COMMA; xs = patterns { x :: xs }
  | x = pattern { [x] }
  | { [] }

expr_app:
  | REF a = expr_atom { ERef a }
  | k = UNAME; a = expr_atom+ { ECons (k, ref Type.datadef_Void, a) }
  | f = expr_atom; a = expr_atom+ { EApp (f, a) }
  | e = expr_atom { e }

expr_atom:
  | LPAREN e = exprs_semi RPAREN { ESeq e }
  | LCURLY e = exprs RCURLY { ETup e }
  | LSQUARE e = exprs RSQUARE {
    let tl = ECons ("[]", ref Type.datadef_Void, []) in
    List.fold_right (fun hd tl ->
      ECons ("::", ref Type.datadef_Void, [hd; tl])) e tl
  }
  | n = UNAME { ECons (n, ref Type.datadef_Void, []) }
  | e = LNAME { EVar e }
  | e = expr_atom LD { EDeref e }

exprs:
  | x = expr; COMMA; xs = exprs { x :: xs }
  | x = expr { [x] }
  | { [] }

exprs_semi:
  | x = expr SEMI xs = exprs_semi { NonEmpty.cons x xs }
  | x = expr SEMI { NonEmpty.singleton x }
  | x = expr { NonEmpty.singleton x }
