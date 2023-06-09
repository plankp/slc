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
%token CASE IGNORE BIND
%token COLON
%token DOT
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
  | x = LNAME COMMA xs = names { GVar x :: xs }
  | x = UNAME COMMA xs = names { GData x :: xs }
  | x = LNAME { [GVar x] }
  | x = UNAME { [GData x] }

root:
  | DATA b = datadefs xs = root { RData b :: xs }
  | LET b = binders xs = root { RLet b :: xs }
  | REC b = binders xs = root { RRec b :: xs }
  | LET IGNORE SET e = expr xs = root { RExpr e :: xs }
  | EOF { [] }

datadefs:
  | x = datadef AND xs = datadefs { x :: xs }
  | x = datadef { [x] }

datadef:
  | n = UNAME a = datapoly* SET BAR? xs = data_entries { (n, a, xs) }

datapoly:
  | ADD a = LNAME { (Some true, a) }
  | SUB a = LNAME { (Some false, a) }
  | a = LNAME { (None, a) }

data_entries:
  | x = data_entry BAR xs = data_entries { x :: xs }
  | x = data_entry { [x] }

data_entry:
  | n = UNAME a = texpr_atom* { (n, a) }

texpr:
  | a = texpr_app ARROW r = texpr { TEArr (a, r) }
  | e = texpr_app { e }

texpr_app:
  | REF a = texpr_atom { TERef a }
  | k = UNAME a = texpr_atom+ { TECons (None, k, a) }
  | m = UNAME DOT k = UNAME a = texpr_atom+ { TECons (Some m, k, a) }
  | e = texpr_atom { e }

texpr_atom:
  | LPAREN e = texpr RPAREN { e }
  | LCURLY e = texprs RCURLY { TETup e }
  | LSQUARE e = texpr RSQUARE { TECons (None, "[]", [e]) }
  | n = LNAME { TEVar n }
  | n = UNAME { TECons (None, n, []) }
  | m = UNAME DOT n = UNAME { TECons (Some m, n, []) }

texprs:
  | x = texpr COMMA xs = texprs { x :: xs }
  | x = texpr { [x] }
  | { [] }

expr:
  | SLASH p = pattern+ ARROW e = expr { ELam (p, e) }
  | SLASH CASE LCURLY k = cases RCURLY { ELamCase k }
  | LET b = binders IN e = expr { ELet (b, e) }
  | REC b = binders IN e = expr { ERec (b, e) }
  | e = expr_cons CASE LCURLY k = cases RCURLY { ECase (e, k) }
  | e = expr_cons COLON t = texpr { ETyped (e, t) }
  | l = expr_cons ST r = expr { EAssign (l, r) }
  | e = expr_cons { e }

expr_cons:
  | hd = expr_app CONS tl = expr_cons {
    ECons (None, "::", ref Type.datadef_Void, [hd; tl])
  }
  | e = expr_app { e }

binders:
  | x = binder AND xs = binders { x :: xs }
  | x = binder { [x] }

binder:
  | n = LNAME p = pattern_atom* SET i = expr { BValue (n, p, i) }
  | n = LNAME COLON t = texpr { BAnnot (n, t) }

cases:
  | x = case SEMI xs = cases { x :: xs }
  | x = case SEMI? { [x] }

case:
  | p = pattern ARROW e = expr { (p, e) }

pattern:
  | e = pattern_cons COLON t = texpr { PTyped (e, t) }
  | e = pattern_cons { e }

pattern_cons:
  | hd = pattern_app CONS tl = pattern {
    PDecons (None, "::", ref Type.datadef_Void, [hd; tl])
  }
  | p = pattern_app { p }

pattern_app:
  | REF a = pattern_atom { PDeref a }
  | k = UNAME a = pattern_atom+ {
    PDecons (None, k, ref Type.datadef_Void, a)
  }
  | m = UNAME DOT k = UNAME a = pattern_atom+ {
    PDecons (Some m, k, ref Type.datadef_Void, a)
  }
  | e = pattern_atom { e }

pattern_atom:
  | LPAREN e = pattern RPAREN { e }
  | LCURLY e = patterns RCURLY { PTup e }
  | LSQUARE e = patterns RSQUARE {
    let tl = PDecons (None, "[]", ref Type.datadef_Void, []) in
    List.fold_right (fun hd tl ->
      PDecons (None, "::", ref Type.datadef_Void, [hd; tl])) e tl
  }
  | IGNORE { PIgn }
  | n = UNAME { PDecons (None, n, ref Type.datadef_Void, []) }
  | n = LNAME { PVar (n, PIgn) }
  | m = UNAME DOT n = UNAME { PDecons (Some m, n, ref Type.datadef_Void, []) }
  | n = LNAME BIND p = pattern_atom { PVar (n, p) }

patterns:
  | x = pattern COMMA xs = patterns { x :: xs }
  | x = pattern { [x] }
  | { [] }

expr_app:
  | REF a = expr_atom { ERef a }
  | k = UNAME a = expr_atom+ { ECons (None, k, ref Type.datadef_Void, a) }
  | m = UNAME DOT k = UNAME a = expr_atom+ {
    ECons (Some m, k, ref Type.datadef_Void, a)
  }
  | f = expr_atom a = expr_atom+ { EApp (f, a) }
  | e = expr_atom { e }

expr_atom:
  | LPAREN e = exprs_semi RPAREN { ESeq e }
  | LCURLY e = exprs RCURLY { ETup e }
  | LSQUARE e = exprs RSQUARE {
    let tl = ECons (None, "[]", ref Type.datadef_Void, []) in
    List.fold_right (fun hd tl ->
      ECons (None, "::", ref Type.datadef_Void, [hd; tl])) e tl
  }
  | n = UNAME { ECons (None, n, ref Type.datadef_Void, []) }
  | e = LNAME { EVar (None, e) }
  | m = UNAME DOT n = UNAME { ECons (Some m, n, ref Type.datadef_Void, []) }
  | m = UNAME DOT n = LNAME { EVar (Some m, n) }
  | e = expr_atom LD { EDeref e }

exprs:
  | x = expr COMMA xs = exprs { x :: xs }
  | x = expr { [x] }
  | { [] }

exprs_semi:
  | x = expr SEMI xs = exprs_semi { NonEmpty.cons x xs }
  | x = expr SEMI? { NonEmpty.singleton x }
