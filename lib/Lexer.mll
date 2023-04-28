{
open Parser
}

let newline = '\n' | '\r' | "\r\n"
let ident = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*

rule read = parse
  | '#' [^ '\n' '\r']* { read lexbuf }

  | ' ' | '\t' { read lexbuf }
  | newline { Lexing.new_line lexbuf; read lexbuf }

  | '('     { LPAREN }
  | ')'     { RPAREN }
  | '['     { LSQUARE }
  | ']'     { RSQUARE }
  | '_'     { IGNORE }
  | '@'     { BIND }
  | '\\'    { SLASH }
  | "->"    { ARROW }
  | '='     { SET }
  | ','     { COMMA }
  | "let"   { LET }
  | "rec"   { REC }
  | "in"    { IN }
  | "case"  { CASE }
  | "of"    { OF }

  | ident { IDENT (Lexing.lexeme lexbuf) }

  | eof { EOF }
