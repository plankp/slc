{
open Parser
}

let newline = '\n' | '\r' | "\r\n"
let lname = ['a'-'z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*
let uname = ['A'-'Z'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*

rule read = parse
  | '#' [^ '\n' '\r']* { read lexbuf }

  | ' ' | '\t' { read lexbuf }
  | newline { Lexing.new_line lexbuf; read lexbuf }

  | '('       { LPAREN }
  | ')'       { RPAREN }
  | '['       { LSQUARE }
  | ']'       { RSQUARE }
  | '{'       { LCURLY }
  | '}'       { RCURLY }
  | '_'       { IGNORE }
  | '@'       { BIND }
  | '\\'      { SLASH }
  | "->"      { ARROW }
  | ":="      { ST }
  | '^'       { LD }
  | '+'       { ADD }
  | '-'       { SUB }
  | "::"      { CONS }
  | ':'       { COLON }
  | '='       { SET }
  | '|'       { BAR }
  | ','       { COMMA }
  | ';'       { SEMI }
  | '.'       { DOT }
  | "let"     { LET }
  | "rec"     { REC }
  | "and"     { AND }
  | "in"      { IN }
  | "case"    { CASE }
  | "data"    { DATA }
  | "export"  { EXPORT }
  | "ref"     { REF }

  | lname     { LNAME (Lexing.lexeme lexbuf) }
  | uname     { UNAME (Lexing.lexeme lexbuf) }

  | eof { EOF }
