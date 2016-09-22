{
  open Parser
}

let space = ' ' | '\t' | '\r'

rule token = parse
  | "coh" { COH }
  | "let" { LET }
  | "set" { SET }
  | "(" { LPAR }
  | ")" { RPAR }
  | ":" { COL }
  | "->" { ARR }
  | "=>" { ARROW }
  | "*" { OBJ }
  | "=" { EQ }
  | (['_''a'-'z''A'-'Z']['a'-'z''A'-'Z''0'-'9''_']*['\'']* as str) { IDENT str }
  | space+ { token lexbuf }
  | "#"[^'\n']* { token lexbuf }
  | "\n" { Lexing.new_line lexbuf; token lexbuf }
  | eof { EOF }
