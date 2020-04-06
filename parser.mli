type token =
  | INT of (int)
  | BOOL of (bool)
  | ID of (string)
  | EOC
  | LET
  | IN
  | EQ
  | LT
  | PLUS
  | MINUS
  | TIMES
  | DIV
  | LBRA
  | RBRA
  | SEMI
  | LPAR
  | RPAR
  | COMMA
  | CONS
  | IF
  | THEN
  | ELSE
  | MATCH
  | WITH
  | BAR
  | UNDERSCORE
  | END
  | FUN
  | REC
  | RARROW
  | AND
  | EOF

val main :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Syntax.command
