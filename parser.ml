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

open Parsing;;
let _ = parse_error;;
# 2 "parser.mly"
open Syntax
  (* ここに書いたものは，ExampleParser.mliに入らないので注意 *)
# 41 "parser.ml"
let yytransl_const = [|
  260 (* EOC *);
  261 (* LET *);
  262 (* IN *);
  263 (* EQ *);
  264 (* LT *);
  265 (* PLUS *);
  266 (* MINUS *);
  267 (* TIMES *);
  268 (* DIV *);
  269 (* LBRA *);
  270 (* RBRA *);
  271 (* SEMI *);
  272 (* LPAR *);
  273 (* RPAR *);
  274 (* COMMA *);
  275 (* CONS *);
  276 (* IF *);
  277 (* THEN *);
  278 (* ELSE *);
  279 (* MATCH *);
  280 (* WITH *);
  281 (* BAR *);
  282 (* UNDERSCORE *);
  283 (* END *);
  284 (* FUN *);
  285 (* REC *);
  286 (* RARROW *);
  287 (* AND *);
    0 (* EOF *);
    0|]

let yytransl_block = [|
  257 (* INT *);
  258 (* BOOL *);
  259 (* ID *);
    0|]

let yylhs = "\255\255\
\001\000\001\000\001\000\002\000\002\000\002\000\002\000\002\000\
\007\000\007\000\006\000\006\000\004\000\004\000\004\000\004\000\
\004\000\004\000\004\000\008\000\008\000\003\000\003\000\003\000\
\003\000\003\000\003\000\003\000\003\000\003\000\010\000\010\000\
\011\000\011\000\009\000\009\000\009\000\013\000\013\000\012\000\
\012\000\012\000\014\000\014\000\014\000\015\000\015\000\016\000\
\016\000\016\000\016\000\016\000\016\000\016\000\017\000\017\000\
\018\000\018\000\005\000\000\000"

let yylen = "\002\000\
\002\000\002\000\001\000\004\000\006\000\005\000\008\000\001\000\
\006\000\004\000\002\000\003\000\006\000\004\000\008\000\007\000\
\006\000\005\000\001\000\005\000\003\000\001\000\001\000\001\000\
\001\000\003\000\003\000\002\000\003\000\003\000\003\000\003\000\
\001\000\003\000\003\000\003\000\001\000\003\000\001\000\003\000\
\003\000\001\000\003\000\003\000\001\000\002\000\001\000\001\000\
\001\000\001\000\003\000\002\000\003\000\003\000\003\000\003\000\
\003\000\001\000\001\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\048\000\049\000\050\000\000\000\000\000\000\000\
\000\000\000\000\000\000\003\000\060\000\000\000\008\000\000\000\
\000\000\037\000\000\000\000\000\047\000\022\000\023\000\059\000\
\000\000\000\000\025\000\000\000\000\000\024\000\000\000\052\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\
\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\046\000\028\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\053\000\054\000\000\000\051\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\038\000\
\000\000\000\000\000\000\029\000\030\000\000\000\026\000\000\000\
\000\000\000\000\000\000\000\000\057\000\000\000\056\000\000\000\
\000\000\000\000\014\000\034\000\000\000\032\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\018\000\000\000\
\000\000\011\000\000\000\013\000\000\000\000\000\017\000\000\000\
\000\000\000\000\012\000\016\000\000\000\000\000\015\000\000\000\
\007\000\020\000\000\000\000\000\000\000\000\000\009\000"

let yydgoto = "\002\000\
\013\000\014\000\051\000\033\000\030\000\097\000\121\000\090\000\
\016\000\054\000\052\000\017\000\018\000\019\000\020\000\021\000\
\036\000\034\000"

let yysindex = "\018\000\
\246\000\000\000\000\000\000\000\000\000\013\255\119\255\135\255\
\135\255\135\255\035\255\000\000\000\000\002\000\000\000\070\255\
\026\255\000\000\087\255\163\255\000\000\000\000\000\000\000\000\
\143\255\069\255\000\000\035\255\005\255\000\000\031\255\000\000\
\010\255\060\255\092\255\032\255\063\255\057\255\056\255\000\000\
\000\000\163\255\163\255\163\255\163\255\163\255\163\255\163\255\
\000\000\000\000\022\255\079\255\050\255\085\255\035\255\135\255\
\069\255\035\255\011\255\135\255\000\000\000\000\135\255\000\000\
\135\255\069\255\135\255\107\255\107\255\087\255\087\255\000\000\
\163\255\163\255\069\255\000\000\000\000\069\255\000\000\043\255\
\090\255\095\255\035\255\135\255\000\000\093\255\000\000\096\255\
\248\254\098\255\000\000\000\000\108\255\000\000\135\255\049\255\
\124\255\135\255\058\255\090\255\135\255\135\255\000\000\000\255\
\135\255\000\000\135\255\000\000\135\255\124\255\000\000\109\255\
\135\255\035\255\000\000\000\000\137\255\069\255\000\000\035\255\
\000\000\000\000\134\255\135\255\121\255\035\255\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\219\000\
\153\000\000\000\079\000\001\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\140\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\148\255\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\175\000\197\000\105\000\131\000\000\000\
\027\000\053\000\000\000\000\000\000\000\000\000\000\000\000\000\
\010\000\073\255\000\000\000\000\000\000\150\255\000\000\000\000\
\000\000\000\000\000\000\000\000\151\255\000\000\000\000\000\000\
\013\000\000\000\000\000\000\000\000\000\000\000\000\000\017\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\144\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\020\000\000\000\000\000"

let yygindex = "\000\000\
\000\000\000\000\253\255\255\255\249\255\200\255\044\000\054\000\
\000\000\095\000\099\000\086\000\132\000\116\000\102\000\241\255\
\114\000\120\000"

let yytablesize = 530
let yytable = "\015\000\
\045\000\041\000\029\000\039\000\049\000\113\000\035\000\037\000\
\038\000\004\000\057\000\056\000\006\000\022\000\023\000\024\000\
\005\000\084\000\001\000\010\000\055\000\102\000\053\000\057\000\
\060\000\025\000\043\000\059\000\026\000\057\000\114\000\022\000\
\023\000\024\000\044\000\045\000\075\000\024\000\027\000\106\000\
\057\000\028\000\110\000\025\000\046\000\024\000\026\000\080\000\
\064\000\095\000\083\000\024\000\044\000\082\000\081\000\105\000\
\027\000\049\000\049\000\058\000\024\000\086\000\089\000\088\000\
\109\000\091\000\077\000\078\000\057\000\022\000\023\000\024\000\
\096\000\061\000\093\000\099\000\042\000\043\000\042\000\027\000\
\066\000\025\000\100\000\065\000\026\000\067\000\027\000\027\000\
\096\000\027\000\027\000\096\000\076\000\104\000\027\000\098\000\
\108\000\047\000\048\000\111\000\112\000\079\000\027\000\115\000\
\040\000\116\000\120\000\117\000\062\000\063\000\063\000\119\000\
\123\000\057\000\089\000\044\000\045\000\101\000\120\000\003\000\
\004\000\005\000\125\000\031\000\103\000\078\000\057\000\068\000\
\069\000\107\000\041\000\007\000\032\000\118\000\008\000\003\000\
\004\000\005\000\009\000\031\000\124\000\010\000\113\000\022\000\
\023\000\024\000\011\000\007\000\073\000\074\000\008\000\126\000\
\039\000\058\000\009\000\025\000\050\000\010\000\026\000\070\000\
\071\000\033\000\011\000\003\000\004\000\005\000\055\000\031\000\
\027\000\127\000\021\000\122\000\094\000\092\000\035\000\007\000\
\087\000\072\000\008\000\085\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\036\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\019\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\012\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\045\000\040\000\045\000\045\000\
\045\000\045\000\045\000\045\000\045\000\004\000\045\000\045\000\
\006\000\045\000\045\000\045\000\005\000\045\000\045\000\010\000\
\045\000\045\000\000\000\045\000\000\000\000\000\043\000\045\000\
\043\000\043\000\043\000\043\000\043\000\043\000\043\000\000\000\
\043\000\043\000\000\000\043\000\043\000\043\000\000\000\043\000\
\043\000\000\000\043\000\043\000\000\000\043\000\000\000\000\000\
\044\000\043\000\044\000\044\000\044\000\044\000\044\000\044\000\
\044\000\000\000\044\000\044\000\000\000\044\000\044\000\044\000\
\000\000\044\000\044\000\000\000\044\000\044\000\000\000\044\000\
\000\000\000\000\042\000\044\000\042\000\042\000\042\000\042\000\
\042\000\000\000\000\000\000\000\042\000\042\000\000\000\042\000\
\042\000\042\000\000\000\042\000\042\000\000\000\042\000\042\000\
\000\000\042\000\000\000\000\000\040\000\042\000\040\000\040\000\
\040\000\040\000\040\000\000\000\000\000\000\000\040\000\040\000\
\000\000\040\000\040\000\040\000\000\000\040\000\040\000\000\000\
\040\000\040\000\000\000\040\000\000\000\000\000\041\000\040\000\
\041\000\041\000\041\000\041\000\041\000\000\000\000\000\000\000\
\041\000\041\000\000\000\041\000\041\000\041\000\000\000\041\000\
\041\000\000\000\041\000\041\000\039\000\041\000\039\000\039\000\
\039\000\041\000\000\000\000\000\000\000\000\000\039\000\039\000\
\000\000\039\000\039\000\000\000\000\000\039\000\039\000\000\000\
\039\000\039\000\035\000\039\000\035\000\035\000\035\000\039\000\
\000\000\000\000\000\000\000\000\035\000\035\000\000\000\035\000\
\035\000\000\000\000\000\035\000\035\000\000\000\035\000\035\000\
\036\000\035\000\036\000\036\000\036\000\035\000\000\000\000\000\
\000\000\000\000\036\000\036\000\000\000\036\000\036\000\000\000\
\000\000\036\000\036\000\000\000\036\000\036\000\019\000\036\000\
\019\000\000\000\000\000\036\000\000\000\000\000\000\000\000\000\
\019\000\019\000\000\000\019\000\019\000\000\000\000\000\019\000\
\019\000\000\000\019\000\019\000\000\000\019\000\003\000\004\000\
\005\000\019\000\006\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\007\000\000\000\000\000\008\000\000\000\000\000\
\000\000\009\000\000\000\000\000\010\000\000\000\000\000\000\000\
\000\000\011\000"

let yycheck = "\001\000\
\000\000\000\000\006\000\011\000\020\000\006\001\008\000\009\000\
\010\000\000\000\019\001\007\001\000\000\001\001\002\001\003\001\
\000\000\007\001\001\000\000\000\028\000\030\001\026\000\019\001\
\015\001\013\001\000\000\031\000\016\001\019\001\031\001\001\001\
\002\001\003\001\009\001\010\001\015\001\003\001\026\001\096\000\
\019\001\029\001\099\000\013\001\019\001\003\001\016\001\055\000\
\017\001\007\001\058\000\003\001\000\000\057\000\056\000\007\001\
\026\001\073\000\074\000\029\001\003\001\063\000\066\000\065\000\
\007\001\067\000\017\001\018\001\019\001\001\001\002\001\003\001\
\080\000\014\001\078\000\083\000\007\001\008\001\000\000\007\001\
\024\001\013\001\084\000\021\001\016\001\030\001\014\001\015\001\
\096\000\017\001\018\001\099\000\014\001\095\000\026\001\006\001\
\098\000\011\001\012\001\101\000\102\000\017\001\030\001\105\000\
\000\000\107\000\114\000\109\000\017\001\018\001\018\001\113\000\
\120\000\019\001\118\000\009\001\010\001\022\001\126\000\001\001\
\002\001\003\001\124\000\005\001\027\001\018\001\019\001\042\000\
\043\000\006\001\000\000\013\001\014\001\025\001\016\001\001\001\
\002\001\003\001\020\001\005\001\007\001\023\001\006\001\001\001\
\002\001\003\001\028\001\013\001\047\000\048\000\016\001\031\001\
\000\000\014\001\020\001\013\001\014\001\023\001\016\001\044\000\
\045\000\014\001\028\001\001\001\002\001\003\001\017\001\017\001\
\026\001\126\000\027\001\118\000\078\000\075\000\000\000\013\001\
\063\000\046\000\016\001\060\000\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\000\000\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\000\000\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\000\000\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\004\001\004\001\006\001\007\001\
\008\001\009\001\010\001\011\001\012\001\004\001\014\001\015\001\
\004\001\017\001\018\001\019\001\004\001\021\001\022\001\004\001\
\024\001\025\001\255\255\027\001\255\255\255\255\004\001\031\001\
\006\001\007\001\008\001\009\001\010\001\011\001\012\001\255\255\
\014\001\015\001\255\255\017\001\018\001\019\001\255\255\021\001\
\022\001\255\255\024\001\025\001\255\255\027\001\255\255\255\255\
\004\001\031\001\006\001\007\001\008\001\009\001\010\001\011\001\
\012\001\255\255\014\001\015\001\255\255\017\001\018\001\019\001\
\255\255\021\001\022\001\255\255\024\001\025\001\255\255\027\001\
\255\255\255\255\004\001\031\001\006\001\007\001\008\001\009\001\
\010\001\255\255\255\255\255\255\014\001\015\001\255\255\017\001\
\018\001\019\001\255\255\021\001\022\001\255\255\024\001\025\001\
\255\255\027\001\255\255\255\255\004\001\031\001\006\001\007\001\
\008\001\009\001\010\001\255\255\255\255\255\255\014\001\015\001\
\255\255\017\001\018\001\019\001\255\255\021\001\022\001\255\255\
\024\001\025\001\255\255\027\001\255\255\255\255\004\001\031\001\
\006\001\007\001\008\001\009\001\010\001\255\255\255\255\255\255\
\014\001\015\001\255\255\017\001\018\001\019\001\255\255\021\001\
\022\001\255\255\024\001\025\001\004\001\027\001\006\001\007\001\
\008\001\031\001\255\255\255\255\255\255\255\255\014\001\015\001\
\255\255\017\001\018\001\255\255\255\255\021\001\022\001\255\255\
\024\001\025\001\004\001\027\001\006\001\007\001\008\001\031\001\
\255\255\255\255\255\255\255\255\014\001\015\001\255\255\017\001\
\018\001\255\255\255\255\021\001\022\001\255\255\024\001\025\001\
\004\001\027\001\006\001\007\001\008\001\031\001\255\255\255\255\
\255\255\255\255\014\001\015\001\255\255\017\001\018\001\255\255\
\255\255\021\001\022\001\255\255\024\001\025\001\004\001\027\001\
\006\001\255\255\255\255\031\001\255\255\255\255\255\255\255\255\
\014\001\015\001\255\255\017\001\018\001\255\255\255\255\021\001\
\022\001\255\255\024\001\025\001\255\255\027\001\001\001\002\001\
\003\001\031\001\005\001\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\013\001\255\255\255\255\016\001\255\255\255\255\
\255\255\020\001\255\255\255\255\023\001\255\255\255\255\255\255\
\255\255\028\001"

let yynames_const = "\
  EOC\000\
  LET\000\
  IN\000\
  EQ\000\
  LT\000\
  PLUS\000\
  MINUS\000\
  TIMES\000\
  DIV\000\
  LBRA\000\
  RBRA\000\
  SEMI\000\
  LPAR\000\
  RPAR\000\
  COMMA\000\
  CONS\000\
  IF\000\
  THEN\000\
  ELSE\000\
  MATCH\000\
  WITH\000\
  BAR\000\
  UNDERSCORE\000\
  END\000\
  FUN\000\
  REC\000\
  RARROW\000\
  AND\000\
  EOF\000\
  "

let yynames_block = "\
  INT\000\
  BOOL\000\
  ID\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'command_expr) in
    Obj.repr(
# 32 "parser.mly"
                         ( _1 )
# 348 "parser.ml"
               : Syntax.command))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'command_expr) in
    Obj.repr(
# 33 "parser.mly"
                         ( _1 )
# 355 "parser.ml"
               : Syntax.command))
; (fun __caml_parser_env ->
    Obj.repr(
# 34 "parser.mly"
                         ( CEnd )
# 361 "parser.ml"
               : Syntax.command))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'pattern_expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 38 "parser.mly"
                                               ( CLet (_2,_4) )
# 369 "parser.ml"
               : 'command_expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 3 : 'var) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'var) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 39 "parser.mly"
                                               ( CRLet (_3,_4,_6) )
# 378 "parser.ml"
               : 'command_expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'var) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'var) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'argument_expr) in
    Obj.repr(
# 41 "parser.mly"
                                               ( CRLet (_3,_4,_5) )
# 387 "parser.ml"
               : 'command_expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 5 : 'var) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : 'var) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _8 = (Parsing.peek_val __caml_parser_env 0 : 'mutualrec_expr) in
    Obj.repr(
# 42 "parser.mly"
                                               ( CMRLet ([(_3,_4,_6)] @ (_8)) )
# 397 "parser.ml"
               : 'command_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 43 "parser.mly"
                                               ( CExp (_1) )
# 404 "parser.ml"
               : 'command_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 5 : 'var) in
    let _2 = (Parsing.peek_val __caml_parser_env 4 : 'var) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'mutualrec_expr) in
    Obj.repr(
# 46 "parser.mly"
                                        ( [(_1,_2,_4)] @ (_6) )
# 414 "parser.ml"
               : 'mutualrec_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'var) in
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'var) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 47 "parser.mly"
                                        ( [(_1,_2,_4)] )
# 423 "parser.ml"
               : 'mutualrec_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'var) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'argument_expr) in
    Obj.repr(
# 50 "parser.mly"
                           ( EFun (_1,_2) )
# 431 "parser.ml"
               : 'argument_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'var) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 51 "parser.mly"
                           ( EFun (_1,_3) )
# 439 "parser.ml"
               : 'argument_expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : 'pattern_expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 54 "parser.mly"
                                      ( ELet (_2,_4,_6) )
# 448 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'var) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 55 "parser.mly"
                                      ( EFun (_2,_4) )
# 456 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 5 : 'var) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : 'var) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _8 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 56 "parser.mly"
                                      ( ERLet (_3,_4,_6,_8) )
# 466 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 4 : 'var) in
    let _4 = (Parsing.peek_val __caml_parser_env 3 : 'var) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : 'argument_expr) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 57 "parser.mly"
                                            ( ERLet (_3,_4,_5, _7) )
# 476 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 58 "parser.mly"
                                      ( EIf (_2,_4,_6) )
# 485 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'branch_expr) in
    Obj.repr(
# 59 "parser.mly"
                                      ( EMatch (_2,_4) )
# 493 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'compare_expr) in
    Obj.repr(
# 60 "parser.mly"
                                      ( _1 )
# 500 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : 'pattern_expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'branch_expr) in
    Obj.repr(
# 63 "parser.mly"
                                             ( (_1,_3)::(_5) )
# 509 "parser.ml"
               : 'branch_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'pattern_expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 64 "parser.mly"
                                             ( [(_1,_3)] )
# 517 "parser.ml"
               : 'branch_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 67 "parser.mly"
                                   ( PInt  _1 )
# 524 "parser.ml"
               : 'pattern_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : bool) in
    Obj.repr(
# 68 "parser.mly"
                                   ( PBool _1 )
# 531 "parser.ml"
               : 'pattern_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'var) in
    Obj.repr(
# 69 "parser.mly"
                                   ( PVar  _1 )
# 538 "parser.ml"
               : 'pattern_expr))
; (fun __caml_parser_env ->
    Obj.repr(
# 70 "parser.mly"
                                   ( PUnderscore )
# 544 "parser.ml"
               : 'pattern_expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'tuple_pattern_expr) in
    Obj.repr(
# 71 "parser.mly"
                                   ( PTuple (_2) )
# 551 "parser.ml"
               : 'pattern_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'pattern_expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'pattern_expr) in
    Obj.repr(
# 72 "parser.mly"
                                   ( PCons (_1,_3) )
# 559 "parser.ml"
               : 'pattern_expr))
; (fun __caml_parser_env ->
    Obj.repr(
# 73 "parser.mly"
                                   ( PNil )
# 565 "parser.ml"
               : 'pattern_expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'list_pattern_expr) in
    Obj.repr(
# 74 "parser.mly"
                                   ( _2 )
# 572 "parser.ml"
               : 'pattern_expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'pattern_expr) in
    Obj.repr(
# 75 "parser.mly"
                                   ( _2 )
# 579 "parser.ml"
               : 'pattern_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'pattern_expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'pattern_expr) in
    Obj.repr(
# 78 "parser.mly"
                                          ( [_1;_3] )
# 587 "parser.ml"
               : 'tuple_pattern_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'pattern_expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'tuple_pattern_expr) in
    Obj.repr(
# 79 "parser.mly"
                                          ( [_1] @ (_3) )
# 595 "parser.ml"
               : 'tuple_pattern_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'pattern_expr) in
    Obj.repr(
# 82 "parser.mly"
                                        ( PCons (_1, PNil) )
# 602 "parser.ml"
               : 'list_pattern_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'pattern_expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'list_pattern_expr) in
    Obj.repr(
# 83 "parser.mly"
                                        ( PCons (_1,_3) )
# 610 "parser.ml"
               : 'list_pattern_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'compare_expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'arith_expr) in
    Obj.repr(
# 86 "parser.mly"
                               ( EBin (OpEq,_1,_3) )
# 618 "parser.ml"
               : 'compare_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'compare_expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'arith_expr) in
    Obj.repr(
# 87 "parser.mly"
                               ( EBin (OpLt,_1,_3) )
# 626 "parser.ml"
               : 'compare_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'cons_expr) in
    Obj.repr(
# 88 "parser.mly"
                               ( _1 )
# 633 "parser.ml"
               : 'compare_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'arith_expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'cons_expr) in
    Obj.repr(
# 91 "parser.mly"
                             ( ECons (_1,_3) )
# 641 "parser.ml"
               : 'cons_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'arith_expr) in
    Obj.repr(
# 92 "parser.mly"
                              ( _1 )
# 648 "parser.ml"
               : 'cons_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'arith_expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'factor_expr) in
    Obj.repr(
# 95 "parser.mly"
                                 ( EBin(OpAdd,_1,_3) )
# 656 "parser.ml"
               : 'arith_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'arith_expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'factor_expr) in
    Obj.repr(
# 96 "parser.mly"
                                 ( EBin(OpSub,_1,_3) )
# 664 "parser.ml"
               : 'arith_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'factor_expr) in
    Obj.repr(
# 97 "parser.mly"
                                 ( _1 )
# 671 "parser.ml"
               : 'arith_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'factor_expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'app_expr) in
    Obj.repr(
# 100 "parser.mly"
                               ( EBin(OpMul,_1,_3) )
# 679 "parser.ml"
               : 'factor_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'factor_expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'app_expr) in
    Obj.repr(
# 101 "parser.mly"
                               ( EBin(OpDiv,_1,_3) )
# 687 "parser.ml"
               : 'factor_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'app_expr) in
    Obj.repr(
# 102 "parser.mly"
                               ( _1 )
# 694 "parser.ml"
               : 'factor_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'app_expr) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'atomic_expr) in
    Obj.repr(
# 105 "parser.mly"
                         ( EApp (_1,_2) )
# 702 "parser.ml"
               : 'app_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'atomic_expr) in
    Obj.repr(
# 106 "parser.mly"
                         ( _1 )
# 709 "parser.ml"
               : 'app_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 109 "parser.mly"
                         ( EValue (VInt _1) )
# 716 "parser.ml"
               : 'atomic_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : bool) in
    Obj.repr(
# 110 "parser.mly"
                         ( EValue (VBool _1))
# 723 "parser.ml"
               : 'atomic_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 111 "parser.mly"
                         ( EVar   _1 )
# 730 "parser.ml"
               : 'atomic_expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'tuple_expr) in
    Obj.repr(
# 112 "parser.mly"
                         ( ETuple (_2) )
# 737 "parser.ml"
               : 'atomic_expr))
; (fun __caml_parser_env ->
    Obj.repr(
# 113 "parser.mly"
                         ( ENil )
# 743 "parser.ml"
               : 'atomic_expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'list_expr) in
    Obj.repr(
# 114 "parser.mly"
                         ( _2 )
# 750 "parser.ml"
               : 'atomic_expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 115 "parser.mly"
                         ( _2 )
# 757 "parser.ml"
               : 'atomic_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 118 "parser.mly"
                          ( [_1;_3] )
# 765 "parser.ml"
               : 'tuple_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'tuple_expr) in
    Obj.repr(
# 119 "parser.mly"
                          ( [_1] @ (_3) )
# 773 "parser.ml"
               : 'tuple_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'list_expr) in
    Obj.repr(
# 123 "parser.mly"
                        ( ECons (_1,_3) )
# 781 "parser.ml"
               : 'list_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 124 "parser.mly"
                        ( ECons (_1, ENil) )
# 788 "parser.ml"
               : 'list_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 127 "parser.mly"
       ( _1 )
# 795 "parser.ml"
               : 'var))
(* Entry main *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let main (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : Syntax.command)
