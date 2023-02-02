type token =
  | NUM of (int)
  | IDENT of (string)
  | LPAR
  | RPAR
  | LBRA
  | RBRA
  | PVERG
  | DPOINTS
  | STAR
  | VIRGULE
  | ARROW
  | IF
  | AND
  | OR
  | NOT
  | EQ
  | LT
  | ADD
  | SUB
  | MUL
  | DIV
  | CONST
  | FUN
  | REC
  | ECHO
  | INT
  | BOOL
  | TRUE
  | FALSE
  | VAR
  | SET
  | VARP
  | ADR
  | WHILE
  | IFB
  | PROC
  | CALL

open Parsing;;
let _ = parse_error;;
# 2 "parser.mly"
(* ========================================================================== *)
(* == UPMC/master/info/4I506 -- Janvier 2016/2017                          == *)
(* == SU/FSI/master/info/MU4IN503 -- Janvier 2020/2021/2022                == *)
(* == Analyse des programmes et sémantiques                                == *)
(* ========================================================================== *)
(* == hello-APS Syntaxe ML                                                 == *)
(* == Fichier: parser.mly                                                  == *)
(* == Analyse syntaxique                                                   == *)
(* ========================================================================== *)

open Ast

# 56 "parser.ml"
let yytransl_const = [|
  259 (* LPAR *);
  260 (* RPAR *);
  261 (* LBRA *);
  262 (* RBRA *);
  263 (* PVERG *);
  264 (* DPOINTS *);
  265 (* STAR *);
  266 (* VIRGULE *);
  267 (* ARROW *);
  268 (* IF *);
  269 (* AND *);
  270 (* OR *);
  271 (* NOT *);
  272 (* EQ *);
  273 (* LT *);
  274 (* ADD *);
  275 (* SUB *);
  276 (* MUL *);
  277 (* DIV *);
  278 (* CONST *);
  279 (* FUN *);
  280 (* REC *);
  281 (* ECHO *);
  282 (* INT *);
  283 (* BOOL *);
  284 (* TRUE *);
  285 (* FALSE *);
  286 (* VAR *);
  287 (* SET *);
  288 (* VARP *);
  289 (* ADR *);
  290 (* WHILE *);
  291 (* IFB *);
  292 (* PROC *);
  293 (* CALL *);
    0|]

let yytransl_block = [|
  257 (* NUM *);
  258 (* IDENT *);
    0|]

let yylhs = "\255\255\
\006\000\014\000\005\000\005\000\005\000\007\000\007\000\007\000\
\008\000\008\000\010\000\011\000\011\000\012\000\012\000\013\000\
\013\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\
\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\
\001\000\002\000\002\000\003\000\003\000\004\000\004\000\015\000\
\015\000\015\000\015\000\015\000\009\000\009\000\009\000\009\000\
\009\000\009\000\000\000"

let yylen = "\002\000\
\003\000\003\000\001\000\003\000\003\000\001\000\001\000\005\000\
\001\000\003\000\003\000\001\000\003\000\003\000\004\000\001\000\
\003\000\001\000\001\000\001\000\001\000\006\000\005\000\005\000\
\005\000\005\000\005\000\005\000\005\000\005\000\004\000\004\000\
\004\000\001\000\002\000\001\000\004\000\001\000\002\000\002\000\
\003\000\003\000\003\000\004\000\004\000\007\000\008\000\003\000\
\006\000\007\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\051\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\018\000\019\000\000\000\000\000\020\000\
\021\000\040\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\001\000\000\000\000\000\000\000\006\000\007\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\048\000\041\000\000\000\042\000\000\000\000\000\000\000\000\000\
\036\000\000\000\043\000\004\000\005\000\000\000\000\000\045\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\044\000\000\000\000\000\000\000\000\000\000\000\
\000\000\039\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\031\000\000\000\000\000\000\000\000\000\000\000\000\000\
\035\000\032\000\011\000\013\000\033\000\002\000\000\000\000\000\
\000\000\000\000\000\000\000\000\010\000\000\000\000\000\000\000\
\000\000\023\000\024\000\029\000\030\000\025\000\026\000\027\000\
\028\000\014\000\000\000\017\000\049\000\000\000\037\000\008\000\
\046\000\000\000\022\000\015\000\050\000\047\000"

let yydgoto = "\002\000\
\053\000\086\000\066\000\067\000\014\000\004\000\070\000\071\000\
\015\000\055\000\056\000\094\000\095\000\060\000\016\000"

let yysindex = "\010\000\
\010\255\000\000\087\255\000\000\014\255\005\255\022\255\016\255\
\018\255\022\255\022\255\006\255\022\255\042\255\021\255\045\255\
\057\255\057\255\047\255\000\000\000\000\131\255\054\255\000\000\
\000\000\000\000\057\255\022\255\053\255\053\255\058\255\062\255\
\052\255\000\000\087\255\087\255\057\255\000\000\000\000\022\255\
\060\255\057\255\022\255\022\255\022\255\022\255\022\255\022\255\
\022\255\022\255\022\255\022\255\022\255\004\255\056\255\061\255\
\000\000\000\000\087\255\000\000\053\255\003\255\066\255\086\255\
\000\000\052\255\000\000\000\000\000\000\077\255\083\255\000\000\
\054\255\090\255\022\255\022\255\022\255\093\255\022\255\022\255\
\022\255\022\255\022\255\022\255\022\255\104\255\057\255\054\255\
\022\255\110\255\000\000\117\255\124\255\118\255\121\255\003\255\
\022\255\000\000\057\255\057\255\123\255\054\255\022\255\126\255\
\133\255\000\000\134\255\136\255\137\255\138\255\149\255\150\255\
\000\000\000\000\000\000\000\000\000\000\000\000\057\255\127\255\
\003\255\053\255\151\255\152\255\000\000\154\255\022\255\155\255\
\158\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\057\255\000\000\000\000\053\255\000\000\000\000\
\000\000\022\255\000\000\000\000\000\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\157\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\159\255\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\007\255\000\000\000\000\000\000\144\255\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\160\255\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\161\255\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000"

let yygindex = "\000\000\
\249\255\081\000\000\000\102\000\026\000\000\000\248\255\070\000\
\000\000\000\000\185\255\000\000\182\255\227\255\000\000"

let yytablesize = 169
let yytable = "\026\000\
\061\000\101\000\029\000\030\000\092\000\033\000\018\000\031\000\
\040\000\041\000\001\000\087\000\038\000\038\000\003\000\017\000\
\116\000\027\000\057\000\028\000\058\000\123\000\020\000\021\000\
\022\000\065\000\023\000\035\000\019\000\032\000\128\000\091\000\
\072\000\074\000\093\000\075\000\076\000\077\000\078\000\079\000\
\080\000\081\000\082\000\083\000\084\000\085\000\140\000\034\000\
\042\000\024\000\025\000\036\000\020\000\021\000\064\000\054\000\
\023\000\059\000\065\000\037\000\068\000\069\000\062\000\063\000\
\073\000\088\000\089\000\103\000\104\000\105\000\096\000\107\000\
\108\000\109\000\110\000\111\000\112\000\085\000\115\000\024\000\
\025\000\117\000\038\000\039\000\090\000\099\000\020\000\021\000\
\022\000\124\000\023\000\126\000\141\000\100\000\102\000\129\000\
\106\000\043\000\044\000\045\000\046\000\047\000\048\000\049\000\
\050\000\051\000\052\000\114\000\005\000\006\000\138\000\007\000\
\149\000\024\000\025\000\118\000\008\000\009\000\097\000\145\000\
\010\000\011\000\012\000\013\000\119\000\120\000\122\000\121\000\
\127\000\130\000\148\000\020\000\021\000\022\000\139\000\023\000\
\131\000\132\000\150\000\133\000\134\000\135\000\043\000\044\000\
\045\000\046\000\047\000\048\000\049\000\050\000\051\000\052\000\
\136\000\137\000\009\000\143\000\142\000\144\000\024\000\025\000\
\146\000\147\000\003\000\034\000\012\000\113\000\016\000\098\000\
\125\000"

let yycheck = "\007\000\
\030\000\073\000\010\000\011\000\002\001\013\000\002\001\002\001\
\017\000\018\000\001\000\008\001\006\001\007\001\005\001\002\001\
\088\000\002\001\027\000\002\001\028\000\096\000\001\001\002\001\
\003\001\033\000\005\001\007\001\024\001\024\001\102\000\061\000\
\040\000\042\000\032\001\043\000\044\000\045\000\046\000\047\000\
\048\000\049\000\050\000\051\000\052\000\053\000\121\000\006\001\
\002\001\028\001\029\001\007\001\001\001\002\001\003\001\002\001\
\005\001\005\001\066\000\003\001\035\000\036\000\005\001\002\001\
\005\001\010\001\006\001\075\000\076\000\077\000\005\001\079\000\
\080\000\081\000\082\000\083\000\084\000\085\000\087\000\028\001\
\029\001\089\000\026\001\027\001\059\000\009\001\001\001\002\001\
\003\001\097\000\005\001\100\000\122\000\011\001\005\001\103\000\
\004\001\012\001\013\001\014\001\015\001\016\001\017\001\018\001\
\019\001\020\001\021\001\004\001\022\001\023\001\119\000\025\001\
\142\000\028\001\029\001\006\001\030\001\031\001\033\001\127\000\
\034\001\035\001\036\001\037\001\008\001\002\001\006\001\010\001\
\006\001\004\001\139\000\001\001\002\001\003\001\008\001\005\001\
\004\001\004\001\146\000\004\001\004\001\004\001\012\001\013\001\
\014\001\015\001\016\001\017\001\018\001\019\001\020\001\021\001\
\004\001\004\001\011\001\004\001\006\001\004\001\028\001\029\001\
\006\001\004\001\006\001\004\001\006\001\085\000\006\001\066\000\
\099\000"

let yynames_const = "\
  LPAR\000\
  RPAR\000\
  LBRA\000\
  RBRA\000\
  PVERG\000\
  DPOINTS\000\
  STAR\000\
  VIRGULE\000\
  ARROW\000\
  IF\000\
  AND\000\
  OR\000\
  NOT\000\
  EQ\000\
  LT\000\
  ADD\000\
  SUB\000\
  MUL\000\
  DIV\000\
  CONST\000\
  FUN\000\
  REC\000\
  ECHO\000\
  INT\000\
  BOOL\000\
  TRUE\000\
  FALSE\000\
  VAR\000\
  SET\000\
  VARP\000\
  ADR\000\
  WHILE\000\
  IFB\000\
  PROC\000\
  CALL\000\
  "

let yynames_block = "\
  NUM\000\
  IDENT\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Ast.cmd list) in
    Obj.repr(
# 45 "parser.mly"
                        ( _2 )
# 288 "parser.ml"
               : Ast.cmd list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Ast.cmd list) in
    Obj.repr(
# 48 "parser.mly"
                        ( ASTBlock(_2) )
# 295 "parser.ml"
               : 'block))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'stat) in
    Obj.repr(
# 52 "parser.mly"
                        ( [ASTStat _1] )
# 302 "parser.ml"
               : Ast.cmd list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Ast.def) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.cmd list) in
    Obj.repr(
# 53 "parser.mly"
                        ( ASTDec(_1)::_3 )
# 310 "parser.ml"
               : Ast.cmd list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'stat) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.cmd list) in
    Obj.repr(
# 54 "parser.mly"
                        ( ASTStat(_1)::_3 )
# 318 "parser.ml"
               : Ast.cmd list))
; (fun __caml_parser_env ->
    Obj.repr(
# 58 "parser.mly"
                                 ( Int )
# 324 "parser.ml"
               : Ast.typ))
; (fun __caml_parser_env ->
    Obj.repr(
# 59 "parser.mly"
                                 ( Bool )
# 330 "parser.ml"
               : Ast.typ))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : Ast.typs) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.typ) in
    Obj.repr(
# 60 "parser.mly"
                                 ( ASTTypeFunc(_2, _4) )
# 338 "parser.ml"
               : Ast.typ))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast.typ) in
    Obj.repr(
# 64 "parser.mly"
                                 ( ASTType(_1) )
# 345 "parser.ml"
               : Ast.typs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Ast.typ) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.typs) in
    Obj.repr(
# 65 "parser.mly"
                                 ( ASTTypes(_1, _3) )
# 353 "parser.ml"
               : Ast.typs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.typ) in
    Obj.repr(
# 69 "parser.mly"
                                 ( ASTArg(_1, _3) )
# 361 "parser.ml"
               : Ast.arg))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast.arg) in
    Obj.repr(
# 72 "parser.mly"
                                ( [_1] )
# 368 "parser.ml"
               : Ast.arg list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Ast.arg) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.arg list) in
    Obj.repr(
# 73 "parser.mly"
                                ( _1::_3 )
# 376 "parser.ml"
               : Ast.arg list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.typ) in
    Obj.repr(
# 76 "parser.mly"
                                ( ASTArgp(_1, _3) )
# 384 "parser.ml"
               : Ast.argp))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : Ast.typ) in
    Obj.repr(
# 77 "parser.mly"
                                ( ASTArgpVar(_2, _4) )
# 392 "parser.ml"
               : Ast.argp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast.argp) in
    Obj.repr(
# 80 "parser.mly"
                                ( [_1] )
# 399 "parser.ml"
               : Ast.argp list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Ast.argp) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.argp list) in
    Obj.repr(
# 81 "parser.mly"
                                ( _1::_3 )
# 407 "parser.ml"
               : Ast.argp list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 85 "parser.mly"
                                ( ASTNum(_1) )
# 414 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 86 "parser.mly"
                                ( ASTId(_1) )
# 421 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    Obj.repr(
# 87 "parser.mly"
                                ( ASTBool(true) )
# 427 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    Obj.repr(
# 88 "parser.mly"
                                ( ASTBool(false) )
# 433 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 3 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 89 "parser.mly"
                                ( ASTIf(_3, _4, _5) )
# 442 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 90 "parser.mly"
                                ( ASTAnd(_3, _4) )
# 450 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 91 "parser.mly"
                                ( ASTOr(_3, _4) )
# 458 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 92 "parser.mly"
                                ( ASTBinary(Ast.ADD, _3, _4) )
# 466 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 93 "parser.mly"
                                ( ASTBinary(Ast.SUB, _3, _4) )
# 474 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 94 "parser.mly"
                                ( ASTBinary(Ast.MUL, _3, _4) )
# 482 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 95 "parser.mly"
                                ( ASTBinary(Ast.DIV, _3, _4) )
# 490 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 96 "parser.mly"
                                ( ASTBinary(Ast.EQ, _3, _4) )
# 498 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 97 "parser.mly"
                                ( ASTBinary(Ast.LT, _3, _4) )
# 506 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 98 "parser.mly"
                                ( ASTUnary(Ast.NOT, _3) )
# 513 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr list) in
    Obj.repr(
# 99 "parser.mly"
                                ( ASTApp(_2, _3) )
# 521 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : Ast.arg list) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 100 "parser.mly"
                                ( ASTArgs(_2, _4) )
# 529 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 104 "parser.mly"
                                ( [_1] )
# 536 "parser.ml"
               : Ast.expr list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr list) in
    Obj.repr(
# 105 "parser.mly"
                                ( _1::_2 )
# 544 "parser.ml"
               : Ast.expr list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 109 "parser.mly"
                                ( ASTExprp(_1) )
# 551 "parser.ml"
               : Ast.exprp))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 110 "parser.mly"
                                ( ASTExprpAdr(_3) )
# 558 "parser.ml"
               : Ast.exprp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast.exprp) in
    Obj.repr(
# 114 "parser.mly"
                                ( [_1] )
# 565 "parser.ml"
               : Ast.exprp list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : Ast.exprp) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : Ast.exprp list) in
    Obj.repr(
# 115 "parser.mly"
                                ( _1::_2 )
# 573 "parser.ml"
               : Ast.exprp list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 119 "parser.mly"
                        ( ASTEcho(_2) )
# 580 "parser.ml"
               : 'stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 120 "parser.mly"
                        ( ASTSet(_2, _3) )
# 588 "parser.ml"
               : 'stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 121 "parser.mly"
                        ( ASTWhile(_2, _3))
# 596 "parser.ml"
               : 'stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.exprp list) in
    Obj.repr(
# 122 "parser.mly"
                        ( ASTCall(_2, _3) )
# 604 "parser.ml"
               : 'stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'block) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 123 "parser.mly"
                        ( ASTIfb(_2, _3, _4) )
# 613 "parser.ml"
               : 'stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast.typ) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 127 "parser.mly"
                                         ( ASTConst(_2, _3, _4) )
# 622 "parser.ml"
               : Ast.def))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 4 : Ast.typ) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : Ast.arg list) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 128 "parser.mly"
                                         ( ASTFun(_2, _3, _5, _7) )
# 632 "parser.ml"
               : Ast.def))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : Ast.typ) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : Ast.arg list) in
    let _8 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 129 "parser.mly"
                                         ( ASTFunRec(_3, _4, _6, _8) )
# 642 "parser.ml"
               : Ast.def))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.typ) in
    Obj.repr(
# 130 "parser.mly"
                                         ( ASTVar(_2, _3) )
# 650 "parser.ml"
               : Ast.def))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : Ast.argp list) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 131 "parser.mly"
                                         ( ASTProc(_2, _4, _6) )
# 659 "parser.ml"
               : Ast.def))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : Ast.argp list) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 132 "parser.mly"
                                         ( ASTProcRec(_3, _5, _7) )
# 668 "parser.ml"
               : Ast.def))
(* Entry prog *)
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
let prog (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : Ast.cmd list)
