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
  | LEN
  | NTH
  | ALLOC
  | VSET
  | VEC

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

# 61 "parser.ml"
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
  294 (* LEN *);
  295 (* NTH *);
  296 (* ALLOC *);
  297 (* VSET *);
  298 (* VEC *);
    0|]

let yytransl_block = [|
  257 (* NUM *);
  258 (* IDENT *);
    0|]

let yylhs = "\255\255\
\006\000\014\000\005\000\005\000\005\000\007\000\007\000\007\000\
\007\000\008\000\008\000\010\000\011\000\011\000\012\000\012\000\
\013\000\013\000\001\000\001\000\001\000\001\000\001\000\001\000\
\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\
\001\000\001\000\001\000\001\000\001\000\001\000\002\000\002\000\
\003\000\003\000\004\000\004\000\016\000\016\000\015\000\015\000\
\015\000\015\000\015\000\009\000\009\000\009\000\009\000\009\000\
\009\000\000\000"

let yylen = "\002\000\
\003\000\003\000\001\000\003\000\003\000\001\000\001\000\005\000\
\004\000\001\000\003\000\003\000\001\000\003\000\003\000\004\000\
\001\000\003\000\001\000\001\000\001\000\001\000\006\000\005\000\
\005\000\005\000\005\000\005\000\005\000\005\000\005\000\004\000\
\004\000\004\000\004\000\005\000\004\000\006\000\001\000\002\000\
\001\000\004\000\001\000\002\000\001\000\005\000\002\000\003\000\
\003\000\003\000\004\000\004\000\007\000\008\000\003\000\006\000\
\007\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\058\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\019\000\020\000\000\000\000\000\021\000\
\022\000\047\000\000\000\045\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\001\000\000\000\000\000\000\000\006\000\
\007\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\055\000\000\000\
\048\000\000\000\049\000\000\000\000\000\000\000\000\000\041\000\
\000\000\050\000\004\000\005\000\000\000\000\000\000\000\052\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\051\000\
\000\000\000\000\000\000\000\000\000\000\000\000\044\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\032\000\
\000\000\000\000\000\000\000\000\000\000\000\000\035\000\000\000\
\037\000\000\000\040\000\033\000\012\000\014\000\034\000\000\000\
\002\000\000\000\000\000\000\000\000\000\000\000\000\000\009\000\
\011\000\000\000\000\000\000\000\000\000\024\000\025\000\030\000\
\031\000\026\000\027\000\028\000\029\000\036\000\000\000\046\000\
\015\000\000\000\018\000\056\000\000\000\042\000\008\000\053\000\
\000\000\023\000\038\000\016\000\057\000\054\000"

let yydgoto = "\002\000\
\059\000\098\000\073\000\074\000\014\000\004\000\078\000\079\000\
\015\000\061\000\062\000\107\000\108\000\067\000\016\000\030\000"

let yysindex = "\007\000\
\010\255\000\000\111\255\000\000\014\255\003\255\070\255\016\255\
\009\255\070\255\070\255\005\255\070\255\018\255\013\255\015\255\
\085\255\085\255\023\255\000\000\000\000\195\255\055\255\000\000\
\000\000\000\000\085\255\000\000\247\254\070\255\053\255\053\255\
\054\255\058\255\099\255\000\000\111\255\111\255\028\255\000\000\
\000\000\070\255\056\255\085\255\070\255\070\255\070\255\070\255\
\070\255\070\255\070\255\070\255\070\255\070\255\070\255\070\255\
\070\255\070\255\070\255\057\255\064\255\061\255\000\000\009\255\
\000\000\111\255\000\000\053\255\024\255\059\255\154\255\000\000\
\099\255\000\000\000\000\000\000\085\255\077\255\052\255\000\000\
\055\255\063\255\070\255\070\255\070\255\075\255\070\255\070\255\
\070\255\070\255\070\255\070\255\088\255\070\255\089\255\070\255\
\070\255\092\255\085\255\055\255\070\255\070\255\091\255\000\000\
\097\255\105\255\098\255\103\255\024\255\070\255\000\000\109\255\
\085\255\085\255\108\255\055\255\070\255\112\255\113\255\000\000\
\114\255\115\255\116\255\117\255\118\255\120\255\000\000\121\255\
\000\000\070\255\000\000\000\000\000\000\000\000\000\000\125\255\
\000\000\085\255\107\255\024\255\053\255\126\255\127\255\000\000\
\000\000\131\255\070\255\132\255\133\255\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\135\255\000\000\
\000\000\085\255\000\000\000\000\053\255\000\000\000\000\000\000\
\070\255\000\000\000\000\000\000\000\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\137\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\138\255\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\007\255\000\000\000\000\000\000\000\000\140\255\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\145\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\146\255\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000"

let yygindex = "\000\000\
\249\255\056\000\000\000\085\000\252\255\000\000\248\255\047\000\
\000\000\000\000\177\255\000\000\148\255\241\255\000\000\097\000"

let yytablesize = 236
let yytable = "\026\000\
\142\000\115\000\031\000\032\000\018\000\035\000\033\000\001\000\
\042\000\043\000\028\000\029\000\043\000\043\000\003\000\017\000\
\068\000\027\000\063\000\037\000\134\000\038\000\065\000\036\000\
\044\000\105\000\019\000\072\000\034\000\064\000\039\000\163\000\
\075\000\076\000\080\000\082\000\148\000\083\000\084\000\085\000\
\086\000\087\000\088\000\089\000\090\000\091\000\092\000\093\000\
\094\000\095\000\096\000\097\000\104\000\040\000\041\000\106\000\
\060\000\066\000\069\000\070\000\081\000\103\000\114\000\109\000\
\099\000\072\000\101\000\116\000\112\000\077\000\020\000\021\000\
\022\000\100\000\023\000\117\000\118\000\119\000\120\000\121\000\
\122\000\123\000\124\000\125\000\126\000\113\000\128\000\039\000\
\130\000\097\000\133\000\127\000\129\000\135\000\136\000\132\000\
\137\000\024\000\025\000\020\000\021\000\071\000\143\000\023\000\
\138\000\146\000\139\000\140\000\141\000\149\000\040\000\041\000\
\144\000\147\000\162\000\150\000\151\000\152\000\153\000\154\000\
\155\000\156\000\159\000\157\000\158\000\164\000\024\000\025\000\
\160\000\161\000\166\000\165\000\005\000\006\000\167\000\007\000\
\170\000\169\000\171\000\168\000\008\000\009\000\003\000\013\000\
\010\000\011\000\012\000\013\000\039\000\173\000\010\000\017\000\
\131\000\172\000\020\000\021\000\022\000\111\000\023\000\145\000\
\102\000\174\000\000\000\000\000\000\000\045\000\046\000\047\000\
\048\000\049\000\050\000\051\000\052\000\053\000\054\000\000\000\
\000\000\000\000\000\000\000\000\000\000\024\000\025\000\000\000\
\000\000\000\000\110\000\000\000\000\000\000\000\000\000\055\000\
\056\000\057\000\058\000\020\000\021\000\022\000\000\000\023\000\
\000\000\000\000\000\000\000\000\000\000\000\000\045\000\046\000\
\047\000\048\000\049\000\050\000\051\000\052\000\053\000\054\000\
\000\000\000\000\000\000\000\000\000\000\000\000\024\000\025\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\055\000\056\000\057\000\058\000"

let yycheck = "\007\000\
\109\000\081\000\010\000\011\000\002\001\013\000\002\001\001\000\
\017\000\018\000\002\001\003\001\006\001\007\001\005\001\002\001\
\032\000\002\001\027\000\007\001\100\000\007\001\030\000\006\001\
\002\001\002\001\024\001\035\000\024\001\039\001\003\001\140\000\
\037\000\038\000\042\000\044\000\116\000\045\000\046\000\047\000\
\048\000\049\000\050\000\051\000\052\000\053\000\054\000\055\000\
\056\000\057\000\058\000\059\000\068\000\026\001\027\001\032\001\
\002\001\005\001\005\001\002\001\005\001\066\000\011\001\005\001\
\008\001\073\000\006\001\005\001\077\000\042\001\001\001\002\001\
\003\001\010\001\005\001\083\000\084\000\085\000\004\001\087\000\
\088\000\089\000\090\000\091\000\092\000\009\001\094\000\003\001\
\096\000\097\000\099\000\004\001\004\001\101\000\102\000\004\001\
\006\001\028\001\029\001\001\001\002\001\003\001\110\000\005\001\
\008\001\114\000\002\001\010\001\006\001\117\000\026\001\027\001\
\004\001\006\001\008\001\004\001\004\001\004\001\004\001\004\001\
\004\001\004\001\130\000\004\001\004\001\141\000\028\001\029\001\
\004\001\138\000\004\001\006\001\022\001\023\001\004\001\025\001\
\004\001\006\001\004\001\147\000\030\001\031\001\006\001\006\001\
\034\001\035\001\036\001\037\001\004\001\165\000\011\001\006\001\
\097\000\162\000\001\001\002\001\003\001\073\000\005\001\113\000\
\064\000\169\000\255\255\255\255\255\255\012\001\013\001\014\001\
\015\001\016\001\017\001\018\001\019\001\020\001\021\001\255\255\
\255\255\255\255\255\255\255\255\255\255\028\001\029\001\255\255\
\255\255\255\255\033\001\255\255\255\255\255\255\255\255\038\001\
\039\001\040\001\041\001\001\001\002\001\003\001\255\255\005\001\
\255\255\255\255\255\255\255\255\255\255\255\255\012\001\013\001\
\014\001\015\001\016\001\017\001\018\001\019\001\020\001\021\001\
\255\255\255\255\255\255\255\255\255\255\255\255\028\001\029\001\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\038\001\039\001\040\001\041\001"

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
  LEN\000\
  NTH\000\
  ALLOC\000\
  VSET\000\
  VEC\000\
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
# 330 "parser.ml"
               : Ast.cmd list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Ast.cmd list) in
    Obj.repr(
# 48 "parser.mly"
                        ( ASTBlock(_2) )
# 337 "parser.ml"
               : 'block))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'stat) in
    Obj.repr(
# 52 "parser.mly"
                        ( [ASTStat _1] )
# 344 "parser.ml"
               : Ast.cmd list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Ast.def) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.cmd list) in
    Obj.repr(
# 53 "parser.mly"
                        ( ASTDec(_1)::_3 )
# 352 "parser.ml"
               : Ast.cmd list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'stat) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.cmd list) in
    Obj.repr(
# 54 "parser.mly"
                        ( ASTStat(_1)::_3 )
# 360 "parser.ml"
               : Ast.cmd list))
; (fun __caml_parser_env ->
    Obj.repr(
# 58 "parser.mly"
                                 ( Int )
# 366 "parser.ml"
               : Ast.typ))
; (fun __caml_parser_env ->
    Obj.repr(
# 59 "parser.mly"
                                 ( Bool )
# 372 "parser.ml"
               : Ast.typ))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : Ast.typs) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.typ) in
    Obj.repr(
# 60 "parser.mly"
                                 ( ASTTypeFunc(_2, _4) )
# 380 "parser.ml"
               : Ast.typ))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast.typ) in
    Obj.repr(
# 61 "parser.mly"
                                 ( ASTTypeVec(_3) )
# 387 "parser.ml"
               : Ast.typ))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast.typ) in
    Obj.repr(
# 65 "parser.mly"
                                 ( ASTType(_1) )
# 394 "parser.ml"
               : Ast.typs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Ast.typ) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.typs) in
    Obj.repr(
# 66 "parser.mly"
                                 ( ASTTypes(_1, _3) )
# 402 "parser.ml"
               : Ast.typs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.typ) in
    Obj.repr(
# 70 "parser.mly"
                                 ( ASTArg(_1, _3) )
# 410 "parser.ml"
               : Ast.arg))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast.arg) in
    Obj.repr(
# 73 "parser.mly"
                                ( [_1] )
# 417 "parser.ml"
               : Ast.arg list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Ast.arg) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.arg list) in
    Obj.repr(
# 74 "parser.mly"
                                ( _1::_3 )
# 425 "parser.ml"
               : Ast.arg list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.typ) in
    Obj.repr(
# 77 "parser.mly"
                                ( ASTArgp(_1, _3) )
# 433 "parser.ml"
               : Ast.argp))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : Ast.typ) in
    Obj.repr(
# 78 "parser.mly"
                                ( ASTArgpVar(_2, _4) )
# 441 "parser.ml"
               : Ast.argp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast.argp) in
    Obj.repr(
# 81 "parser.mly"
                                ( [_1] )
# 448 "parser.ml"
               : Ast.argp list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Ast.argp) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.argp list) in
    Obj.repr(
# 82 "parser.mly"
                                ( _1::_3 )
# 456 "parser.ml"
               : Ast.argp list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 86 "parser.mly"
                                ( ASTNum(_1) )
# 463 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 87 "parser.mly"
                                ( ASTId(_1) )
# 470 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    Obj.repr(
# 88 "parser.mly"
                                ( ASTBool(true) )
# 476 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    Obj.repr(
# 89 "parser.mly"
                                ( ASTBool(false) )
# 482 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 3 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 90 "parser.mly"
                                ( ASTIf(_3, _4, _5) )
# 491 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 91 "parser.mly"
                                ( ASTAnd(_3, _4) )
# 499 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 92 "parser.mly"
                                ( ASTOr(_3, _4) )
# 507 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 93 "parser.mly"
                                ( ASTBinary(Ast.ADD, _3, _4) )
# 515 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 94 "parser.mly"
                                ( ASTBinary(Ast.SUB, _3, _4) )
# 523 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 95 "parser.mly"
                                ( ASTBinary(Ast.MUL, _3, _4) )
# 531 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 96 "parser.mly"
                                ( ASTBinary(Ast.DIV, _3, _4) )
# 539 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 97 "parser.mly"
                                ( ASTBinary(Ast.EQ, _3, _4) )
# 547 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 98 "parser.mly"
                                ( ASTBinary(Ast.LT, _3, _4) )
# 555 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 99 "parser.mly"
                                ( ASTUnary(Ast.NOT, _3) )
# 562 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr list) in
    Obj.repr(
# 100 "parser.mly"
                                ( ASTApp(_2, _3) )
# 570 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : Ast.arg list) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 101 "parser.mly"
                                ( ASTArgs(_2, _4) )
# 578 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 102 "parser.mly"
                                ( ASTLen(_3) )
# 585 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 103 "parser.mly"
                                ( ASTNth(_3, _4) )
# 593 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 104 "parser.mly"
                                ( ASTAlloc(_3) )
# 600 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 3 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 105 "parser.mly"
                                ( ASTVset(_3, _4, _5) )
# 609 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 109 "parser.mly"
                                ( [_1] )
# 616 "parser.ml"
               : Ast.expr list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr list) in
    Obj.repr(
# 110 "parser.mly"
                                ( _1::_2 )
# 624 "parser.ml"
               : Ast.expr list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 114 "parser.mly"
                                ( ASTExprp(_1) )
# 631 "parser.ml"
               : Ast.exprp))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 115 "parser.mly"
                                ( ASTExprpAdr(_3) )
# 638 "parser.ml"
               : Ast.exprp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast.exprp) in
    Obj.repr(
# 119 "parser.mly"
                                ( [_1] )
# 645 "parser.ml"
               : Ast.exprp list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : Ast.exprp) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : Ast.exprp list) in
    Obj.repr(
# 120 "parser.mly"
                                ( _1::_2 )
# 653 "parser.ml"
               : Ast.exprp list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 124 "parser.mly"
                                ( ASTLvId(_1) )
# 660 "parser.ml"
               : 'lval))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'lval) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 125 "parser.mly"
                                ( ASTLvVar(_3, _4) )
# 668 "parser.ml"
               : 'lval))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 129 "parser.mly"
                        ( ASTEcho(_2) )
# 675 "parser.ml"
               : 'stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'lval) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 130 "parser.mly"
                        ( ASTSet(_2, _3) )
# 683 "parser.ml"
               : 'stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 131 "parser.mly"
                        ( ASTWhile(_2, _3))
# 691 "parser.ml"
               : 'stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.exprp list) in
    Obj.repr(
# 132 "parser.mly"
                        ( ASTCall(_2, _3) )
# 699 "parser.ml"
               : 'stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'block) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 133 "parser.mly"
                        ( ASTIfb(_2, _3, _4) )
# 708 "parser.ml"
               : 'stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast.typ) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 137 "parser.mly"
                                         ( ASTConst(_2, _3, _4) )
# 717 "parser.ml"
               : Ast.def))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 4 : Ast.typ) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : Ast.arg list) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 138 "parser.mly"
                                         ( ASTFun(_2, _3, _5, _7) )
# 727 "parser.ml"
               : Ast.def))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : Ast.typ) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : Ast.arg list) in
    let _8 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 139 "parser.mly"
                                         ( ASTFunRec(_3, _4, _6, _8) )
# 737 "parser.ml"
               : Ast.def))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.typ) in
    Obj.repr(
# 140 "parser.mly"
                                         ( ASTVar(_2, _3) )
# 745 "parser.ml"
               : Ast.def))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : Ast.argp list) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 141 "parser.mly"
                                         ( ASTProc(_2, _4, _6) )
# 754 "parser.ml"
               : Ast.def))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : Ast.argp list) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 142 "parser.mly"
                                         ( ASTProcRec(_3, _5, _7) )
# 763 "parser.ml"
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
