%{
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

%}
  
%token <int> NUM
%token <string> IDENT
%token LPAR RPAR LBRA RBRA PVERG DPOINTS STAR VIRGULE ARROW
%token IF AND OR NOT
%token EQ LT ADD SUB MUL DIV
%token CONST FUN REC ECHO
%token INT BOOL
%token TRUE FALSE
%token VAR SET 
%token VARP ADR
%token WHILE IFB PROC CALL

%type <Ast.expr> expr
%type <Ast.expr list> exprs
%type <Ast.exprp> exprp
%type <Ast.exprp list> exprsp
%type <Ast.cmd list> cmds
%type <Ast.cmd list> prog
%type <Ast.typ> type
%type <Ast.typs> types
%type <Ast.def> def
%type <Ast.arg> arg
%type <Ast.arg list> args
%type <Ast.argp> argp
%type <Ast.argp list> argsp

%start prog

%%
prog: LBRA cmds RBRA    { $2 }
;

block: LBRA cmds RBRA   { ASTBlock($2) }
;

cmds:
  stat                  { [ASTStat $1] }
| def PVERG cmds        { ASTDec($1)::$3 }
| stat PVERG cmds       { ASTStat($1)::$3 }
;

type: 
  INT                            { Int }
| BOOL                           { Bool }
| LPAR types ARROW type RPAR     { ASTTypeFunc($2, $4) }
;

types:
  type                           { ASTType($1) }
| type STAR types                { ASTTypes($1, $3) }
;

arg:
  IDENT DPOINTS type             { ASTArg($1, $3) }

args:
  arg                           { [$1] }
| arg VIRGULE args              { $1::$3 }

argp:
  IDENT DPOINTS type            { ASTArgp($1, $3) }
| VARP IDENT DPOINTS type       { ASTArgpVar($2, $4) }

argsp:
  argp                          { [$1] }
| argp VIRGULE argsp            { $1::$3 }
;

expr:
  NUM                           { ASTNum($1) }
| IDENT                         { ASTId($1) }
| TRUE                          { ASTBool(true) }
| FALSE                         { ASTBool(false) }
| LPAR IF expr expr expr RPAR   { ASTIf($3, $4, $5) }
| LPAR AND expr expr RPAR       { ASTAnd($3, $4) }
| LPAR OR expr expr RPAR        { ASTOr($3, $4) }
| LPAR ADD expr expr RPAR       { ASTBinary(Ast.ADD, $3, $4) }
| LPAR SUB expr expr RPAR       { ASTBinary(Ast.SUB, $3, $4) }
| LPAR MUL expr expr RPAR       { ASTBinary(Ast.MUL, $3, $4) }
| LPAR DIV expr expr RPAR       { ASTBinary(Ast.DIV, $3, $4) }
| LPAR EQ expr expr RPAR        { ASTBinary(Ast.EQ, $3, $4) }
| LPAR LT expr expr RPAR        { ASTBinary(Ast.LT, $3, $4) }
| LPAR NOT expr RPAR            { ASTUnary(Ast.NOT, $3) }
| LPAR expr exprs RPAR          { ASTApp($2, $3) }
| LBRA args RBRA expr           { ASTArgs($2, $4) }
;

exprs :
  expr                          { [$1] }
| expr exprs                    { $1::$2 }
;

exprp:
  expr                          { ASTExprp($1) }
| LPAR ADR expr RPAR            { ASTExprpAdr($3) }
;

exprsp:
  exprp                         { [$1] }
| exprp exprsp                  { $1::$2 }
;

stat:
  ECHO expr             { ASTEcho($2) }
| SET IDENT expr        { ASTSet($2, $3) }
| WHILE expr block      { ASTWhile($2, $3)}
| CALL expr exprsp      { ASTCall($2, $3) }
| IFB expr block block  { ASTIfb($2, $3, $4) }
;

def:
  CONST IDENT type expr                  { ASTConst($2, $3, $4) }
| FUN IDENT type LBRA args RBRA expr     { ASTFun($2, $3, $5, $7) }
| FUN REC IDENT type LBRA args RBRA expr { ASTFunRec($3, $4, $6, $8) }
| VAR IDENT type                         { ASTVar($2, $3) }
| PROC IDENT LBRA argsp RBRA block       { ASTProc($2, $4, $6) }
| PROC REC IDENT LBRA argsp RBRA block   { ASTProcRec($3, $5, $7) }
;