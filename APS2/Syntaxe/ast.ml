(* ========================================================================== *)
(* == UPMC/master/info/4I506 -- Janvier 2016/2017/2018                     == *)
(* == SU/FSI/master/info/MU4IN503 -- Janvier 2020/2021/2022                == *)
(* == Analyse des programmes et sémantiques                                == *)
(* ========================================================================== *)
(* == hello-APS Syntaxe ML                                                 == *)
(* == Fichier: ast.ml                                                      == *)
(* ==  Arbre de syntaxe abstraite                                          == *)
(* ========================================================================== *)

type bin = ADD | SUB | MUL | DIV | EQ | LT
type unary = NOT

type typ = 
    Bool | Int
  | ASTTypeFunc of typs * typ
  | ASTTypeVec of typ
and typs =
    ASTType of typ
  | ASTTypes of typ * typs
  
type arg = 
    ASTArg of string * typ

type argp = 
    ASTArgp of string * typ
  | ASTArgpVar of string * typ

type expr =
    ASTNum of int
  | ASTId of string
  | ASTBool of bool
  | ASTApp of expr * expr list
  | ASTIf of expr * expr * expr
  | ASTAnd of expr * expr
  | ASTOr of expr * expr
  | ASTBinary of bin * expr * expr
  | ASTUnary of unary * expr
  | ASTArgs of arg list * expr
  | ASTLen of expr
  | ASTNth of expr * expr
  | ASTAlloc of expr
  | ASTVset of expr * expr * expr

type exprp = 
    ASTExprp of expr
  | ASTExprpAdr of expr

type lval =
    ASTLvId of string
  | ASTLvVar of lval * expr

type cmd =
    ASTStat of stat
  | ASTDec of def
and stat =
    ASTEcho of expr
  | ASTSet of lval * expr
  | ASTWhile of expr * block
  | ASTCall of expr * exprp list
  | ASTIfb of expr * block * block
and block = 
  | ASTBlock of cmd list
and def = 
    ASTConst of string * typ * expr
  | ASTFun of string * typ * arg list * expr
  | ASTFunRec of string * typ * arg list * expr
  | ASTVar of string * typ
  | ASTProc of string * argp list * block
  | ASTProcRec of string * argp list * block



