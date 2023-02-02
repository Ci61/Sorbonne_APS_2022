(* ========================================================================== *)
(* == UPMC/master/info/4I506 -- Janvier 2016/2017/2018                     == *)
(* == SU/FSI/master/info/MU4IN503 -- Janvier 2020/2021/2022                == *)
(* == Analyse des programmes et sémantiques                                == *)
(* ========================================================================== *)
(* == hello-APS Syntaxe ML                                                 == *)
(* == Fichier: prologTerm.ml                                               == *)
(* ==  Génération de termes Prolog                                         == *)
(* ========================================================================== *)
open Ast

let print_operateursBi op =
  match op with
      ADD -> "add"
    | SUB -> "sub"
    | MUL -> "mul"
    | DIV -> "div"
    | EQ -> "eq"
    | LT -> "lt"
  
let print_operateursUn op =
  match op with
    | NOT -> "not"

let rec print_typ t =
  match t with 
      Int -> Printf.printf("int")
    | Bool -> Printf.printf("bool")
    | ASTTypeFunc(typs, typ) -> (
  Printf.printf("typeFunc");
  Printf.printf("(");
  Printf.printf("[") ;     
  print_typs typs;
  Printf.printf("]") ; 
  print_char ',';  
  print_typ typ ;  
  Printf.printf(")")
    )
    | ASTTypeVec(typ) -> (
  Printf.printf("typeVec");
  Printf.printf("(");
  print_typ typ ;  
  Printf.printf(")")
    )
and print_typs ts =
  match ts with
      ASTType(t) ->  print_typ t 
    | ASTTypes(typ, typs) -> (
  print_typ typ;
  print_char ',';
  print_typs typs
    )
(* print args normal *)
let print_arg a =
  match a with
      ASTArg(a,t) -> (
  Printf.printf("(");
  Printf.printf "%s" a;
  Printf.printf(",");
  print_typ t;
  Printf.printf(")");
    )

let rec print_args args =
  match args with
    [] -> ()
    | [a] -> print_arg a
    | a::ags -> (
  print_arg a;
  print_char ',';
  print_args ags;
      )

(* print args DANS PROC *)
let print_argp a =
  match a with
      ASTArgp(a,t) -> (
  Printf.printf("(");
  Printf.printf "%s" a;
  Printf.printf(",");
  print_typ t;
  Printf.printf(")");
    )
  | ASTArgpVar(a,t) -> (
  Printf.printf("argpVar");
  Printf.printf("(");
  Printf.printf "%s" a;
  Printf.printf(",");
  print_typ t;
  Printf.printf(")");
    )

let rec print_argsp args =
  match args with
    [] -> ()
    | [a] -> print_argp a
    | a::ags -> (
  print_argp a;
  print_char ',';
  print_argsp ags;
      )

let rec print_expr e =
  match e with
      ASTNum n -> Printf.printf"num(%d)" n
    | ASTId x -> Printf.printf"id(%s)" x
    | ASTBool(e) -> Printf.printf "%b" e
    | ASTIf(e1, e2, e3) -> (
  Printf.printf"if(";
  print_expr e1;
  Printf.printf",";
  print_expr e2;
  Printf.printf",";
  print_expr e3;
  Printf.printf")"     
      )
    | ASTAnd(e1, e2) -> (
  Printf.printf"and(";
  print_expr e1;
  Printf.printf",";
  print_expr e2;
  Printf.printf")"  
      )
    | ASTOr(e1, e2) -> (
  Printf.printf"or(";
  print_expr e1;
  Printf.printf",";
  print_expr e2;
  Printf.printf")"  
      )
    | ASTBinary(op, e1, e2) -> (
  Printf.printf "%s" (print_operateursBi op);
  Printf.printf"(";
  print_expr e1;
  Printf.printf",";
  print_expr e2;
  Printf.printf")"  
    )
    | ASTUnary(op, e) -> (
  Printf.printf "%s" (print_operateursUn op);
  Printf.printf"(";
  print_expr e;
  Printf.printf")"  
    )
    | ASTApp(e, es) -> (
	Printf.printf"app(";
	print_expr e;
	Printf.printf",[";
	print_exprs es;
	Printf.printf"])"
    )
    | ASTArgs(args, e) -> (
  Printf.printf"args(";
  Printf.printf"[";
  print_args args;
  Printf.printf"]";
  Printf.printf",";
  print_expr e;
  Printf.printf")"
    )
    | ASTLen(e) -> (
	Printf.printf"len(";
	print_expr e;
	Printf.printf")"
    )
    | ASTNth(e1, e2) -> (
  Printf.printf"nth(";
  print_expr e1;
  Printf.printf",";
  print_expr e2;
  Printf.printf")"  
      )
    | ASTAlloc(e) -> (
	Printf.printf"alloc(";
	print_expr e;
	Printf.printf")"
    )
    | ASTVset(e1, e2, e3) -> (
  Printf.printf"vset(";
  print_expr e1;
  Printf.printf",";
  print_expr e2;
  Printf.printf",";
  print_expr e3;
  Printf.printf")"  
      )
and print_exprs es =
  match es with
      [] -> ()
    | [e] -> print_expr e
    | e::es -> (
	print_expr e;
	print_char ',';
	print_exprs es
    )

let rec print_lval l = 
  match l with
    ASTLvId (x) -> Printf.printf"id(%s)" x
  | ASTLvVar(lv, e) -> (
  Printf.printf"nth(";
  print_lval lv;
  Printf.printf",";
  print_expr e;
  Printf.printf")"
    )

let rec print_exprp ep =
   match ep with
    ASTExprp (e) -> print_expr e
  | ASTExprpAdr (e) -> (
  Printf.printf"adr(";
  print_expr e;
  Printf.printf")"
  )
and print_exprsp es =
  match es with
      [] -> ()
    | [e] -> print_exprp e
    | e::es -> (
	print_exprp e;
	print_char ',';
	print_exprsp es
    )

let rec print_cmd c =
  match c with
      ASTStat s -> (
  Printf.printf("stat(");
  print_stat s;
  Printf.printf(")")
      )
    | ASTDec(d) ->  (
  Printf.printf("def(");
  print_def d;
  Printf.printf(")")
    )
and print_cmds cs =
  match cs with
    [] -> ()
    | [c] -> print_cmd c
    | c::cs -> (
  print_cmd c;
  print_char ',';
  print_cmds cs
      )
and print_stat s =
  match s with
      ASTEcho e -> (
	Printf.printf("echo(");
	print_expr(e);
	Printf.printf(")")
      )
    | ASTSet(i, e) -> (
  Printf.printf("set(");
  print_lval i;
  Printf.printf(",");
  print_expr(e);
  Printf.printf(")")
      )
    | ASTWhile(e, b) -> (
  Printf.printf("while(");
  print_expr(e);
  Printf.printf(",");
  print_block(b);
  Printf.printf(")")
      )
    | ASTCall(e, es) -> (
  Printf.printf("appel(");
  print_expr(e);
  Printf.printf(",[");
  print_exprsp(es);
  Printf.printf("])")
    )
    | ASTIfb(e, b1, b2) -> (
  Printf.printf"ifb(";
  print_expr e;
  Printf.printf",";
  print_block b1;
  Printf.printf",";
  print_block b2;
  Printf.printf")" 
    )
and print_block b =
  match b with
      ASTBlock(cs) -> (
  Printf.printf("block([");
  print_cmds cs;
  Printf.printf("])")
      )
and print_def d =
  match d with
      ASTConst(i, t, e) -> (
  Printf.printf("const(");
  Printf.printf "%s" i;
  Printf.printf(",");
  print_typ(t);
  Printf.printf(",");
  print_expr(e);
  Printf.printf(")")
      )
    | ASTFun(i, t, args, e) -> (
  Printf.printf("fun(");
  Printf.printf "%s" i;
  Printf.printf(",");
  print_typ(t);
  Printf.printf(",");
  Printf.printf"[";
  print_args args;
  Printf.printf"]";
  Printf.printf(",");
  print_expr(e);
  Printf.printf(")")
      )
    | ASTFunRec(i, t, args, e) -> (
  Printf.printf("funRec(");
  Printf.printf "%s" i;
  Printf.printf(",");
  print_typ(t);
  Printf.printf(",");
  Printf.printf"[";
  print_args args;
  Printf.printf"]";
  Printf.printf(",");
  print_expr(e);
  Printf.printf(")")
      )     
    | ASTVar(i, t) -> (
  Printf.printf("var(");
  Printf.printf "%s" i;
  Printf.printf(",");
  print_typ(t);
  Printf.printf(")")
      )
    | ASTProc(i, args, b) -> (
  Printf.printf("proc(");
  Printf.printf "%s" i;
  Printf.printf(",");
  Printf.printf"[";
  print_argsp args;
  Printf.printf"]";
  Printf.printf(",");
  print_block(b);
  Printf.printf(")")
      )
    | ASTProcRec(i, args, b) -> (
  Printf.printf("procRec(");
  Printf.printf "%s" i;
  Printf.printf(",");
  Printf.printf"[";
  print_argsp args;
  Printf.printf"]";
  Printf.printf(",");
  print_block(b);
  Printf.printf(")")
    )

      
 (*  | _ -> failwith "not yet implemented" *) 

let print_prog p =
  Printf.printf("prog([");
  print_cmds p;
  Printf.printf("])")

;;
	
let fname = Sys.argv.(1) in
let ic = open_in fname in
  try
    let lexbuf = Lexing.from_channel ic in
    let p = Parser.prog Lexer.token lexbuf in
      print_prog p;
      print_string ".\n"
  with Lexer.Eof ->
    exit 0
      
