open Ast;;

type valeur = InZ of int 
            | InF of expr * string list * env list 
            | InFR of expr * string * string list * env list 
            | InA of int
            | InP of block * string list * env list
            | InPR of block * string * string list * env list
and env = Couple of string * valeur 
type memoire = Mem of int * valeur ref

let rec in_env ident l =
    match l with
      [] -> false
    | Couple(str, _)::tl ->  if (String.equal str ident) then true else (in_env ident tl)

let rec chercher_env ident l =
    match l with
    | Couple(str, v)::tl ->  if (String.equal str ident) then v else (chercher_env ident tl)
    | _ -> failwith "erreur chercher_env"

let rec in_mem adr l =
    match l with
      [] -> false
    | Mem(a, _)::tl ->  if (a = adr) then true else (in_mem adr tl)

let rec chercher_mem adr l =
    match l with
    | Mem(a, v)::tl ->  if (a = adr) then v else (chercher_mem adr tl)
    | _ -> failwith "erreur chercher_mem"

let get_InZ v = 
    match v with
    | InZ(n) -> n
    | _ -> failwith "erreur get_InZ"

let prim1 op v =
    match op with
    | NOT -> if (get_InZ v) == 0 then InZ(1)
            else if (get_InZ v) == 1 then InZ(0)
            else failwith "erreur prim1"

let prim2 op v1 v2 =
    let inZ_v1 = (get_InZ v1) 
    and inZ_v2 = (get_InZ v2)
    in
    match op with
    | ADD -> InZ(inZ_v1 + inZ_v2)
    | SUB -> InZ(inZ_v1 - inZ_v2)
    | MUL -> InZ(inZ_v1 * inZ_v2)
    | DIV -> InZ(inZ_v1 / inZ_v2)
    | EQ -> if (inZ_v1 == inZ_v2) then InZ(1) else InZ(0)
    | LT -> if (inZ_v1 < inZ_v2) then InZ(1) else InZ(0)

let rec get_args l = 
    match l with
     [] -> []
    |ASTArg(str, _)::tl -> str::(get_args tl)

let rec get_argsp l = 
    match l with
     [] -> []
    |ASTArgp(str, _)::tl -> str::(get_argsp tl)
    |ASTArgpVar(str, _)::tl -> str::(get_argsp tl)

(*Expression*)
let rec calcul_expression expr env mem =
    match expr with
    |ASTNum(n) -> InZ(n)    
    |ASTId(x) -> if (in_env x env) then 
                        match (chercher_env x env) with
                        | InA(a) -> if (in_mem a mem) then 
                                    !(chercher_mem a mem)
                                    else failwith "adresse n'existe pas"
                        | v -> v
                 else failwith "ident n'existe pas"
    |ASTBool(b) -> if b then InZ(1) else InZ(0)
    |ASTUnary(x, e) -> prim1 x (calcul_expression e env mem) 
    |ASTBinary(x, e1, e2) -> prim2 x (calcul_expression e1 env mem)  (calcul_expression e2 env mem)
    |ASTIf(e1, e2, e3) -> if (calcul_expression e1 env mem) = InZ(1)
                            then (calcul_expression e2 env mem)
                            else (calcul_expression e3 env mem)
    |ASTAnd(e1, e2) -> if (calcul_expression e1 env mem) == InZ(0) 
                            then InZ(0) 
                            else (calcul_expression e2 env mem) 
    |ASTOr(e1, e2) -> if (calcul_expression e1 env mem) == InZ(1) 
                            then InZ(1) 
                            else (calcul_expression e2 env mem) 
    |ASTArgs(l, e) -> InF(e,get_args(l), env)
    |ASTApp(e, el) -> match (calcul_expression e env mem) with
                    | InF(e2, args, env2) ->
                        let new_env = env2@(assoc_arg_val args el env mem) in
                        calcul_expression e2 new_env mem
                    | InFR(e2, f, args, env2) ->
                        let new_env = env2@(assoc_arg_val args el env mem)@
                        [Couple(f, InFR(e2, f, args, env2))] in
                        calcul_expression e2 new_env mem
                    | _ -> failwith "erreur calcul_expression ASTApp"
and assoc_arg_val args el env mem = 
    match args,el with
    |[],[] -> []
    |arg::atl, e::etl -> Couple(arg, calcul_expression e env mem)::(assoc_arg_val atl etl env mem) 
    |_ -> failwith "erreur assoc_arg_val"

(*aps1a*)
let calcul_exprp ep env mem =
    match ep with 
      ASTExprp(e) -> calcul_expression e env mem
    | ASTExprpAdr(e)-> 
        begin
        match e with  
        |ASTId(x) -> if (in_env x env) then 
                            match (chercher_env x env) with
                            | InA(a) -> InA(a)
                            | v -> v
                    else failwith "ident n'existe pas"
        |_ -> failwith "ident n'existe pas"
        end

let rec assoc_arg_val_p args el env mem = 
    match args,el with
    |[],[] -> []
    |arg::atl, e::etl -> Couple(arg, calcul_exprp e env mem)::(assoc_arg_val_p atl etl env mem) 
    |_ -> failwith "erreur assoc_arg_val_p"



(*Definition*)
let alloc_indice = ref 0
let alloc mem = 
    let res = (!alloc_indice, Mem(!alloc_indice, ref (InZ(-1)))::mem) in
    alloc_indice := !alloc_indice + 1;
    res

let rec calcul_def expr env mem =
    match expr with
    | ASTConst(str, _, e) -> (Couple(str, (calcul_expression e env mem))::env, mem)
    | ASTFun(str, _, args, e) -> (Couple(str, InF(e, (get_args args), env))::env, mem)
    | ASTFunRec(str, _, args, e) -> (Couple(str, InFR(e, str, (get_args args), env))::env, mem)
    | ASTVar(str, _) -> let (adr, mem_prime) = (alloc mem) in 
                        (Couple(str, InA(adr))::env, mem_prime)
    | ASTProc(str, args, bk) -> (Couple(str, InP(bk, (get_argsp args), env))::env, mem)
    | ASTProcRec(str, args, bk) -> (Couple(str, InPR(bk, str, (get_argsp args), env))::env, mem)


(*Suites de commandes*)
let rec calcul_cmds cmds env mem flux = 
    match cmds with
    | [ASTStat(stat)] -> calcul_instr stat env mem flux
    | ASTDec(def)::tl -> let (new_env, new_mem) = calcul_def def env mem in
                        calcul_cmds tl new_env new_mem flux
    | ASTStat(stat)::tl -> let (new_mem, new_flux) = calcul_instr stat env mem flux in
                        calcul_cmds tl env new_mem new_flux
    | _ -> failwith "erreur calcul_cmds"
and calcul_block cmds env mem flux =
    match cmds with
    | ASTBlock(cs) -> calcul_cmds cs env mem flux
and calcul_instr stat env mem flux =
    match stat with
    | ASTEcho(e) -> (mem, get_InZ(calcul_expression e env mem)::flux)
    | ASTSet(x, e) ->  if (in_env x env) then 
                        begin
                            match (chercher_env x env) with
                            | InA(adr) -> 
                                let v = calcul_expression e env mem in
                                    if (in_mem adr mem) then 
                                        begin
                                            let v_pre = chercher_mem adr mem in
                                            v_pre := v;
                                            (mem,flux)
                                        end 
                                    else failwith "adresse n'existe pas"
                            | _ -> failwith "wrong valeur"
                        end
                       else failwith "ident n'existe pas"
    | ASTWhile(e, b) -> if (calcul_expression e env mem) = InZ(0)
                            then (mem,flux)
                            else 
                            begin
                                let (mem1,flux1) = calcul_block b env mem flux in
                                calcul_instr stat env mem1 flux1
                            end
    | ASTIfb(e, b1, b2) -> if (calcul_expression e env mem) = InZ(1)
                            then (calcul_block b1 env mem flux) 
                            else (calcul_block b2 env mem flux) 
    | ASTCall(e, el) -> begin
                    match (calcul_expression e env mem) with
                    | InP(bk, args, env2) ->
                        let new_env = env2@(assoc_arg_val_p args el env mem) in
                        calcul_block bk new_env mem flux
                    | InPR(bk, p, args, env2) ->
                        let new_env = env2@(assoc_arg_val_p args el env mem)@
                        [Couple(p, InPR(bk, p, args, env2))] in
                        calcul_block bk new_env mem flux
                    | _ -> failwith "erreur calcul_expression ASTApp"
                    end

let rec print_output output =
  List.iter (function x -> Printf.printf "%d\n" x) (List.rev output) 

(*Prog*)
let calcul_prog cs = let (mem, flux) = (calcul_cmds cs [] [] []) in
                    print_output flux;;

let fname = Sys.argv.(1) in
let ic = open_in fname in
  try
    let lexbuf = Lexing.from_channel ic in
    let p = Parser.prog Lexer.token lexbuf in
      calcul_prog p;
      print_string "\n"
  with Lexer.Eof ->
    exit 0