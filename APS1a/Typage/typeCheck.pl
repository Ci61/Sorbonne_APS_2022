assoc(X, [(X,T)|_], T).
assoc(X, [(X,ref(T))|_], T).
assoc(X, [argpVar(X,T)|_], ref(T)).
assoc(X, [argpVar(X,T)|_], T).
assoc(X, [_|B], T) :- 
   assoc(X, B, T).

/* Prog */
typeProg(prog(Cmds), void) :-
    typeCmds([], Cmds, void).

/* Instruction */
typeStat(G, echo(X), void) :-
    typeExpr(G, X, int).

typeStat(G, set(X, E), void) :-
    assoc(X, G, ref(T)),
    typeExpr(G, E, T).

typeStat(G, while(E, B), void) :-
    typeExpr(G, E, bool),
    typeBlock(G, B, void).

typeStat(G, appel(E, ES), void) :-
    typeExprp(G, E, typeFunc(TS, void)),
    typeExprps(G, ES, TS). 

typeStat(G, ifb(E, B1, B2), void) :-
    typeExpr(G, E, bool),
    typeBlock(G, B1, void),
    typeBlock(G, B2, void).

/* Block */
typeBlock(G, block(Cmds), void) :-
    typeCmds(G, Cmds, void).

/* definitions */
/*Recuperer le type de chaque element de la liste d'arguments*/
typeArg([], []).
typeArg([(_,T)|ARGS], [T|RES]) :-
    typeArg(ARGS,RES).
    
typeArg([argpVar(_,T)|ARGS], [ref(T)|RES]) :-
    typeArg(ARGS,RES).


/* var */
isRef(bool).
isRef(int).

/* const */
typeDef(G, const(X, T, E), [(X,T)|G]) :- 
    typeExpr(G, E, T).

/* fun */
typeDef(G, fun(X, T, ARGS, E), [(X,typeFunc(TS, T))|G]) :-
    append(ARGS, G, G2),
    typeArg(ARGS, TS), 
    typeExpr(G2, E, T).

/* fun rec */
typeDef(G, funRec(X, T, ARGS, E), G3) :-
    typeArg(ARGS, TS), 
    append(ARGS, G, G2),
    G3 = [(X,typeFunc(TS, T))|G2],
    typeExpr(G3, E, T).

typeDef(G, var(X, T), [(X, ref(T))|G]):-
    isRef(T).

/* proc */
typeDef(G, proc(X, ARGS, B), [(X,typeFunc(TS, void))|G]) :-
    append(ARGS, G, G2),
    typeArg(ARGS, TS), 
    typeBlock(G2, B, void).

/* proc rec */
typeDef(G, procRec(X, ARGS, B), G3) :-
    typeArg(ARGS, TS), 
    append(ARGS, G, G2),
    G3 = [(X,typeFunc(TS, void))|G2],
    typeBlock(G3, B, void).

/* Suite de commandes */
/* end */
typeCmds(_, [], void).

/* defs */
typeCmds(G, [stat(X)|Y], void) :-
    typeStat(G, X, void),
    typeCmds(G, Y, void).

typeCmds(G, [def(X)|Y], G2) :-
    typeDef(G, X, Env),
    typeCmds(Env, Y, G2).

/* Expressions */
/* Application */
typeExprs(_, [], []).

typeExprs(G, [E|ES], [T|TS]) :-
    typeExpr(G, E, T),
    typeExprs(G, ES, TS).

/* bool */
typeExpr(_, true, bool). 
    
typeExpr(_, false, bool). 

/* num */
typeExpr(_, num(N), int) :- 
    integer(N).

/* ident */
typeExpr(G, id(X), T) :- 
    assoc(X, G, T).

typeExpr(G, id(X), T) :- 
    assoc(X, G, ref(T)).

/* if */
typeExpr(G, if(Cond, Cons, Alter), T) :-
    typeExpr(G, Cond, bool),
    typeExpr(G, Cons, T),
    typeExpr(G, Alter, T).

/* and */
typeExpr(G, and(X,Y), bool) :-
    typeExpr(G, X, bool),
    typeExpr(G, Y, bool).

/* or */
typeExpr(G, or(X,Y), bool) :-
    typeExpr(G, X, bool),
    typeExpr(G, Y, bool).

/* binary */
typeExpr(G, add(X,Y), int) :-
    typeExpr(G, X, int),
    typeExpr(G, Y, int).

typeExpr(G, sub(X,Y), int) :-
    typeExpr(G, X, int),
    typeExpr(G, Y, int).

typeExpr(G, mul(X,Y), int) :-
    typeExpr(G, X, int),
    typeExpr(G, Y, int).

typeExpr(G, div(X,Y), int) :-
    typeExpr(G, X, int),
    typeExpr(G, Y, int).

typeExpr(G, eq(X,Y), bool) :-
    typeExpr(G, X, int),
    typeExpr(G, Y, int).

typeExpr(G, lt(X,Y), bool) :-
    typeExpr(G, X, int),
    typeExpr(G, Y, int).


/* unary */
typeExpr(G, not(X), bool) :-
    typeExpr(G, X, bool).

/* app */
typeExpr(G, app(E,ES), T) :-
    typeExpr(G, E, typeFunc(TS, T)),
    typeExprs(G, ES, TS). 

/* abs */
typeExpr(G, args(ARGS,E), typeFunc(_, T)) :-
    append(ARGS, G, G2),
    typeExpr(G2, E, T).


/* exprp */

typeExprp(G, X, T) :- 
    typeExpr(G, X, T).

/* ref */
typeExprp(G, adr(X), T) :- 
    typeExpr(G, X, T).

typeExprps(_, [], []).

typeExprps(G, [E|ES], [T|TS]) :-
    typeExprp(G, E, T),
    typeExprps(G, ES, TS).

%
typeCheck(P,ok) :- typeProg(P,void).
typeCheck(_,ko).    


%
exitCode(ok) :- halt(0).
exitCode(_) :- halt(1).

%
main_stdin :-
    read(user_input,T),
    typeCheck(T,R),
    print(R),
    nl,
    exitCode(R).
