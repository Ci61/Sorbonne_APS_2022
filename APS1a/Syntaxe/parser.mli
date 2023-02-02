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

val prog :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Ast.cmd list
