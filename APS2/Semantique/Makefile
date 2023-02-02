# =============================================================================
# == UPMC/master/info/4I506 -- Janvier 2016/2017                            ===
# === SU/FSI/master/info/MU4IN503 -- Janvier 2020                           ===
# == Analyse des programmes et sémantiques                                  ===
# =============================================================================
# == Fichier: Makefile                                                      ===
# =============================================================================

CC = /usr/local/bin/ocamlc
FLAG = -c
YACC = /usr/local/bin/ocamlyacc
LEX = /usr/local/bin/ocamllex
I = -I ../Syntaxe

eval : ../Syntaxe/ast.cmo ../Syntaxe/parser.cmo ../Syntaxe/lexer.cmo eval.ml
	${CC} -o exeprog ${I} ast.cmo parser.cmo lexer.cmo eval.ml

clean :
	rm -f *~
	rm -f *.cmi *.cmo
	rm -f eval

.SUFFIXES : .mll .mly .mli .cmi .ml .cmo

.mly.ml : 
	$(YACC) $<

.mly.mli : 
	$(YACC) $<

.mll.ml : 
	$(LEX) $<

.ml.cmi : 
	$(CC) $(I) $(FLAG) $<

.mli.cmi : 
	$(CC) $(I) $(FLAG) $<

.ml.cmo : 
	$(CC) $(I) $(FLAG) $<
