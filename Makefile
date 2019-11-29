CMO=main.cmo
#go_lexer.cmo go_parser.cmo main.cmo
GENERATED = 
# go_lexer.ml go_parser.ml go_parser.mli
FLAGS=-annot -g

all: petitgo
	cd tests && ./test -n ../petitgo

.PHONY: tests
tests: petitgo
	bash run-tests

petitgo: $(CMO)
	ocamlc $(FLAGS) -o $@ nums.cma $(CMO)

.SUFFIXES: .mli .ml .cmi .cmo .mll .mly

.mli.cmi:
	ocamlc $(FLAGS) -c  $<

.ml.cmo:
	ocamlc $(FLAGS) -c $<

.mll.ml:
	ocamllex $<

.mly.ml:
	menhir -v $<

.mly.mli:
	menhir -v $<

clean:
	rm -f *.cm[io] *.o *.annot *~ petitgo $(GENERATED)
	rm -f go_parser.output go_parser.automaton

go_parser.ml: go_ast.cmi

.depend depend:$(GENERATED)
	rm -f .depend
	ocamldep *.ml *.mli > .depend

include .depend



