CMO=go_lexer.cmo go_parser.cmo go_error.cmo graph.cmo go_typer.cmo main.cmo
GENERATED = go_lexer.ml go_parser.ml go_parser.mli
FLAGS=-annot -g -bin-annot

all: pgo
	./pgo test.go

.PHONY: tests
tests: pgo
	 cd tests && ./test.sh -2 ../pgo -parse

pgo: $(CMO)
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
	rm -f *.cm[io] *.cmt[io] *.o *.annot *~ pgo $(GENERATED)
	rm -f go_parser.output go_parser.automaton
	rm -f go_parser.conflicts go_parser.cmt main.cmt go_lexer.cmt
	rm -f main.cmt go_error.cmt graph.cmt go_typer.cmt

re: clean all

.depend depend:$(GENERATED)
	rm -f .depend
	ocamldep *.ml *.mli > .depend

include .depend



