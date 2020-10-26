CMO= smap_definer.cmo go_lexer.cmo go_parser.cmo graph.cmo go_typer.cmo x86_64.cmo compiler.cmo main.cmo
GENERATED = go_lexer.ml go_parser.ml go_parser.mli
FLAGS=-annot -g -bin-annot

all: pgo
	./pgo test.go
	gcc -g -no-pie test.s
	./a.out

.PHONY: tests
tests: pgo
	cd tests && ./test.sh -3 ../pgo -parse

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
	rm -f main.cmt graph.cmt go_typer.cmt compiler.cmt x86_64.cmt smap_definer.cmt
re: clean all

.depend depend:$(GENERATED)
	rm -f .depend
	ocamldep *.ml *.mli > .depend

include .depend



