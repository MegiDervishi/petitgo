all: pgo

pgo:
	dune build ./src/main.exe 
	ln -f -s ./_build/default/src/main.exe pgo

.PHONY: tests
tests: pgo
	$(MAKE) -C tests
clean:
	rm pgo
	dune clean

%.s: %.go pgo
	./pgo -v $<

%.exe: %.s
	gcc -no-pie -g $< -o $@
	$@


	
