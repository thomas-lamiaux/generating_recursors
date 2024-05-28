all: Makefile.coq
	$(MAKE) -f Makefile.coq
	for file in recursors_named/tests/*.out; do mv -- "$$file" "$${file%.out}.v"; done

install: all
	$(MAKE) -f Makefile.coq install

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
	rm -f recursors_named/tests/*

clean-tests:
	rm -f recursors_named/tests/*

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq
