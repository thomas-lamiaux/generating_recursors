all: Makefile.coq
	@+$(MAKE) -f Makefile.coq all
	for file in unit_tests/tests/*.out; do mv -- "$$file" "$${file%.out}.v"; done

install: all
	$(MAKE) -f Makefile.coq install

clean: Makefile.coq
	@+$(MAKE) -f Makefile.coq cleanall
	rm -f Makefile.coq
	rm -f unit_tests/tests/*

clean-tests:
	rm -f unit_tests/tests/*

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq
