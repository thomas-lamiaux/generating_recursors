all: Makefile.coq
	$(MAKE) -f Makefile.coq
	for file in tests/*.out; do mv -- "$$file" "$${file%.out}.v"; done

install: all
	$(MAKE) -f Makefile.coq install

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq

clean-test:
	rm -f tests/test_*.*

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq
