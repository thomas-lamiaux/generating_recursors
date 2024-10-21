all: Makefile.coq
	@+$(MAKE) -f Makefile.coq all
	for file in recursors_api/UnitTests/tests/*.out; do mv -- "$$file" "$${file%.out}.v"; done
	# for file in recursors_named/UnitTests/tests/*.out; do mv -- "$$file" "$${file%.out}.v"; done

install: all
	$(MAKE) -f Makefile.coq install

clean: Makefile.coq
	@+$(MAKE) -f Makefile.coq cleanall
	rm -f Makefile.coq
	rm -f recursors_api/UnitTests/tests/*
	# rm -f recursors_named/unit_tests/tests/*

clean-tests:
	rm -f recursors_api/UnitTests/tests/*
	# rm -f recursors_named/unit_tests/tests/*

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq
