all: Makefile.coq
	@+$(MAKE) -f Makefile.coq all
	for file in plugin_nested_eliminators/UnitTests/tests/*.out; do mv -- "$$file" "$${file%.out}.v"; done
	# for file in eliminators_named/UnitTests/tests/*.out; do mv -- "$$file" "$${file%.out}.v"; done

install: all
	$(MAKE) -f Makefile.coq install

clean: Makefile.coq
	@+$(MAKE) -f Makefile.coq cleanall
	rm -f Makefile.coq
	rm -f plugin_nested_eliminators/UnitTests/tests/*
	# rm -f eliminators_named/unit_tests/tests/*

clean-tests:
	rm -f plugin_nested_eliminators/UnitTests/tests/*
	# rm -f eliminators_named/unit_tests/tests/*

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq
