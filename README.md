# Generating Recursors

This repository contains a small project in progress to generate recursors for mutual inductive types and verify that the terms generated as the proper types.

The files are stored in `recursors/` and corresponds to :

- `preliminary.v`
- `preprocess_debruijn_to_named` preprocess a mutual inductive type by naming each de Bruijn variables
- `postprocess_named_to_debruijn.v` to convert a named term made of forall all to one defined using de Bruijn variables
- `generate_rec_types_named.v` generates the type of the recursor of a mutual inductive type using named variables as a middle step.
WIP, it is currently only handle mutual inductive types with parameter but without indices nor nesting.
- `unit_tests.v` tests for `generate_rec_types_named.v`

The file `generate_rec_types_DeBruijn.v` is a non completed attempt to generates the type of the recursor of a mutual inductive type directly using de Bruijn variables.
It is currently not working, nor in the _CoqProject.