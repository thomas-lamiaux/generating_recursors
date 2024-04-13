# Generating Recursors

This repository contains a small project in progress to generate recursors for mutual inductive types and verify that the terms generated as the proper types.

The files are stored in `recursors/` and corresponds to :

- `preliminary.v`
- `named_to_debruijn.v` to convert a named term to one defined using de Bruijn variables
- `generate_rec_types_named.v` generates the type of the recursor of a mutual inductive type using named variables as a middle step (WIP)
- `generate_rec_types_DeBruijn.v` generates the type of the recursor of a mutual inductive type using de Bruinj variables. Currently not working. Not in the _CoqProject.
- `unit_tests.v` tests for `generate_rec_types_named.v`