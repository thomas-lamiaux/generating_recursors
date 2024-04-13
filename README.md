# generating_recursors

- `preliminary.v`
- `named_to_debruijn.v` to convert a named term to one defined using de Bruijn variables
- `generate_rec_types_named.v` generates the type of the recursor of a mutual inductive type using named variables as a middle step (WIP)
- `generate_rec_types_DeBruijn.v` generates the type of the recursor of a mutual inductive type using de Bruinj variables. Currently not working. Not in the _CoqProject.
- `unit_tests.v` tests for `generate_rec_types_named.v`