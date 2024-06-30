# Generating Recursors

This repository contains a small project in progress to generate recursors for inductive types.
- `recursors_named/` generating recursors using named variables
- `recursors_api/` generating recursors using an API to handle DeBruijn variables
- `unit_tests/` Several unit tests

### Content of `recursors_named`:
- `naming.v` naming functions and scheme for the named definition
- `commons.v` functions building terms common to many files
- `preprocess_parameters.v` computes uniform parameters and converts gather relevant
information
- `preprocess_debruijn_to_named.v` fully names the deburijn variables present in the interface
- `postprocess_named_to_debruijn.v` converts a named term to one
   defined using debruijn variables
- `generate_rec_call` computes rec call, if any, both for types and terms
- `generate_types.v` generates the types that are used for the term and type of
    the recursor
- `generate_rec_type.v` generates the type of the recursor of a mutual inductive type given a fully named mdecl. It handles:
  - [X] basics
  - [X] parameters
  - [X] indices
  - [X] mutual
  - [X] non uniform parameters
  - [X] nested on uparam (no other)
  - [ ] all nesting (but eq)
  - [X] LetIn in args
  - [ ] rec call on LetIn
  - [ ] relevance
  - [ ] universe constrains
  - [ ] sort poly
- `generate_rec_term.v` generates the type of the recursor of a mutual inductive type given a fully named mdecl. It handles:
  - [X] basics
  - [X] parameters
  - [X] indices
  - [X] mutual
  - [X] non uniform parameters
  - [X] nested on uparam (no other)
  - [ ] all nesting (but eq)
  - [X] LetIn in args
  - [ ] rec call on LetIn
  - [ ] relevance
  - [ ] universe constrains
  - [ ] sort poly

### Content of `recursors_api`:
- `commons.v` functions building terms common to many files
- `preprocess_parameters.v` computes uniform parameters and converts gather relevant
information
- `generate_rec_call` computes rec call, if any, both for types and terms
- `generate_types.v` generates the types that are used for the term and type of
    the recursor
- `generate_rec_type.v` generates the type of the recursor of a mutual inductive type given a fully named mdecl. It handles:
  - [X] basics
  - [X] parameters
  - [ ] indices    (Issues Eq)
  - [X] mutual
  - [X] non uniform parameters
  - [X] nested on uparam (no other)
  - [ ] all nesting (but eq)
  - [ ] LetIn in args
  - [ ] rec call on LetIn
  - [ ] relevance
  - [ ] universe constrains
  - [ ] sort poly
- `generate_rec_term.v` generates the type of the recursor of a mutual inductive type given a fully named mdecl. It handles:
  - [X] basics
  - [X] parameters
  - [X] indices
  - [X] mutual
  - [X] non uniform parameters
  - [X] nested on uparam (no other)
  - [ ] all nesting (but eq)
  - [X] LetIn in args
  - [ ] rec call on LetIn
  - [ ] relevance
  - [ ] universe constrains
  - [ ] sort poly

### Content of `unit-tests`:
- `unit_tests.v` provide a testing functions with different mode of testing
- `t01_basic_types`: basic inductive types like `bool` / `nat` etc...
- `t02_uniform_param_types`: inductive types with uniform parmeters like `list`
- `t03_indexed_param_types`: inductive types with indices like `vec`
- `t04_mutual_types`: basic mutual inductive types like `even` and `odd`
- `t05_uniform_param_types`: inductive types with non uniform parameters like `nu_list` :
- `t06_nested_types`: nested inductive types like `RoseTree`
- `t07_let_types`: inductive types with `let in` in the type of the constructors
- `t08_metacoq_types`: types from MetaCoq

