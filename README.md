# Generating Recursors

This repository contains a small project in progress to generate recursors for inductive types.

- `preliminary.v`
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
  - [X] nested on param (no indices)
  - [ ] nested on param (has indices)
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
  - [X] nested on param (no indices)
  - [ ] nested on param (has indices)
  - [X] LetIn in args
  - [ ] rec call on LetIn
  - [ ] relevance
  - [ ] universe constrains
  - [ ] sort poly
- `unit_tests.v` provide a testing functions with different mode of testing and examples

There is then a folder of unit tests. It contains:
- `t01_basic_types`: basic inductive types like `bool` / `nat` etc...
- `t02_uniform_param_types`: inductive types with uniform parmeters like `list`
- `t03_indexed_param_types`: inductive types with indices like `vec`
- `t04_mutual_types`: basic mutual inductive types like `even` and `odd`
- `t05_uniform_param_types`: inductive types with non uniform parameters like `nu_list` :
```
Inductive nu_list (A : Type) : Type :=
| nu_nil : nu_list A
| nu_cons : nu_list (A * A) -> nu_list A.
```
- `t06_nested_types`: nested inductive types like `RoseTree`
- `t07_let_types`: inductive types with `let in` in the type of the constructors
- `t08_metacoq_types`: types from MetaCoq

