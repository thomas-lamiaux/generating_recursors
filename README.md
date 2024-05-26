# Generating Recursors

This repository contains a small project in progress to generate recursors for inductive types.

- `preliminary.v`
- `preprocess_debruijn_to_named.v` converts a `mutual_body` using debruijn variables
  to a fully named one
- `postprocess_named_to_debruijn.v` converts a named term to one
   defined using de ruijn variables
-  `generate_types.v` generates the types that are used for the term and type of
    the recursor
-
- `generate_rec_type.v` generates the type of the recursor of a mutual inductive type given a fully named mdecl. It handles:
  - [X] basics
  - [X] parameters
  - [X] indices
  - [X] mutual
  - [ ] nested
- `generate_rec_term.v` generates the type of the recursor of a mutual inductive type given a fully named mdecl. It handles:
  - [X] basics
  - [X] parameters
  - [X] indices
  - [X] mutual
  - [ ] nested
- `unit_tests.v` provide a testing functions with different mode of testing and examples
