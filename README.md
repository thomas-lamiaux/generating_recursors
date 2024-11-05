# Generating Recursors

This repository contains a small project in progress to generate recursors for inductive types.
- `named_api/` generating recursors using an API to handle DeBruijn variables
- `recursors_named/` outdated folder, generating recursors fully using named variables


### Content of `recursors_api`:

#### API
- `api_debruijn` an api to deal with debruijn indices inspired from work by Weituo Dai and Yannick Forester

#### Preprocess
- `uniform_parameters.v` computes uniform parameters and converts gather relevant
information
  - [X] basic
  - [X] nesting
- `strictly_positive_uniform_parameters` computes strictly positive uniform parameters that one is allowed to nest on
  - [X] basic
  - [X] nesting

#### CustomParametricity
- `custom_parametricty_rec_call.v` generates the rec call for the custom parametricity
- `custom_parametricty.v` generates the custom parametricity of an inductive type as an inductive
- `fundamental_theorem.v` generates the type and term of the associated custom fundamental theorem

#### Recursors
- `commons.v` functions building terms common to many files
- `recursor_rec_call` computes rec call, if any, both for types and terms
- `recursor.v` generates the type and term of the recursors. It handles:
  - [X] basics + functions types in args
  - [X] parameters
  - [X] indices
  - [X] mutual
  - [X] non uniform parameters
  - [X] LetIn in args
  - [X] rec call needing reduction (including let in)
  - [X] nesting (provided plugins)
  - [ ] relevance
  - [ ] universe constrains

### Functoriality
- `functoriality.v` generates the type and term of the functoriality lemma

### UnitTests
- `unit_tests.v` provide a testing functions with different mode of testing
- `nesting_param.v` types used for nesting with their custom param and fundamental theorem
- `t01_basic_types`: basic inductive types like `bool` / `nat` etc...
- `t02_uniform_param_types`: inductive types with uniform parameters like `list`
- `t03_indexed_param_types`: inductive types with indices like `vec`
- `t04_mutual_types`: basic mutual inductive types like `even` and `odd`
- `t05_non_uniform_param_types`: inductive types with non uniform parameters like `nu_list` :
- `t06_nested_types`: nested inductive types like `RoseTree`
- `t07_let_types`: inductive types with `let in` in the type of the constructors
- `t08_metacoq_types`: inductive types from MetaCoq
- `t11_strpos_uparams`: inductive types with non-strictly positive parameters





### (Outdated) Content of `recursors_named`:
- `naming.v` naming functions and scheme for the named definition
- `commons.v` functions building terms common to many files
- `preprocess_parameters.v` computes uniform parameters and converts gather relevant
information
- `preprocess_debruijn_to_named.v` fully names the debruijn variables present in the interface
- `postprocess_named_to_debruijn.v` converts a named term to one
   defined using debruijn variables
- `generate_rec_call` computes rec call, if any, both for types and terms
- `generate_types.v` generates the types that are used for the term and type of
    the recursor
- `generate_rec_type.v` generates the type of the recursor of a mutual inductive type given a fully named mdecl. It handles:
  - [X] basics
  - [ ] basics + functions types in args
  - [X] parameters
  - [X] indices
  - [X] mutual
  - [X] non uniform parameters
  - [X] ad hoc nesting (all type uparams + nice enough)
  - [ ] nesting
  - [X] LetIn in args
  - [ ] rec call needing reduction (including let in)
  - [ ] relevance
  - [ ] universe constrains
  - [ ] sort poly
- `generate_rec_term.v` generates the type of the recursor of a mutual inductive type given a fully named mdecl. It handles:
  - [X] basics
  - [ ] basics + functions types in args
  - [X] parameters
  - [X] indices
  - [X] mutual
  - [X] non uniform parameters
  - [X] ad hoc nesting (all type uparams + nice enough + no fct)
  - [ ] nesting
  - [X] LetIn in args
  - [ ] rec call needing reduction (including let in)
  - [ ] relevance
  - [ ] universe constrains
  - [ ] sort poly
