From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import All.

From RecAPI Require Import unit_tests.
From RecAPI Require Import nesting_param.


(* ################################################# *)
(* MetaCoq Examples                                   *)

Unset Elimination Schemes.

Definition term_ind := term_forall_list_ind.

Redirect "unit_tests/tests/08_01_term_custom" MetaCoq Run (print_rec "term").
Redirect "unit_tests/tests/08_01_term_gen"  MetaCoq Run (gen_rec E term).

Definition red1_ind := red1_ind_all.

(* Print red1.
Print typing. *)

(* Bugs: Issue with let in ?  *)
Redirect "unit_tests/tests/08_02_red1_custom" MetaCoq Run (print_rec "red1").
Redirect "unit_tests/tests/08_02_red1_gen"  MetaCoq Run (gen_rec E red1).


(* Bugs : Issue with flags *)
From MetaCoq.Common Require Import config.
Variable (x : checker_flags).
Existing Instance x.

Redirect "unit_tests/tests/08_03_typing_custom" MetaCoq Run (print_rec "typing").
Redirect "unit_tests/tests/08_03_typing_gen"  MetaCoq Run (gen_rec E typing).

Print judgment.

(* Print typing.  *)
