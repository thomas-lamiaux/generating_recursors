From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.

From PluginNestedElim Require Import unit_tests.
From PluginNestedElim Require Import nesting_param.


(* ################################################# *)
(* MetaRocq Examples                                   *)

Unset Elimination Schemes.

Definition term_ind := term_forall_list_ind.

Redirect "unit_tests/tests/08_01_term_custom" MetaRocq Run (print_rec "term").
Redirect "unit_tests/tests/08_01_term_gen"  MetaRocq Run (generate E term).

Definition red1_ind := red1_ind_all.

(* Print red1.
Print typing. *)

(* Bugs: Issue with let in ?  *)
Redirect "unit_tests/tests/08_02_red1_custom" MetaRocq Run (print_rec "red1").
Redirect "unit_tests/tests/08_02_red1_gen"  MetaRocq Run (generate E red1).


(* Bugs : Issue with flags *)
From MetaRocq.Common Require Import config.
Variable (x : checker_flags).
Existing Instance x.

Redirect "unit_tests/tests/08_03_typing_custom" MetaRocq Run (print_rec "typing").
Redirect "unit_tests/tests/08_03_typing_gen"  MetaRocq Run (generate E typing).

Print judgment.

(* Print typing.  *)
