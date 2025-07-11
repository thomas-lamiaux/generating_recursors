From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.

From NamedAPI Require Import unit_tests.
From NamedAPI Require Import nesting_param.

MetaRocq Run (tmMsg "01/10 t11 strpos uprams").

(* [false]  *)
(* Basic *)
Inductive non_strpos (A : Type) : Type :=
| nstrpos1 : non_strpos A
| nstrpos2 : (A -> non_strpos A) -> non_strpos A.

MetaRocq Run (tmMsg "01/10 non_strpos").
Redirect "UnitTests/tests/11_01_non_strpos_coq" MetaRocq Run (print_rec "non_strpos" ).
Redirect "UnitTests/tests/11_01_non_strpos_gen" MetaRocq Run (generate Ep non_strpos).

(* [false, false] *)
(* Alllowed nesting *)
Inductive non_strpos2 (A B : Type) : Type :=
| nstrpos21 : non_strpos2 A B
| nstrpos22 : (A -> (list B) -> non_strpos2 A B) -> non_strpos2 A B.

MetaRocq Run (tmMsg "02/10 non_strpos2").
Redirect "UnitTests/tests/11_02_non_strpos_coq" MetaRocq Run (print_rec "non_strpos2" ).
Redirect "UnitTests/tests/11_02_non_strpos_gen" MetaRocq Run (generate Ep non_strpos2).

(* [false, false] *)
Inductive non_strpos3 (A B : Type) : Type :=
| nstrpos31 : B -> non_strpos3 A B
| nstrpos32 : (A -> B -> A * B -> False) -> non_strpos3 A B.

MetaRocq Run (tmMsg "03/10 non_strpos3").
Redirect "UnitTests/tests/11_03_non_strpos_coq" MetaRocq Run (print_rec "non_strpos3" ).
Redirect "UnitTests/tests/11_03_non_strpos_gen" MetaRocq Run (generate Ep non_strpos3).

(* [false, true, true] *)
(* Allowed nesting but left *)
Inductive non_strpos4 (A B C : Type) : Type :=
| nstrpos41 : A -> non_strpos4 A B C
| nstrpos42 : C -> (list A -> False) -> non_strpos4 A B C.

MetaRocq Run (tmMsg "04/10 non_strpos4").
Redirect "UnitTests/tests/11_04_non_strpos_coq" MetaRocq Run (print_rec "non_strpos4" ).
Redirect "UnitTests/tests/11_04_non_strpos_gen" MetaRocq Run (generate Ep non_strpos4).

(* [true, true]  *)
(* Left allowed + nesting *)
Inductive non_strpos5 (A B : Type) : Type :=
| nstrpos51 : A -> non_strpos5 A B
| nstrpos52 : (nat -> A) -> non_strpos5 A B.

MetaRocq Run (tmMsg "05/10 non_strpos5").
Redirect "UnitTests/tests/11_05_non_strpos_coq" MetaRocq Run (print_rec "non_strpos5" ).
Redirect "UnitTests/tests/11_05_non_strpos_gen" MetaRocq Run (generate Ep non_strpos5).

(* [false, false, false] *)
(* Application but not nesting *)
Inductive non_strpos6 (A : Type) (f : nat -> Type -> Type) (n : nat) : Type :=
| nstrpos61 : n = 0 -> non_strpos6 A f n
| nstrpos62 : (nat -> f n A) -> non_strpos6 A f n.

MetaRocq Run (tmMsg "06/10 non_strpos6").
Redirect "UnitTests/tests/11_06_non_strpos_coq" MetaRocq Run (print_rec "non_strpos6" ).
Redirect "UnitTests/tests/11_06_non_strpos_gen" MetaRocq Run (generate Ep non_strpos6).

(* [true, false, false] *)
(* Nesting not allowed       *)
Inductive non_strpos7 (A B : Type) (n : nat) : Type :=
| nstrpos71 : n = 0 -> non_strpos7 A B n
| nstrpos72 : A -> Nstrpos B -> non_strpos7 A B n.

MetaRocq Run (tmMsg "07/10 non_strpos7").
Redirect "UnitTests/tests/11_07_non_strpos_coq" MetaRocq Run (print_rec "non_strpos7" ).
Redirect "UnitTests/tests/11_07_non_strpos_gen" MetaRocq Run (generate Ep non_strpos7).

(* [true, true, false] *)
Inductive non_strpos8 (A B : Type) (n : nat) : Type :=
| nstrpos81 : n = 0 -> non_strpos8 A B n
| nstrpos82 : A -> list B -> non_strpos8 A B n.

MetaRocq Run (tmMsg "08/10 non_strpos8").
Redirect "UnitTests/tests/11_08_non_strpos_coq" MetaRocq Run (print_rec "non_strpos8" ).
Redirect "UnitTests/tests/11_08_non_strpos_gen" MetaRocq Run (generate Ep non_strpos8).

(* [false, true, false] *)
(* Nesting on a nuparams => not allowed *)
Inductive non_strpos9 (A B : Type) (n : nat) : Type :=
| nstrpos91 : n = 0 -> non_strpos9 A B n
| nstrpos92 : A -> mixed1 B A nat -> non_strpos9 A B n.

MetaRocq Run (tmMsg "09/10 non_strpos9").
Redirect "UnitTests/tests/11_09_non_strpos_coq" MetaRocq Run (print_rec "non_strpos9" ).
Redirect "UnitTests/tests/11_09_non_strpos_gen" MetaRocq Run (generate Ep non_strpos9).

(* Nesting on indices is not allowed *)
MetaRocq Run (tmMsg "10/10 eq").
Redirect "UnitTests/tests/11_10_eq_coq" MetaRocq Run (print_rec "eq" ).
Redirect "UnitTests/tests/11_10_eq_gen" MetaRocq Run (generate Ep (@eq)).
