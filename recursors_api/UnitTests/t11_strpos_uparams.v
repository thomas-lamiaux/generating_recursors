From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import All.

From RecAPI Require Import unit_tests.
From RecAPI Require Import nesting_param.

MetaCoq Run (tmPrint "01/10 t11 strpos uprams").

(* [false]  *)
(* Basic *)
Inductive non_strpos (A : Type) : Type :=
| nstrpos1 : non_strpos A
| nstrpos2 : (A -> non_strpos A) -> non_strpos A.

MetaCoq Run (tmPrint "01/10 non_strpos").
Redirect "recursors_api/UnitTests/tests/11_01_non_strpos_coq" MetaCoq Run (print_rec "non_strpos" ).
Redirect "recursors_api/UnitTests/tests/11_01_non_strpos_gen" MetaCoq Run (gen_rec Ep non_strpos).

(* [false, false] *)
(* Alllowed nesting *)
Inductive non_strpos2 (A B : Type) : Type :=
| nstrpos21 : non_strpos2 A B
| nstrpos22 : (A -> (list B) -> non_strpos2 A B) -> non_strpos2 A B.

MetaCoq Run (tmPrint "02/10 non_strpos2").
Redirect "recursors_api/UnitTests/tests/11_02_non_strpos_coq" MetaCoq Run (print_rec "non_strpos2" ).
Redirect "recursors_api/UnitTests/tests/11_02_non_strpos_gen" MetaCoq Run (gen_rec Ep non_strpos2).

(* [false, false] *)
Inductive non_strpos3 (A B : Type) : Type :=
| nstrpos31 : B -> non_strpos3 A B
| nstrpos32 : (A -> B -> A * B -> False) -> non_strpos3 A B.

MetaCoq Run (tmPrint "03/10 non_strpos3").
Redirect "recursors_api/UnitTests/tests/11_03_non_strpos_coq" MetaCoq Run (print_rec "non_strpos3" ).
Redirect "recursors_api/UnitTests/tests/11_03_non_strpos_gen" MetaCoq Run (gen_rec Ep non_strpos3).

(* [false, true, true] *)
(* Allowed nesting but left *)
Inductive non_strpos4 (A B C : Type) : Type :=
| nstrpos41 : A -> non_strpos4 A B C
| nstrpos42 : C -> (list A -> False) -> non_strpos4 A B C.

MetaCoq Run (tmPrint "04/10 non_strpos4").
Redirect "recursors_api/UnitTests/tests/11_04_non_strpos_coq" MetaCoq Run (print_rec "non_strpos4" ).
Redirect "recursors_api/UnitTests/tests/11_04_non_strpos_gen" MetaCoq Run (gen_rec Ep non_strpos4).

(* [true, true]  *)
(* Left allowed + nesting *)
Inductive non_strpos5 (A B : Type) : Type :=
| nstrpos51 : A -> non_strpos5 A B
| nstrpos52 : (nat -> A) -> non_strpos5 A B.

MetaCoq Run (tmPrint "05/10 non_strpos5").
Redirect "recursors_api/UnitTests/tests/11_05_non_strpos_coq" MetaCoq Run (print_rec "non_strpos5" ).
Redirect "recursors_api/UnitTests/tests/11_05_non_strpos_gen" MetaCoq Run (gen_rec Ep non_strpos5).

(* [false, false, false] *)
(* Application but not nesting *)
Inductive non_strpos6 (A : Type) (f : nat -> Type -> Type) (n : nat) : Type :=
| nstrpos61 : n = 0 -> non_strpos6 A f n
| nstrpos62 : (nat -> f n A) -> non_strpos6 A f n.

MetaCoq Run (tmPrint "06/10 non_strpos6").
Redirect "recursors_api/UnitTests/tests/11_06_non_strpos_coq" MetaCoq Run (print_rec "non_strpos6" ).
Redirect "recursors_api/UnitTests/tests/11_06_non_strpos_gen" MetaCoq Run (gen_rec Ep non_strpos6).

(* [true, false, false] *)
(* Nesting not allowed       *)
Inductive non_strpos7 (A B : Type) (n : nat) : Type :=
| nstrpos71 : n = 0 -> non_strpos7 A B n
| nstrpos72 : A -> Nstrpos B -> non_strpos7 A B n.

MetaCoq Run (tmPrint "07/10 non_strpos7").
Redirect "recursors_api/UnitTests/tests/11_07_non_strpos_coq" MetaCoq Run (print_rec "non_strpos7" ).
Redirect "recursors_api/UnitTests/tests/11_07_non_strpos_gen" MetaCoq Run (gen_rec Ep non_strpos7).

(* [true, true, false] *)
Inductive non_strpos8 (A B : Type) (n : nat) : Type :=
| nstrpos81 : n = 0 -> non_strpos8 A B n
| nstrpos82 : A -> list B -> non_strpos8 A B n.

MetaCoq Run (tmPrint "08/10 non_strpos8").
Redirect "recursors_api/UnitTests/tests/11_08_non_strpos_coq" MetaCoq Run (print_rec "non_strpos8" ).
Redirect "recursors_api/UnitTests/tests/11_08_non_strpos_gen" MetaCoq Run (gen_rec Ep non_strpos8).

(* [false, true, false] *)
(* Nesting on a nuparams => not allowed *)
Inductive non_strpos9 (A B : Type) (n : nat) : Type :=
| nstrpos91 : n = 0 -> non_strpos9 A B n
| nstrpos92 : A -> mixed1 B A nat -> non_strpos9 A B n.

MetaCoq Run (tmPrint "09/10 non_strpos9").
Redirect "recursors_api/UnitTests/tests/11_09_non_strpos_coq" MetaCoq Run (print_rec "non_strpos9" ).
Redirect "recursors_api/UnitTests/tests/11_09_non_strpos_gen" MetaCoq Run (gen_rec Ep non_strpos9).

(* Nesting on indices is not allowed *)
MetaCoq Run (tmPrint "10/10 eq").
Redirect "recursors_api/UnitTests/tests/11_10_eq_coq" MetaCoq Run (print_rec "eq" ).
Redirect "recursors_api/UnitTests/tests/11_10_eq_gen" MetaCoq Run (gen_rec Ep (@eq)).
