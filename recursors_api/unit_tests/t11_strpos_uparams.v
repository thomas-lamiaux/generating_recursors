From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import All.

From RecAPI Require Import unit_tests.


(* [false]  *)
Inductive non_strpos (A : Type) : Type :=
| nstrpos1 : non_strpos A
| nstrpos2 : (A -> non_strpos A) -> non_strpos A.

Redirect "recursors_api/unit_tests/tests/11_01_non_strpos_coq" MetaCoq Run (print_rec "non_strpos" ).
Redirect "recursors_api/unit_tests/tests/11_01_non_strpos_gen" MetaCoq Run (gen_rec non_strpos).

(* [false, false] *)
Inductive non_strpos2 (A B : Type) : Type :=
| nstrpos21 : non_strpos2 A B
| nstrpos22 : (A -> (list B) -> non_strpos2 A B) -> non_strpos2 A B.

Redirect "recursors_api/unit_tests/tests/11_02_non_strpos_coq" MetaCoq Run (print_rec "non_strpos2" ).
Redirect "recursors_api/unit_tests/tests/11_02_non_strpos_gen" MetaCoq Run (gen_rec non_strpos2).

(* [false, false] *)
Inductive non_strpos3 (A B : Type) : Type :=
| nstrpos31 : B -> non_strpos3 A B
| nstrpos32 : (A -> B -> A * B -> False) -> non_strpos3 A B.

Redirect "recursors_api/unit_tests/tests/11_03_non_strpos_coq" MetaCoq Run (print_rec "non_strpos3" ).
Redirect "recursors_api/unit_tests/tests/11_03_non_strpos_gen" MetaCoq Run (gen_rec non_strpos3).

(* [false, true, true] *)
Inductive non_strpos4 (A B C : Type) : Type :=
| nstrpos41 : A -> non_strpos4 A B C
| nstrpos42 : C -> (list A -> False) -> non_strpos4 A B C.

Redirect "recursors_api/unit_tests/tests/11_04_non_strpos_coq" MetaCoq Run (print_rec "non_strpos4" ).
Redirect "recursors_api/unit_tests/tests/11_04_non_strpos_gen" MetaCoq Run (gen_rec non_strpos4).

(* [true, true]  *)
Inductive non_strpos5 (A B : Type) : Type :=
| nstrpos51 : A -> non_strpos5 A B
| nstrpos52 : (nat -> A) -> non_strpos5 A B.

Redirect "recursors_api/unit_tests/tests/11_05_non_strpos_coq" MetaCoq Run (print_rec "non_strpos5" ).
Redirect "recursors_api/unit_tests/tests/11_05_non_strpos_gen" MetaCoq Run (gen_rec non_strpos5).

(* [true, false, false] *)
Inductive non_strpos6 (A : Type) (f : nat -> Type -> Type) (n : nat) : Type :=
| nstrpos61 : n = 0 -> non_strpos6 A f n
| nstrpos62 : (nat -> f n A) -> non_strpos6 A f n.

Redirect "recursors_api/unit_tests/tests/11_06_non_strpos_coq" MetaCoq Run (print_rec "non_strpos6" ).
Redirect "recursors_api/unit_tests/tests/11_06_non_strpos_gen" MetaCoq Run (gen_rec non_strpos6).

(* [true, false, false] *)
Inductive non_strpos7 (A B : Type) (n : nat) : Type :=
| nstrpos71 : (*n = 0 ->*) non_strpos7 A B n
| nstrpos72 : A -> non_strpos B -> non_strpos7 A B n.

Redirect "recursors_api/unit_tests/tests/11_07_non_strpos_coq" MetaCoq Run (print_rec "non_strpos7" ).
Redirect "recursors_api/unit_tests/tests/11_07_non_strpos_gen" MetaCoq Run (gen_rec non_strpos7).

(* [true, true, false] *)
Inductive non_strpos8 (A B : Type) (n : nat) : Type :=
| nstrpos81 : n = 0 -> non_strpos8 A B n
| nstrpos82 : A -> list B -> non_strpos8 A B n.

Redirect "recursors_api/unit_tests/tests/11_08_non_strpos_coq" MetaCoq Run (print_rec "non_strpos8" ).
Redirect "recursors_api/unit_tests/tests/11_08_non_strpos_gen" MetaCoq Run (gen_rec non_strpos8).

Inductive mixed1 (A B C : Type) : Type :=
| mc11 : mixed1 A B C
| mc12 : mixed1 A nat C -> mixed1 A B C.

(* [false, true, false] *)
Inductive non_strpos9 (A B : Type) (n : nat) : Type :=
| nstrpos91 : n = 0 -> non_strpos9 A B n
| nstrpos92 : A -> mixed1 B A nat -> non_strpos9 A B n.

Redirect "recursors_api/unit_tests/tests/11_09_non_strpos_coq" MetaCoq Run (print_rec "non_strpos9" ).
Redirect "recursors_api/unit_tests/tests/11_09_non_strpos_gen" MetaCoq Run (gen_rec non_strpos9).