From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import All.

From RecAPI Require Import unit_tests.


Inductive non_strpos (A : Type) : Type :=
| nstrpos1 : non_strpos A
| nstrpos2 : (A -> non_strpos A) -> non_strpos A.

Redirect "recursors_api/unit_tests/tests/11_01_non_strpos_coq" MetaCoq Run (print_rec "non_strpos" ).
Redirect "recursors_api/unit_tests/tests/11_01_non_strpos_gen" MetaCoq Run (gen_rec non_strpos).

Inductive non_strpos2 (A B : Type) : Type :=
| nstrpos21 : non_strpos2 A B
| nstrpos22 : (A -> (list B) -> non_strpos2 A B) -> non_strpos2 A B.

Redirect "recursors_api/unit_tests/tests/11_02_non_strpos_coq" MetaCoq Run (print_rec "non_strpos2" ).
Redirect "recursors_api/unit_tests/tests/11_02_non_strpos_gen" MetaCoq Run (gen_rec non_strpos2).

Inductive non_strpos3 (A B : Type) : Type :=
| nstrpos31 : B -> non_strpos3 A B
| nstrpos32 : (A -> B -> A * B -> False) -> non_strpos3 A B.

Redirect "recursors_api/unit_tests/tests/11_03_non_strpos_coq" MetaCoq Run (print_rec "non_strpos3" ).
Redirect "recursors_api/unit_tests/tests/11_03_non_strpos_gen" MetaCoq Run (gen_rec non_strpos3).

Inductive non_strpos4 (A B C : Type) : Type :=
| nstrpos41 : B -> non_strpos4 A B C
| nstrpos42 : C -> (list A -> False) -> non_strpos4 A B C.

Redirect "recursors_api/unit_tests/tests/11_04_non_strpos_coq" MetaCoq Run (print_rec "non_strpos4" ).
Redirect "recursors_api/unit_tests/tests/11_04_non_strpos_gen" MetaCoq Run (gen_rec non_strpos4).

Inductive non_strpos5 (A B : Type) : Type :=
| nstrpos51 : B -> non_strpos5 A B
| nstrpos52 : (nat -> A) -> non_strpos5 A B.

Redirect "recursors_api/unit_tests/tests/11_05_non_strpos_coq" MetaCoq Run (print_rec "non_strpos5" ).
Redirect "recursors_api/unit_tests/tests/11_05_non_strpos_gen" MetaCoq Run (gen_rec non_strpos5).

Inductive non_strpos6 (A : Type) (f : nat -> Type -> Type) (n : nat) : Type :=
| nstrpos61 : n = 0 -> non_strpos6 A f n
| nstrpos62 : (nat -> f n A) -> non_strpos6 A f n.

Redirect "recursors_api/unit_tests/tests/11_06_non_strpos_coq" MetaCoq Run (print_rec "non_strpos6" ).
Redirect "recursors_api/unit_tests/tests/11_06_non_strpos_gen" MetaCoq Run (gen_rec non_strpos6).