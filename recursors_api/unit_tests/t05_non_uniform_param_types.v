From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import All.

From RecAPI Require Import unit_tests.


Inductive nu_list (A : Type) : Type :=
| nu_nil : nu_list A
| nu_cons : nu_list (A * A) -> nu_list A.

Redirect "recursors_api/unit_tests/tests/05_01_nu_list_coq" MetaCoq Run (print_rec "nu_list" ).
Redirect "recursors_api/unit_tests/tests/05_01_nu_list_gen" MetaCoq Run (gen_rec <% nu_list %>).

Inductive mixed1 (A B C : Type) : Type :=
| mc11 : mixed1 A B C
| mc12 : mixed1 A nat C -> mixed1 A B C.

Redirect "recursors_api/unit_tests/tests/05_02_mixed1_coq" MetaCoq Run (print_rec "mixed1" ).
Redirect "recursors_api/unit_tests/tests/05_02_mixed1_gen" MetaCoq Run (gen_rec <% mixed1 %>).

Inductive mixed2 (A B C : Type) : Type :=
| mc21 : mixed2 A bool C -> mixed2 A B C
| mc22 : mixed2 nat B C -> mixed2 A B C.

Redirect "recursors_api/unit_tests/tests/05_03_mixed2_coq" MetaCoq Run (print_rec "mixed2" ).
Redirect "recursors_api/unit_tests/tests/05_03_mixed2_gen" MetaCoq Run (gen_rec <% mixed2 %>).

Inductive mixed3 (A B C D : Type) : Type :=
| mc31 : mixed3 A B C bool -> nat -> mixed3 A B C D
| mc32 : mixed3 A B nat D -> nat -> mixed3 A B C D
| mc33 : nat -> mixed3 A B bool D -> mixed3 A B C D
| mc34 : mixed3 nat B C D -> mixed3 A B C D -> mixed3 A B C D
| mc35 : mixed3 A nat C D -> mixed3 B A C D -> mixed3 A B C D.

Redirect "recursors_api/unit_tests/tests/05_04_mixed3_coq" MetaCoq Run (print_rec "mixed3" ).
Redirect "recursors_api/unit_tests/tests/05_04_mixed3_gen" MetaCoq Run (gen_rec <% mixed3 %>).

Inductive nu_vec (n : nat) : Type :=
| vnil_pa : nu_vec n
| vcons_pa : nu_vec (S n) -> nu_vec n.

Redirect "recursors_api/unit_tests/tests/05_05_nu_vec_coq" MetaCoq Run (print_rec "nu_vec").
Redirect "recursors_api/unit_tests/tests/05_05_nu_vec_gen" MetaCoq Run (gen_rec <% nu_vec %>).

(* Inductive nu_let1 (A : Type) : Type :=
| nu_let1_nil : nu_let1 A
| nu_let1_cons : let x := A in nu_let1 x -> nu_let1 A.

Redirect "recursors_api/unit_tests/tests/05_06_nu_let1_coq" MetaCoq Run (print_rec "nu_let1").
Redirect "recursors_api/unit_tests/tests/05_06_nu_let1_gen" MetaCoq Run (gen_rec <% nu_let1 %>).

Inductive nu_let2 (A : Type) : Type :=
| nu_let2_nil : nu_let2 A
| nu_let2_cons : let x := A * A in nu_let2 x -> nu_let2 A.

Redirect "recursors_api/unit_tests/tests/05_07_nu_let2_coq" MetaCoq Run (print_rec "nu_let2").
Redirect "recursors_api/unit_tests/tests/05_07_nu_let2_gen" MetaCoq Run (gen_rec <% nu_let2 %>). *)

Inductive nu_nested (A B C : Type) : Type :=
| nu_nested_nil : A -> nu_nested A B C
| nu_nested_cons : list (nu_nested A (B * B) C) -> nu_nested A B C.

Redirect "recursors_api/unit_tests/tests/05_08_nu_nested_coq" MetaCoq Run (print_rec "nu_nested").
Redirect "recursors_api/unit_tests/tests/05_08_nu_nested_gen" MetaCoq Run (gen_rec <% nu_nested %>).