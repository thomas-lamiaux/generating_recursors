From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import All.

Require Import unit_tests.


Inductive nu_list (A : Type) : Type :=
| nu_nil : nu_list A
| nu_cons : nu_list (A * A) -> nu_list A.

Redirect "recursors_named/tests/05_01_nu_list_coq" MetaCoq Run (print_rec "nu_list" ).
Redirect "recursors_named/tests/05_01_nu_list_gen" MetaCoq Run (gen_rec [] <% nu_list %>).

Inductive mixed1 (A B C : Type) : Type :=
| mc11 : mixed1 A B C
| mc12 : mixed1 A nat C -> mixed1 A B C.

Redirect "recursors_named/tests/05_02_mixed1_coq" MetaCoq Run (print_rec "mixed1" ).
Redirect "recursors_named/tests/05_02_mixed1_gen" MetaCoq Run (gen_rec [] <% mixed1 %>).

Inductive mixed2 (A B C : Type) : Type :=
| mc21 : mixed2 A bool C -> mixed2 A B C
| mc22 : mixed2 nat B C -> mixed2 A B C.

Redirect "recursors_named/tests/05_03_mixed2_coq" MetaCoq Run (print_rec "mixed2" ).
Redirect "recursors_named/tests/05_03_mixed2_gen" MetaCoq Run (gen_rec [] <% mixed2 %>).

Inductive mixed3 (A B C D : Type) : Type :=
| mc31 : mixed3 A B C bool -> nat -> mixed3 A B C D
| mc32 : mixed3 A B nat D -> nat -> mixed3 A B C D
| mc33 : nat -> mixed3 A B bool D -> mixed3 A B C D
| mc34 : mixed3 nat B C D -> mixed3 A B C D -> mixed3 A B C D
| mc35 : mixed3 A nat C D -> mixed3 B A C D -> mixed3 A B C D.

Redirect "recursors_named/tests/05_04_mixed3_coq" MetaCoq Run (print_rec "mixed3" ).
Redirect "recursors_named/tests/05_04_mixed3_gen" MetaCoq Run (gen_rec [] <% mixed3 %>).

Inductive nu_vec (n : nat) : Type :=
| vnil_pa : nu_vec n
| vcons_pa : nu_vec (S n) -> nu_vec n.

Redirect "recursors_named/tests/05_05_nu_vec_coq" MetaCoq Run (print_rec "nu_vec").
Redirect "recursors_named/tests/05_05_nu_vec_gen" MetaCoq Run (gen_rec [] <% nu_vec %>).