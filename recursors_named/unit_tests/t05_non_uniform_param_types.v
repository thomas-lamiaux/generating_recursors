From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import All.

Require Import unit_tests.

Inductive nu_vec (n : nat) : Type :=
| vnil_pa : nu_vec n
| vcons_pa : nu_vec (S n) -> nu_vec n.

Redirect "recursors_named/tests/05_01_nu_vec_coq" MetaCoq Run (print_rec "nu_vec").
Redirect "recursors_named/tests/05_01_nu_vec_gen" MetaCoq Run (gen_rec [] <% nu_vec %>).

Inductive nu_list (A : Type) : Type :=
| nil_pa : nu_list A
| cons_pa : nu_list (A * A) -> nu_list A.

Redirect "recursors_named/tests/05_02_nu_list_coq" MetaCoq Run (print_rec "nu_list" ).
Redirect "recursors_named/tests/05_02_nu_list_gen" MetaCoq Run (gen_rec [] <% nu_list %>).

Inductive mixed1 (A B C : Type) : Type :=
| mnil1_pa : mixed1 A B C
| mcons1_pa : mixed1 A nat C -> mixed1 A B C.

(* Print mixed1_ind. *)

Redirect "recursors_named/tests/05_03_mixed1_coq" MetaCoq Run (print_rec "mixed1" ).
Redirect "recursors_named/tests/05_03_mixed1_gen" MetaCoq Run (gen_rec [] <% mixed1 %>).

Inductive mixed2 (A B C : Type) : Type :=
| mnil2_pa : mixed2 A bool C -> mixed2 A B C
| mcons2_pa : mixed2 nat B C -> mixed2 A B C.

Redirect "recursors_named/tests/05_04_mixed2_coq" MetaCoq Run (print_rec "mixed2" ).
Redirect "recursors_named/tests/05_04_mixed2_gen" MetaCoq Run (gen_rec [] <% mixed2 %>).

Inductive nu_nested (A B C : Type) : Type :=
| nnil_pa : nu_nested A B C -> nu_nested A B C
| ncons_pa : list (nat * (nu_nested bool B C)) -> nu_nested A B C.

Redirect "recursors_named/tests/05_05_nu_nested_coq" MetaCoq Run (print_rec "nu_nested" ).
Redirect "recursors_named/tests/05_05_nu_nested_gen" MetaCoq Run (gen_rec [] <% nu_nested %>).