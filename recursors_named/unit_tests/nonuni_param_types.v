From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import All.

Require Import unit_tests.

(* parameter is actually an indice *)
Inductive vec_param (n : nat) : Type :=
| vnil_pa : vec_param n
| vcons_pa : vec_param (S n) -> vec_param n.

Redirect "recursors_named/tests/06_01_vec_param_coq" MetaCoq Run (print_rec "vec_param").
Redirect "recursors_named/tests/06_01_vec_param_gen" MetaCoq Run (gen_rec [] <% vec_param %>).

Inductive list_param (A : Type) : Type :=
| nil_pa : list_param A
| cons_pa : list_param (A * A) -> list_param A.

Print list_param_ind.

Redirect "recursors_named/tests/06_02_list_param_coq" MetaCoq Run (print_rec "list_param" ).
Redirect "recursors_named/tests/06_02_list_param_gen" MetaCoq Run (gen_rec [] <% list_param %>).

