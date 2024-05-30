From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import All.

Require Import unit_tests.

(* ################################################# *)
(* 2. Mutual : NO / Parameters : YES / Indices : NO *)

(* List *)
Redirect "recursors_named/tests/02_01_list_coq" MetaCoq Run (print_rec "list_ind").
Redirect "recursors_named/tests/02_01_list_gen" MetaCoq Run (gen_rec <% list %>).

(* Prod *)
Redirect "recursors_named/tests/02_02_prod_coq" MetaCoq Run (print_rec "prod_ind").
Redirect "recursors_named/tests/02_02_prod_gen" MetaCoq Run (gen_rec <% prod %>).

(* Sum *)
Redirect "recursors_named/tests/02_03_sum_coq" MetaCoq Run (print_rec "sum_ind").
Redirect "recursors_named/tests/02_03_sum_gen" MetaCoq Run (gen_rec <% sum %>).

(* Prod4 *)
Inductive prod4 (A B C D : Set) : Set :=
| cst : A -> B -> C -> D -> prod4 A B C D.

Redirect "recursors_named/tests/02_04_prod4_coq" MetaCoq Run (print_rec "prod4_ind").
Redirect "recursors_named/tests/02_04_prod4_gen" MetaCoq Run (gen_rec <% prod4 %>).