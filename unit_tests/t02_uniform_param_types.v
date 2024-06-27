From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import All.

Require Import unit_tests.

(* ################################################# *)
(* 2. Mutual : NO / Parameters : YES / Indices : NO *)

(* List *)
Redirect "unit_tests/tests/02_01_list_coq" MetaCoq Run (print_rec "list").
Redirect "unit_tests/tests/02_01_list_gen" MetaCoq Run (gen_rec [] <% list %>).

(* Prod *)
Redirect "unit_tests/tests/02_02_prod_coq" MetaCoq Run (print_rec "prod").
Redirect "unit_tests/tests/02_02_prod_gen" MetaCoq Run (gen_rec [] <% prod %>).

(* Sum *)
Redirect "unit_tests/tests/02_03_sum_coq" MetaCoq Run (print_rec "sum").
Redirect "unit_tests/tests/02_03_sum_gen" MetaCoq Run (gen_rec [] <% sum %>).

(* Prod4 *)
Inductive prod4 (A B C D : Set) : Set :=
| cst : A -> B -> C -> D -> prod4 A B C D.

Redirect "unit_tests/tests/02_04_prod4_coq" MetaCoq Run (print_rec "prod4").
Redirect "unit_tests/tests/02_04_prod4_gen" MetaCoq Run (gen_rec [] <% prod4 %>).