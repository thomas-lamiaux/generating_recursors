From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.

From RecNamed Require Import unit_tests.

(* ################################################# *)
(* 2. Mutual : NO / Parameters : YES / Indices : NO *)

(* List *)
Redirect "recursors_named/unit_tests/tests/02_01_list_coq" MetaRocq Run (print_rec "list").
Redirect "recursors_named/unit_tests/tests/02_01_list_gen" MetaRocq Run (gen_rec [] <% list %>).

(* Prod *)
Redirect "recursors_named/unit_tests/tests/02_02_prod_coq" MetaRocq Run (print_rec "prod").
Redirect "recursors_named/unit_tests/tests/02_02_prod_gen" MetaRocq Run (gen_rec [] <% prod %>).

(* Sum *)
Redirect "recursors_named/unit_tests/tests/02_03_sum_coq" MetaRocq Run (print_rec "sum").
Redirect "recursors_named/unit_tests/tests/02_03_sum_gen" MetaRocq Run (gen_rec [] <% sum %>).

(* Prod4 *)
Inductive prod4 (A B C D : Set) : Set :=
| cst : A -> B -> C -> D -> prod4 A B C D.

Redirect "recursors_named/unit_tests/tests/02_04_prod4_coq" MetaRocq Run (print_rec "prod4").
Redirect "recursors_named/unit_tests/tests/02_04_prod4_gen" MetaRocq Run (gen_rec [] <% prod4 %>).