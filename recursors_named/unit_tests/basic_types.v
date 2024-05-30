
From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import All.

Require Import unit_tests.

(* ################################################# *)
(* 1. Mutual : NO / Parameters : NO / Indices : NO *)

(* False *)
Redirect "recursors_named/tests/01_01_False_coq" MetaCoq Run (print_rec "False_ind").
Redirect "recursors_named/tests/01_01_False_gen" MetaCoq Run (gen_rec <% False %>).

(* True *)
Redirect "recursors_named/tests/01_02_True_coq" MetaCoq Run (print_rec "True_ind").
Redirect "recursors_named/tests/01_02_True_gen" MetaCoq Run (gen_rec <% True %>).

(* Bool *)
Redirect "recursors_named/tests/01_03_bool_coq" MetaCoq Run (print_rec "bool_ind").
Redirect "recursors_named/tests/01_03_bool_gen" MetaCoq Run (gen_rec <% bool %>).

(* Nat *)
Redirect "recursors_named/tests/01_04_nat_coq" MetaCoq Run (print_rec "nat_ind").
Redirect "recursors_named/tests/01_04_nat_gen" MetaCoq Run (gen_rec <% nat %>).

(* Bnat *)
Inductive bnat : Set :=
| bO : bnat
| bS : bnat -> bnat -> bool -> bnat.

Redirect "recursors_named/tests/01_05_bnat_coq" MetaCoq Run (print_rec "bnat_ind").
Redirect "recursors_named/tests/01_05_bnat_gen" MetaCoq Run (gen_rec <% bnat %>).