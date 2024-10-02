
From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import All.

From RecAPI Require Import unit_tests.

(* ################################################# *)
(* 1. Mutual : NO / Parameters : NO / Indices : NO *)

Unset Elimination Schemes.

Definition False_ind (P : False -> Prop) : forall (x : False), P x.
Proof.
  fix rec 1. intro x. destruct x.
Defined.

(* False *)
Redirect "recursors_api/unit_tests/tests/01_01_False_coq" MetaCoq Run (print_rec "False").
Redirect "recursors_api/unit_tests/tests/01_01_False_gen" MetaCoq Run (gen_rec [] False).

Set Elimination Schemes.

(* True *)
Redirect "recursors_api/unit_tests/tests/01_02_True_coq" MetaCoq Run (print_rec "True").
Redirect "recursors_api/unit_tests/tests/01_02_True_gen" MetaCoq Run (gen_rec [] True).

(* Bool *)
Redirect "recursors_api/unit_tests/tests/01_03_bool_coq" MetaCoq Run (print_rec "bool").
Redirect "recursors_api/unit_tests/tests/01_03_bool_gen" MetaCoq Run (gen_rec [] bool).

(* Nat *)
Redirect "recursors_api/unit_tests/tests/01_04_nat_coq" MetaCoq Run (print_rec "nat").
Redirect "recursors_api/unit_tests/tests/01_04_nat_gen" MetaCoq Run (gen_rec [] nat).

(* Bnat *)
Inductive bnat : Set :=
| bO : bnat
| bS : bnat -> bnat -> bool -> bnat.

Redirect "recursors_api/unit_tests/tests/01_05_bnat_coq" MetaCoq Run (print_rec "bnat").
Redirect "recursors_api/unit_tests/tests/01_05_bnat_gen" MetaCoq Run (gen_rec [] bnat).

(* Infinitely branching tree *)
Inductive ftree : Type :=
| fleaf : ftree
| fnode : (nat -> ftree) -> ftree.

Redirect "recursors_api/unit_tests/tests/01_06_ftree_coq" MetaCoq Run (print_rec "ftree").
Redirect "recursors_api/unit_tests/tests/01_06_ftree_gen" MetaCoq Run (gen_rec [] ftree).

Inductive ftree2 : Type :=
| fleaf2 : ftree2
| fnode2 : (nat -> bool -> ftree2) -> ftree2.

Redirect "recursors_api/unit_tests/tests/01_07_ftree2_coq" MetaCoq Run (print_rec "ftree2").
Redirect "recursors_api/unit_tests/tests/01_07_ftree2_gen" MetaCoq Run (gen_rec [] ftree2).

Inductive nat2 : Type :=
| zero2 : nat2
| suc2 : nat2 -> nat2 -> nat2 -> nat2.

Redirect "recursors_api/unit_tests/tests/01_08_nat2_coq" MetaCoq Run (print_rec "nat2").
Redirect "recursors_api/unit_tests/tests/01_08_nat2_gen" MetaCoq Run (gen_rec [] nat2).