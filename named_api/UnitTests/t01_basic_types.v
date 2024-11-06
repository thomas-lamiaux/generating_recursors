
From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import All.

From NamedAPI Require Import unit_tests.

(* ################################################# *)
(* 1. Mutual : NO / Parameters : NO / Indices : NO *)

Unset Elimination Schemes.

(* False *)
Definition False_ind (P : False -> Prop) : forall (x : False), P x.
Proof.
  fix rec 1. intro x. destruct x.
Defined.

Inductive False_param1 : False -> Prop := .

MetaCoq Run (tmMsg "01/08 False").
Redirect "UnitTests/tests/01_01_False_coq" MetaCoq Run (print_rec "False").
Redirect "UnitTests/tests/01_01_False_gen" MetaCoq Run (generate [] False).

Set Elimination Schemes.

(* True *)
Inductive True_param1 : True -> Prop :=
| I_param1 : True_param1 I.

MetaCoq Run (tmMsg "02/08 True").
Redirect "UnitTests/tests/01_02_True_coq" MetaCoq Run (print_rec "True").
Redirect "UnitTests/tests/01_02_True_gen" MetaCoq Run (generate [] True).

(* Bool *)
Inductive bool_param1 : bool -> Type :=
| true_param1 : bool_param1 true
| false_param1 : bool_param1 false.

MetaCoq Run (tmMsg "03/08 bool").
Redirect "UnitTests/tests/01_03_bool_coq" MetaCoq Run (print_rec "bool").
Redirect "UnitTests/tests/01_03_bool_gen" MetaCoq Run (generate [] bool).

(* Nat *)
Inductive nat_param1 : nat -> Type :=
| z_param1 : nat_param1 0
| S_param1 : forall n, nat_param1 n -> nat_param1 (S n).

MetaCoq Run (tmMsg "04/08 nat").
Redirect "UnitTests/tests/01_04_nat_coq" MetaCoq Run (print_rec "nat").
Redirect "UnitTests/tests/01_04_nat_gen" MetaCoq Run (generate [] nat).

(* Bnat *)
Inductive bnat : Type :=
| bO : bnat
| bS : bnat -> bnat -> bool -> bnat.

Inductive bnat_param1 : bnat -> Type :=
| bO_param1 : bnat_param1 bO
| bS_param1 : forall bn1, bnat_param1 bn1 ->
              forall bn2, bnat_param1 bn2 ->
              forall b, bnat_param1 (bS bn1 bn2 b).

MetaCoq Run (tmMsg "05/08 bnat").
Redirect "UnitTests/tests/01_05_bnat_coq" MetaCoq Run (print_rec "bnat").
Redirect "UnitTests/tests/01_05_bnat_gen" MetaCoq Run (generate [] bnat).

(* Infinitely branching tree *)
Inductive ftree : Type :=
| fleaf : ftree
| fnode : (nat -> ftree) -> ftree.

Inductive ftree_param1 : ftree -> Type :=
| fleaf_param1 : ftree_param1 fleaf
| fnode_param1 : forall f, (forall n, ftree_param1 (f n)) ->
                 ftree_param1 (fnode f).

MetaCoq Run (tmMsg "06/08 ftree").
Redirect "UnitTests/tests/01_06_ftree_coq" MetaCoq Run (print_rec "ftree").
Redirect "UnitTests/tests/01_06_ftree_gen" MetaCoq Run (generate [] ftree).

Inductive ftree2 : Type :=
| fleaf2 : ftree2
| fnode2 : (nat -> bool -> ftree2) -> ftree2.

Inductive ftree2_param1 : ftree2 -> Type :=
| fleaf_param2 : ftree2_param1 fleaf2
| fnode_param2 : forall f, (forall n b, ftree2_param1 (f n b)) ->
                 ftree2_param1 (fnode2 f).

MetaCoq Run (tmMsg "07/08 ftree2").
Redirect "UnitTests/tests/01_07_ftree2_coq" MetaCoq Run (print_rec "ftree2").
Redirect "UnitTests/tests/01_07_ftree2_gen" MetaCoq Run (generate [] ftree2).

Inductive nat2 : Type :=
| zero2 : nat2
| suc2 : nat2 -> nat2 -> nat2 -> nat2.

Inductive nat2_param1 : nat2 -> Type :=
| zero2_param1 : nat2_param1 zero2
| suc2_param1 : forall n1, nat2_param1 n1 ->
                forall n2, nat2_param1 n2 ->
                forall n3, nat2_param1 n3 ->
                nat2_param1 (suc2 n1 n2 n3).

MetaCoq Run (tmMsg "08/08 nat2").
Redirect "UnitTests/tests/01_08_nat2_coq" MetaCoq Run (print_rec "nat2").
Redirect "UnitTests/tests/01_08_nat2_gen" MetaCoq Run (generate [] nat2).