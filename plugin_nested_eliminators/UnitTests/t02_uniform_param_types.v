From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.

From PluginNestedElim Require Import unit_tests.

(* ################################################# *)
(* 2. Mutual : NO / Parameters : YES / Indices : NO *)

(* List *)
Inductive list_param1 A (PA : A -> Type) : list A -> Type :=
| nil_param1 : list_param1 A PA nil
| cons_param1 : forall a, PA a ->
                forall l, list_param1 A PA l ->
                list_param1 A PA (a::l).

MetaRocq Run (tmMsg "01/07 list").
Redirect "plugin_nested_eliminators/UnitTests/tests/02_01_list_coq" MetaRocq Run (print_rec "list").
Redirect "plugin_nested_eliminators/UnitTests/tests/02_01_list_gen" MetaRocq Run (generate [] list).

(* Prod *)
Inductive prod_param1 A (PA : A -> Type) B (PB : B -> Type) : prod A B -> Type :=
| pair_param1 : forall a, PA a -> forall b, PB b -> prod_param1 A PA B PB (pair a b).

MetaRocq Run (tmMsg "02/07 prod").
Redirect "plugin_nested_eliminators/UnitTests/tests/02_02_prod_coq" MetaRocq Run (print_rec "prod").
Redirect "plugin_nested_eliminators/UnitTests/tests/02_02_prod_gen" MetaRocq Run (generate [] prod).

(* Sum *)
Inductive sum_param1 A (PA : A -> Prop) B (PB : A -> Prop) : sum A B -> Type :=
| inl_param1 : forall a, PA a -> sum_param1 A PA B PB (inl a)
| inr_param1 : forall b, PB b -> sum_param1 A PA B PB (inl b).

MetaRocq Run (tmMsg "03/07 sum").
Redirect "plugin_nested_eliminators/UnitTests/tests/02_03_sum_coq" MetaRocq Run (print_rec "sum").
Redirect "plugin_nested_eliminators/UnitTests/tests/02_03_sum_gen" MetaRocq Run (generate [] sum).

(* Prod4 *)
Unset Elimination Schemes.

Inductive prod4 (A B C D : Type) : Type :=
| pair4 : A -> B -> C -> D -> prod4 A B C D.

Definition prod4_ind A B C D (P : prod4 A B C D -> Prop)
(f00 : forall a b c d, P (pair4 A B C D a b c d)) :=
  fix F (x : prod4 A B C D) : P x :=
  match x with
  | pair4 a b c d => f00 a b c d
  end.

Set Elimination Schemes.

Inductive prod4_param1 A (PA : A -> Prop) B (PB : B -> Prop) C (PC : C -> Prop) D (PD : D -> Prop) : prod4 A B C D -> Type :=
| pair4_param1 : forall a, PA a -> forall b, PB b ->
                 forall c, PC c -> forall d, PD d ->
                 prod4_param1 A PA B PB C PC D PD (pair4 A B C D a b c d).

MetaRocq Run (tmMsg "04/07 prod4").
Redirect "plugin_nested_eliminators/UnitTests/tests/02_04_prod4_coq" MetaRocq Run (print_rec "prod4").
Redirect "plugin_nested_eliminators/UnitTests/tests/02_04_prod4_gen" MetaRocq Run (generate [] prod4).

(* Infinitely branching tree *)
Inductive ftree (A : Type) : Type :=
| fleaf : A -> ftree A
| fnode : (nat -> ftree A) -> ftree A.

Inductive ftree_param1 A (PA : A -> Prop) : ftree A -> Type :=
| fleaf_param1 : forall a, PA a -> ftree_param1 A PA (fleaf A a)
| fnode_param1 : forall f, (forall n, ftree_param1 A PA (f n)) ->
                 ftree_param1 A PA (fnode A f).

MetaRocq Run (tmMsg "05/07 ftree").
Redirect "plugin_nested_eliminators/UnitTests/tests/02_05_ftree_coq" MetaRocq Run (print_rec "ftree").
Redirect "plugin_nested_eliminators/UnitTests/tests/02_05_ftree_gen" MetaRocq Run (generate [] ftree).

Inductive ftree2 (A : Type) : Type :=
| fleaf2 : A -> ftree2 A
| fnode2 : (nat -> bool -> ftree2 A) -> ftree2 A.

Inductive ftree2_param1 A (PA : A -> Prop) : ftree2 A -> Type :=
| fleaf2_param1 : forall a, PA a -> ftree2_param1 A PA (fleaf2 A a)
| fnode2_param1 : forall f, (forall n b, ftree2_param1 A PA (f n b)) ->
                 ftree2_param1 A PA (fnode2 A f).

MetaRocq Run (tmMsg "06/07 ftree2").
Redirect "plugin_nested_eliminators/UnitTests/tests/02_06_ftree2_coq" MetaRocq Run (print_rec "ftree2").
Redirect "plugin_nested_eliminators/UnitTests/tests/02_06_ftree2_gen" MetaRocq Run (generate [] ftree2).

Inductive tricky A : Type :=
| tricky1 : (bool -> A) -> tricky A.

Inductive tricky_param1 A (PA : A -> Type) : tricky A -> Type :=
| tricky1_param1 : forall f, (forall a, PA (f a)) -> tricky_param1 A PA (tricky1 A f).

MetaRocq Run (tmMsg "07/07 tricky").
Redirect "plugin_nested_eliminators/UnitTests/tests/02_07_tricky_coq" MetaRocq Run (print_rec "tricky").
Redirect "plugin_nested_eliminators/UnitTests/tests/02_07_tricky_gen" MetaRocq Run (generate [] tricky).
