From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.

From PluginNestedElim Require Import unit_tests.
From PluginNestedElim Require Import nesting_param.


(* nb_uparams: 0 *)
Inductive nu_list (A : Type) : Type :=
| nu_nil : nu_list A
| nu_cons : nu_list (A * A) -> nu_list A.

Inductive nu_list_param1 A : nu_list A -> Type :=
| nu_nil_param1 : nu_list_param1 A (nu_nil A)
| nu_cons_param1 : forall l, nu_list_param1 (A * A) l ->
                    nu_list_param1 A (nu_cons A l).

MetaRocq Run (tmMsg "01/08 nu_list").
Redirect "plugin_nested_eliminators/UnitTests/tests/05_01_nu_list_coq" MetaRocq Run (print_rec "nu_list" ).
Redirect "plugin_nested_eliminators/UnitTests/tests/05_01_nu_list_gen" MetaRocq Run (generate [] nu_list).

(* nb_uparams: 1 *)
Inductive mixed1 (A B C : Type) : Type :=
| mc11 : mixed1 A B C
| mc12 : mixed1 A nat C -> mixed1 A B C.

Inductive mixed1_param1 A (PA : A -> Prop) B C : mixed1 A B C -> Type :=
| mc11_param1 : mixed1_param1 A PA B C (mc11 A B C)
| mc12_param1 : forall x, mixed1_param1 A PA nat C x ->
                mixed1_param1 A PA B C (mc12 A B C x).

MetaRocq Run (tmMsg "02/08 mixed1").
Redirect "plugin_nested_eliminators/UnitTests/tests/05_02_mixed1_coq" MetaRocq Run (print_rec "mixed1" ).
Redirect "plugin_nested_eliminators/UnitTests/tests/05_02_mixed1_gen" MetaRocq Run (generate [] mixed1).

(* nb_uparams: 0 *)
Inductive mixed2 (A B C : Type) : Type :=
| mc21 : mixed2 A bool C -> mixed2 A B C
| mc22 : mixed2 nat B C -> mixed2 A B C.

Inductive mixed2_param1 A B C : mixed2 A B C -> Type :=
| mc21_param1 : forall x, mixed2_param1 A bool C x ->
                mixed2_param1 A B C (mc21 A B C x)
| mc22_param1 : forall x, mixed2_param1 nat B C x ->
                mixed2_param1 A B C (mc22 A B C x).

MetaRocq Run (tmMsg "03/08 mixed2").
Redirect "plugin_nested_eliminators/UnitTests/tests/05_03_mixed2_coq" MetaRocq Run (print_rec "mixed2" ).
Redirect "plugin_nested_eliminators/UnitTests/tests/05_03_mixed2_gen" MetaRocq Run (generate [] mixed2).

(* nb_uparams: 0 *)
Inductive mixed3 (A B C D : Type) : Type :=
| mc31 : mixed3 A B C bool -> nat -> mixed3 A B C D
| mc32 : mixed3 A B nat D -> nat -> mixed3 A B C D
| mc33 : nat -> mixed3 A B bool D -> mixed3 A B C D
| mc34 : mixed3 nat B C D -> mixed3 A B C D -> mixed3 A B C D
| mc35 : mixed3 A nat C D -> mixed3 B A C D -> mixed3 A B C D.

Inductive mixed3_param1 (A B C D : Type) : mixed3 A B C D -> Type :=
| mc31_param1 : forall x, mixed3_param1 A B C bool x ->
                forall n,
                mixed3_param1 A B C D (mc31 A B C D x n)
| mc32_param1 : forall x, mixed3_param1 A B nat D x ->
                forall n,
                mixed3_param1 A B C D (mc32 A B C D x n)
| mc33_param1 : forall n,
                forall x, mixed3_param1 A B bool D x ->
                mixed3_param1 A B C D (mc33 A B C D n x)
| mc34_param1 : forall x, mixed3_param1 nat B C D x ->
                forall y, mixed3_param1 A B C D y ->
                mixed3_param1 A B C D (mc34 A B C D x y)
| mc35_param1 : forall x, mixed3_param1 A nat C D x ->
                forall y, mixed3_param1 B A C D y ->
                mixed3_param1 A B C D (mc35 A B C D x y).

MetaRocq Run (tmMsg "04/08 mixed3").
Redirect "plugin_nested_eliminators/UnitTests/tests/05_04_mixed3_coq" MetaRocq Run (print_rec "mixed3" ).
Redirect "plugin_nested_eliminators/UnitTests/tests/05_04_mixed3_gen" MetaRocq Run (generate [] mixed3).

(* nb_uparams: 0 *)
Inductive nu_vec (n : nat) : Type :=
| vnil_pa : nu_vec n
| vcons_pa : nu_vec (S n) -> nu_vec n.

Inductive nu_vec_param1 (n : nat) : nu_vec n -> Type :=
| vnil_pa_param1 : nu_vec_param1 n (vnil_pa n)
| vcons_pa_param1 : forall nv, nu_vec_param1 (S n) nv ->
                    nu_vec_param1 n (vcons_pa n nv).

MetaRocq Run (tmMsg "05/08 nu_vec").
Redirect "plugin_nested_eliminators/UnitTests/tests/05_05_nu_vec_coq" MetaRocq Run (print_rec "nu_vec").
Redirect "plugin_nested_eliminators/UnitTests/tests/05_05_nu_vec_gen" MetaRocq Run (generate [] nu_vec).

(* nb_uparams: 0 *)
Inductive nu_ftree A : Type :=
| fleaf : A -> nu_ftree A
| fnode : (nat -> nu_ftree (A * A)) -> nu_ftree A.

Inductive nu_ftree_param1 A : nu_ftree A -> Type :=
| fleaf_param1 : forall a, nu_ftree_param1 A (fleaf A a)
| fnode_param1 : forall f, (forall n, nu_ftree_param1 (A * A) (f n)) ->
                 nu_ftree_param1 A (fnode A f).

MetaRocq Run (tmMsg "06/08 nu_ftree").
Redirect "plugin_nested_eliminators/UnitTests/tests/05_06_ftree_coq" MetaRocq Run (print_rec "nu_ftree").
Redirect "plugin_nested_eliminators/UnitTests/tests/05_06_ftree_gen" MetaRocq Run (generate [] nu_ftree).

(* nb_uparams: 0 *)
Inductive nu_ftree2 A : Type :=
| fleaf2 : A -> nu_ftree2 A
| fnode2 : (nat -> bool -> nu_ftree2 (A * A)) -> nu_ftree2 A.

Inductive nu_ftree2_param1 A : nu_ftree2 A -> Type :=
| fleaf1_param1 : forall a, nu_ftree2_param1 A (fleaf2 A a)
| fnode1_param1 : forall f, (forall n b, nu_ftree2_param1 (A * A) (f n b)) ->
                 nu_ftree2_param1 A (fnode2 A f).

MetaRocq Run (tmMsg "07/08 nu_ftree2").
Redirect "plugin_nested_eliminators/UnitTests/tests/05_07_ftree2_coq" MetaRocq Run (print_rec "nu_ftree2").
Redirect "plugin_nested_eliminators/UnitTests/tests/05_07_ftree2_gen" MetaRocq Run (generate [] nu_ftree2).

(* nb_uparams : 3 *)
(* strpos : [false, false, true] *)
Inductive All2i {A B : Type} (R : nat -> A -> B -> Type) (n : nat) : list A -> list B -> Type :=
	| All2i_nil : All2i R n [] []
  | All2i_cons : forall (a : A) (b : B) (lA : list A) (lB : list B),
                 R n a b -> All2i R (S n) lA lB -> All2i R n (a :: lA) (b :: lB).

Inductive All2i_param1 {A B : Type} (R : nat -> A -> B -> Type) (PR : forall n a b, R n a b -> Prop)
              (n : nat) : forall (lA : list A) (lB : list B), All2i R n lA lB -> Prop :=
| All2i_nil_param1 : All2i_param1 R PR n [] [] (All2i_nil R n)
| All2i_cons_param1 : forall (a : A) (b : B) (lA : list A) (lB : list B),
                      forall (r : R n a b), PR n a b r ->
                      forall (al : All2i R (S n) lA lB), All2i_param1 R PR (S n) lA lB al ->
                      All2i_param1 R PR n (a :: lA) (b :: lB) (All2i_cons R n a b lA lB r al).

MetaRocq Run (tmMsg "08/08 All2i").
Redirect "plugin_nested_eliminators/UnitTests/tests/05_08_All2i_coq" MetaRocq Run (print_rec "All2i").
Redirect "plugin_nested_eliminators/UnitTests/tests/05_08_All2i_gen" MetaRocq Run (generate Ep (@All2i)).