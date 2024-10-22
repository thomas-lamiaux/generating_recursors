From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import All.

From RecAPI Require Import unit_tests.
From RecAPI Require Import nesting_param.

(* ################################################# *)
(* 2. Mutual : NO / Parameters : YES / Indices : NO *)

(* List *)
Inductive list_param1 A (PA : A -> Type) : list A -> Type :=
| nil_param1 : list_param1 A PA nil
| cons_param1 : forall a, PA a ->
                forall l, list_param1 A PA l ->
                list_param1 A PA (a::l).

Redirect "recursors_api/UnitTests/tests/02_01_list_coq" MetaCoq Run (print_rec "list").
Redirect "recursors_api/UnitTests/tests/02_01_list_gen" MetaCoq Run (gen_rec [] list).

(* Prod *)
Inductive prod_param1 A (PA : A -> Type) B (PB : B -> Type) : prod A B -> Type :=
| pair_param1 : forall a, PA a -> forall b, PB b -> prod_param1 A PA B PB (pair a b).

Redirect "recursors_api/UnitTests/tests/02_02_prod_coq" MetaCoq Run (print_rec "prod").
Redirect "recursors_api/UnitTests/tests/02_02_prod_gen" MetaCoq Run (gen_rec [] prod).

(* Sum *)
Inductive sum_param1 A (PA : A -> Prop) B (PB : A -> Prop) : sum A B -> Type :=
| inl_param1 : forall a, PA a -> sum_param1 A PA B PB (inl a)
| inr_param1 : forall b, PB b -> sum_param1 A PA B PB (inl b).

Redirect "recursors_api/UnitTests/tests/02_03_sum_coq" MetaCoq Run (print_rec "sum").
Redirect "recursors_api/UnitTests/tests/02_03_sum_gen" MetaCoq Run (gen_rec [] sum).

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

Redirect "recursors_api/UnitTests/tests/02_04_prod4_coq" MetaCoq Run (print_rec "prod4").
Redirect "recursors_api/UnitTests/tests/02_04_prod4_gen" MetaCoq Run (gen_rec [] prod4).

(* Infinitely branching tree *)
Inductive ftree (A : Type) : Type :=
| fleaf : A -> ftree A
| fnode : (nat -> ftree A) -> ftree A.

Inductive ftree_param1 A (PA : A -> Prop) : ftree A -> Type :=
| fleaf_param1 : forall a, PA a -> ftree_param1 A PA (fleaf A a)
| fnode_param1 : forall f, (forall n, ftree_param1 A PA (f n)) ->
                 ftree_param1 A PA (fnode A f).

Redirect "recursors_api/UnitTests/tests/02_05_ftree_coq" MetaCoq Run (print_rec "ftree").
Redirect "recursors_api/UnitTests/tests/02_05_ftree_gen" MetaCoq Run (gen_rec [] ftree).

Inductive ftree2 (A : Type) : Type :=
| fleaf2 : A -> ftree2 A
| fnode2 : (nat -> bool -> ftree2 A) -> ftree2 A.

Inductive ftree2_param1 A (PA : A -> Prop) : ftree2 A -> Type :=
| fleaf2_param1 : forall a, PA a -> ftree2_param1 A PA (fleaf2 A a)
| fnode2_param1 : forall f, (forall n b, ftree2_param1 A PA (f n b)) ->
                 ftree2_param1 A PA (fnode2 A f).

Redirect "recursors_api/UnitTests/tests/02_06_ftree2_coq" MetaCoq Run (print_rec "ftree2").
Redirect "recursors_api/UnitTests/tests/02_06_ftree2_gen" MetaCoq Run (gen_rec [] ftree2).

Inductive tricky1 A : Type :=
| tricky11 : A * A -> tricky1 A
| tricky12 : (list A) * A -> tricky1 A.

Inductive tricky1_param1 A (PA : A -> Prop) : tricky1 A -> Type :=
| tricky11_param1 : forall x, nesting_param.prod_param1 A (fun a => PA a) A (fun a => PA a) x ->
                   tricky1_param1 A PA (tricky11 A x)
| tricky12_param1 : forall x, prod_param1 (list A) (fun l => list_param1 A (fun a => PA a) l) A (fun a => PA a) x ->
            tricky1_param1 A PA (tricky12 A x).

Redirect "recursors_api/UnitTests/tests/02_07_tricky1_coq" MetaCoq Run (print_rec "tricky1").
(* BUGS ISSUE UNIVERSE LEVEL *)
(* Redirect "recursors_api/UnitTests/tests/02_07_tricky_gen" MetaCoq Run (gen_rec E tricky). *)

Inductive tricky2 A : Type :=
| tricky21 : (bool -> A) -> tricky2 A.

Inductive tricky2_param1 A (PA : A -> Type) : tricky2 A -> Type :=
| tricky21_param1 : forall f, (forall a, PA (f a)) -> tricky2_param1 A PA (tricky21 A f).

Redirect "recursors_api/UnitTests/tests/02_07_tricky1_coq" MetaCoq Run (print_rec "tricky1").
Redirect "recursors_api/UnitTests/tests/02_07_tricky_gen" MetaCoq Run (gen_rec E tricky2).
