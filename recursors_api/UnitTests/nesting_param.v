From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import All.

From RecAPI Require Import unit_tests.

(* nat *)
Inductive nat_param1 : nat -> Type :=
| z_param1 : nat_param1 0
| S_param1 : forall n, nat_param1 n -> nat_param1 (S n).

Definition nat_param1_term : forall (x : nat), nat_param1 x :=
  nat_rec nat_param1 z_param1 (fun n => S_param1 n ).

MetaCoq Run (get_paramEp nat []).


(* list  *)
Inductive list_param1 A (PA : A -> Type) : list A -> Type :=
| nil_param1 : list_param1 A PA (@nil A)
| cons_param1 : forall a, PA a -> forall l, list_param1 A PA l -> list_param1 A PA (cons a l).

Definition list_param1_term A (PA : A -> Type) (HPA : forall r : A, PA r) (l : list A) : list_param1 A PA l :=
  list_rect (list_param1 A PA)
            (nil_param1 A PA)
            (fun a l0 IHl => cons_param1 A PA a (HPA a) l0 IHl) l.

MetaCoq Run (get_paramEp list []).


(* prod *)
Inductive prod_param1 A (PA : A -> Type) B (PB : B -> Type) : A * B -> Type :=
| pair_param1 : forall a, PA a -> forall b, PB b -> prod_param1 A PA B PB (pair a b).

Definition prod_param1_term A (PA : A -> Type) (HPA : forall a : A, PA a)
                            B (PB : B -> Type) (HPB : forall b : B, PB b)
                            : forall (x : A * B), prod_param1 A PA B PB x :=
  prod_rect (prod_param1 A PA B PB)
            (fun a b => pair_param1 A PA B PB a (HPA a) b (HPB b)).

MetaCoq Run (get_paramEp prod []).


(* vec *)
Inductive vec A : nat -> Type :=
| vnil : vec A 0
| vcons : A -> forall n, vec A n -> vec A (S n).

Inductive vec_param1 A (P : A -> Type) : forall n, vec A n -> Type :=
| vnil_param1 : vec_param1 A P 0 (@vnil A)
| vcons_param1 :    forall a, P a
                 -> forall n,
                    forall v, vec_param1 A P n v
                 -> vec_param1 A P (S n) (vcons _ a n v).

Definition vec_param1_term A (PA : A -> Type) (HPA : forall a : A, PA a)
            n v : vec_param1 A PA n v :=
  vec_rect _ (fun n => vec_param1 A PA n)
              (vnil_param1 A PA)
              (fun a n v IHv => vcons_param1 A PA a (HPA a) n v IHv)
              n v.

MetaCoq Run (get_paramEp vec []).


(* Add the parametricty *)
Inductive eq_param1 (A : Type) (PA : A -> Type) (x : A) : forall y, @eq A x y -> Prop :=
  eq_refl_param1 : eq_param1 A PA x x (@eq_refl A x).

Definition eq_param1_term A PA (HPA: forall a, PA a) x :
  forall y p, eq_param1 A PA x y p.
Proof.
  intros y p; destruct p; constructor; try easy.
Defined.

MetaCoq Run (get_paramEp (@eq) []).


(* Non strict positive parameter *)
Inductive Nstrpos (A : Type) : Type :=
| Nstrpos1 : Nstrpos A
| Nstrpos2 : (A -> Nstrpos A) -> Nstrpos A.

Inductive Nstrpos_param1 (A : Type) : Nstrpos A -> Type :=
| Nstrpos1_param1 : Nstrpos_param1 A (Nstrpos1 A)
| Nstrpos2_param1 :forall f, Nstrpos_param1 A (Nstrpos2 A f).

Definition Nstrpos_param1_term A : forall x, Nstrpos_param1 A x.
Proof.
  intros x; induction x; constructor; try easy.
Defined.

MetaCoq Run (get_paramEp Nstrpos []).


(* A uniform parameters centered  *)
Inductive non_strpos10 (A B : Type) (n : nat) : Type :=
| nstrpos101 : n = 0 -> non_strpos10 A B n
| nstrpos102 : (A -> nat) -> list B -> non_strpos10 A B n.

Inductive non_strpos10_param1 (A B : Type) (PB : B -> Type) (n : nat) : non_strpos10 A B n -> Type :=
| nstrpos101_param1 : forall (x : n = 0), non_strpos10_param1 A B PB n (nstrpos101 A B n x)
| nstrpos102_param1 : forall (f : A -> nat),
                      forall l : list B, list_param1 _ PB l ->
                      non_strpos10_param1 A B PB n (nstrpos102 A B n f l).

Definition non_strpos10_param1_term A B PB (HPB: forall b, PB b) n :
  forall x, non_strpos10_param1 A B PB n x.
Proof.
  intro x; induction x; constructor; try easy. apply list_param1_term; easy.
Defined.

(* MetaCoq Run (get_paramEp non_strpos10 [kmp_list; kmp_eq]). *)
MetaCoq Run (get_paramEp non_strpos10 [kmp_list; kmp_eq]).


(* A non uniform prameters *)
Inductive mixed1 (A B C : Type) : Type :=
| mc11 : mixed1 A B C
| mc12 : mixed1 A nat C -> mixed1 A B C.

Inductive mixed1_param1 A (PA : A -> Prop) B C : mixed1 A B C -> Type :=
| mc11_param1 : mixed1_param1 A PA B C (mc11 A B C)
| mc12_param1 : forall x, mixed1_param1 A PA nat C x ->
                mixed1_param1 A PA B C (mc12 A B C x).

Definition mixed1_param1_term A PA (HPA : forall a, PA a) B C : forall x, mixed1_param1 A PA B C x.
Proof.
  intros x; induction x; constructor; try easy.
Defined.

MetaCoq Run (get_paramEp mixed1 []).


(* Nesting context *)
Definition Ep := [kmp_nat; kmp_list; kmp_prod ; kmp_vec; kmp_eq; kmp_Nstrpos; kmp_non_strpos10 ; kmp_mixed1].
