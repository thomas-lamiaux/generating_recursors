From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import All.

Require Import unit_tests.

(* nat *)
Inductive nat_param1 : nat -> Type :=
| z_param1 : nat_param1 0
| S_param1 : forall n, nat_param1 n -> nat_param1 (S n).

Definition nat_param1_term : forall (x : nat), nat_param1 x :=
  nat_rec nat_param1 z_param1 (fun n => S_param1 n ).

MetaCoq Run (get_paramE "nat").


(* list  *)
Inductive list_param1 A (P : A -> Type) : list A -> Type :=
| nil_param1 : list_param1 A P (@nil A)
| cons_param1 : forall a, P a -> forall l, list_param1 A P l -> list_param1 A P (cons a l).

Definition list_param1_term A (P : A -> Type) (HP : forall r : A, P r) (l : list A) : list_param1 A P l :=
  list_rect (list_param1 A P)
            (nil_param1 A P)
            (fun a l0 IHl => cons_param1 A P a (HP a) l0 IHl) l.

MetaCoq Run (get_paramE "list").


(* prod *)
Inductive prod_param1 A (PA : A -> Type) B (PB : B -> Type) : A * B -> Type :=
| pair_param1 : forall a, PA a -> forall b, PB b -> prod_param1 A PA B PB (pair a b).

Definition prod_param1_term A (PA : A -> Type) (HPA : forall a : A, PA a)
                            B (PB : B -> Type) (HPB : forall b : B, PB b)
                            : forall (x : A * B), prod_param1 A PA B PB x :=
  prod_rect (prod_param1 A PA B PB)
            (fun a b => pair_param1 A PA B PB a (HPA a) b (HPB b)).

MetaCoq Run (get_paramE "prod").


(* vec *)
Inductive vec A : nat -> Type :=
| vnil : vec A 0
| vcons : A -> forall n, vec A n -> vec A (S n).

Inductive vec_param1 A (P : A -> Type) : forall n, nat_param1 n -> vec A n -> Type :=
| vnil_param1 : vec_param1 A P 0 z_param1 (@vnil A)
| vcons_param1 :    forall a, P a
                 -> forall n, forall ne : nat_param1 n,
                    forall v, vec_param1 A P n ne v
                 -> vec_param1 A P (S n) (S_param1 n ne) (vcons _ a n v).

Definition vec_param1_term A (PA : A -> Type) (HPA : forall a : A, PA a)
            n v : vec_param1 A PA n (nat_param1_term n) v.
  apply (vec_rect A (fun n v => vec_param1 A PA n (nat_param1_term n) v)).
  - apply vnil_param1.
  - intros a n0 v0 Hv0. apply vcons_param1. apply HPA. exact Hv0.
  Defined.

MetaCoq Run (get_paramE "vec").


(* Nested indices *)
Inductive NL A : list A -> Type :=
| NLnil : NL A (@nil A)
| NLcons : forall (a : A), forall l, NL A l -> NL A (cons a l).

Inductive NL_param1 A (P : A -> Type) : forall l, list_param1 A P l -> NL A l -> Type :=
| NLnil_param1 : NL_param1 A P (@nil A) (nil_param1 A P) (@NLnil A)
| NLcons_param1 : forall a, forall (HA : P a),
                   forall l, forall le : list_param1 A P l,
                   forall NL, NL_param1 A P l le NL
                   -> NL_param1 A P (cons a l) (cons_param1 A P a HA l le) (NLcons A a l NL).

Definition NL_param1_term A (PA : A -> Type) (HPA : forall a : A, PA a)
            l x : NL_param1 A PA l (list_param1_term _ _ HPA l) x.
  revert x. revert l.
  fix NL_param1_term 2.
  intros l x. destruct x; cbn.
  - apply NLnil_param1.
  - apply NLcons_param1. apply NL_param1_term.
  Qed.

MetaCoq Run (get_paramE "NL").

(* NUlist *)
Inductive NUlist A : Type :=
| NUnil : NUlist A
| NUcons : A -> NUlist (A * A) -> NUlist A.

(* list  *)
Inductive NUlist_param1 A (P : forall (A : Type), A -> Type) : NUlist A -> Type :=
| NUnil_param1 : NUlist_param1 A P (NUnil A)
| NUcons_param1 : forall (a : A), P A a ->
                  forall (l : NUlist (A*A)), NUlist_param1 (A * A) P l ->
                  NUlist_param1 A P (NUcons A a l).

Definition NUlist_param1_term (P : forall (A : Type), A -> Type)
            (HPA : forall A a, P A a) A (l : NUlist A) : NUlist_param1 A P l.
  revert l. revert A. fix NL_param1_term 2.
  intros A l; destruct l; cbn.
  - apply NUnil_param1.
  - apply NUcons_param1. apply HPA. apply NL_param1_term.
Qed.

MetaCoq Run (get_paramE "NUlist").


(* Nesting context *)
Definition E := [kmpnat; kmplist; kmpprod ; kmpvec ; kmpNL ; kmpNUlist].
