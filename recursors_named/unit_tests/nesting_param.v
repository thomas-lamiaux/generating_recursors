From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import All.

Require Import unit_tests.

Inductive list_param1 A (P : A -> Type) : list A -> Type :=
| nil_param1 : list_param1 A P (@nil A)
| cons_param1 : forall a, P a -> forall l, list_param1 A P l -> list_param1 A P (cons a l).

Definition list_param1_term A (P : A -> Type) (HP : forall r : A, P r) (l : list A) : list_param1 A P l :=
  list_rect (list_param1 A P)
            (nil_param1 A P)
            (fun a l0 IHl => cons_param1 A P a (HP a) l0 IHl) l.

MetaCoq Run (get_paramE "list").


Inductive prod_param1 A (PA : A -> Type) B (PB : B -> Type) : A * B -> Type :=
| pair_param1 : forall a, PA a -> forall b, PB b -> prod_param1 A PA B PB (pair a b).

Definition prod_param1_term A (PA : A -> Type) (HPA : forall a : A, PA a)
                            B (PB : B -> Type) (HPB : forall b : B, PB b)
                            : forall (x : A * B), prod_param1 A PA B PB x :=
  prod_rect (prod_param1 A PA B PB)
            (fun a b => pair_param1 A PA B PB a (HPA a) b (HPB b)).

MetaCoq Run (get_paramE "prod").


Inductive vec A : nat -> Type :=
| vnil : vec A 0
| vcons : A -> forall n, vec A n -> vec A (S n).

Inductive vec_param1 A (PA : A -> Type) : forall n, vec A n -> Type :=
| vnil_param1 : vec_param1 A PA 0 (@vnil A)
| vcons_param1 : forall a, PA a -> forall n v, vec_param1 A PA n v ->
              vec_param1 A PA (S n) (vcons A a n v).

Definition vec_param1_term A (PA : A -> Type) (HPA : forall a : A, PA a)
            n v : vec_param1 A PA n v :=
  vec_rect _ (vec_param1 A PA)
             (vnil_param1 A PA)
             (fun a n v IHv => vcons_param1 A PA a (HPA a) n v IHv) n v.

MetaCoq Run (get_paramE "vec").

Definition E := [kmplist; kmpprod ; kmpvec].