From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import All.

From RecAPI Require Import unit_tests.

(* nat *)
Inductive nat_param1 : nat -> Type :=
| z_param1 : nat_param1 0
| S_param1 : forall n, nat_param1 n -> nat_param1 (S n).

Definition nat_param1_term : forall (x : nat), nat_param1 x :=
  nat_rec nat_param1 z_param1 (fun n => S_param1 n ).

MetaCoq Run (get_paramE "nat").


(* list  *)
Inductive list_param1 A (PA : A -> Type) : list A -> Type :=
| nil_param1 : list_param1 A PA (@nil A)
| cons_param1 : forall a, PA a -> forall l, list_param1 A PA l -> list_param1 A PA (cons a l).

Definition list_param1_term A (PA : A -> Type) (HPA : forall r : A, PA r) (l : list A) : list_param1 A PA l :=
  list_rect (list_param1 A PA)
            (nil_param1 A PA)
            (fun a l0 IHl => cons_param1 A PA a (HPA a) l0 IHl) l.

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

MetaCoq Run (get_paramE "vec").

(* Nesting context *)
Definition E := [kmpnat; kmplist; kmpprod ; kmpvec].
