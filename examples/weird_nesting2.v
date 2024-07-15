From RecNamed Require Import nesting_param.

Require Import List. Import ListNotations.






(* 1. Non Types only context *)
(* K *)
Inductive K (A : Type) (a : A) (B : Type) (b : B) : Type :=
| c1 : K A a B b
| c2 : A -> K A a B b -> K A a B b.

Inductive K_param1 (A : Type) (PA : A -> Type) (a : A) (aP : PA a)
                   (B : Type) (PB : B -> Type) (b : B) (bP : PB b)
                  : K A a B b -> Type :=
| c1_param1 : K_param1 A PA a aP B PB b bP (c1 A a B b)
| c2_param1 : forall a0, PA a0 ->
              forall x : K A a B b, K_param1 A PA a aP B PB b bP x ->
              K_param1 A PA a aP B PB b bP (c2 A a B b a0 x).

Definition K_param1_term A PA (HPA : forall a : A, PA a) a aP
                         B PB (HPB : forall b : B, PB b) b bP
          : forall k, K_param1 A PA a aP B PB b bP k.
Proof.
  induction k; constructor; easy.
Defined.

Definition K_param12 (A : Type) (PA : A -> Type) (a : A) (aP : PA a)
                     (B : Type) (b : B) :=
          K_param1 A PA a aP B (fun _ => True) b (I).

Definition K_param12_term A PA (HPA : forall a : A, PA a) a aP B b
  : forall k, K_param12 A PA a aP B b k.
Proof.
  apply K_param1_term; easy.
Defined.


Unset Elimination Schemes.

(* M *)
Inductive M (A B : Type) :=
| Mleaf : A -> M A B
| Mcons : forall a : M A B,
          forall b : list B,
          K (M A B) a (list B) b -> M A B.


Inductive M_param1 (A : Type) (PA : A -> Type)
                   (B : Type) (PB : B -> Type)
                   : M A B -> Type :=
| Mleaf_param1 : forall a, (PA a) -> M_param1 A PA B PB (Mleaf A B a)
| Mcons_param1 :
    forall a, forall aP : M_param1 A PA B PB a,
    forall b, forall bP : list_param1 B PB b,
    forall k, K_param1 (M A B) (M_param1 A PA B PB) a aP
                      (list B) (list_param1 B PB) b bP
                      k ->
    M_param1 A PA B PB (Mcons A B a b k).


Inductive M_param1_bis (A : Type)
                       (B : Type)

                       : M A B -> Type :=
| Mleaf_param1_bis : forall a, forall aP : True, M_param1_bis A B (Mleaf A B a)
| Mcons_param1_bis :
    forall a, forall aP : M_param1_bis A B a,
    forall b, forall bP : list_param1 B (fun _ => True) b,
    forall k, K_param1 (M A B) (M_param1_bis A B) a aP
                       (list B) (list_param1 B (fun _ => True)) b bP
                       k ->
    M_param1_bis A B (Mcons A B a b k).


Inductive M_param1_bis2 (A : Type)
                        (B : Type)

                        : M A B -> Type :=
| Mleaf_param1_bis2 : forall a, M_param1_bis2 A B (Mleaf A B a)
| Mcons_param1_bis2 :
    forall a, forall aP : M_param1_bis2 A B a,
    forall b,
    forall k, K_param1 (M A B) (M_param1_bis2 A B) a aP
              (list B) (list_param1 B (fun _ => True)) b (list_param1_term _ _ (fun _ => I) b)
              k ->
    M_param1_bis2 A B (Mcons A B a b k).


  Inductive M_param1_bis3 (A : Type)
                          (B : Type)

                          : M A B -> Type :=
| Mleaf_param1_bis3 : forall a, M_param1_bis3 A B (Mleaf A B a)
| Mcons_param1_bis3 :
    forall a, forall aP : M_param1_bis3 A B a,
    forall b,
    forall k, K_param1 (M A B) (M_param1_bis3 A B) a aP
    (list B) (fun _ => True) b I
    k ->
    M_param1_bis3 A B (Mcons A B a b k).


Definition M_ind (A B : Type) (P : M A B -> Type)
  (HMleaf : forall a, P (Mleaf A B a))
  (HMcons : forall a, forall aP : P a,
            forall b,
            forall k, K_param1 (M A B) P a aP
            (list B) (list_param1 B (fun _ => True)) b (list_param1_term _ _ (fun _ => I) b)
                      k ->
            P (Mcons A B a b k))
  : forall m : M A B, P m.
  fix rec 1. intro m; destruct m.
  - apply HMleaf.
  - unshelve eapply HMcons.
    -- now apply rec.
    -- apply K_param1_term. easy. now apply list_param1_term.
Qed.

Definition M_ind2 (A B : Type) (P : M A B -> Type)
  (HMleaf : forall a, P (Mleaf A B a))
  (HMcons : forall a, forall aP : P a,
            forall b,
            forall k, K_param1 (M A B) P a aP
            (list B) (fun _ => True) b I
                      k ->
            P (Mcons A B a b k))
  : forall m : M A B, P m.
  fix rec 1. intro m; destruct m.
  - apply HMleaf.
  - unshelve eapply HMcons.
    -- now apply rec.
    -- apply K_param1_term; easy.
Qed.