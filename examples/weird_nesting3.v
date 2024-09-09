From RecNamed Require Import nesting_param.

Require Import List. Import ListNotations.






(* 1. Non Types only context *)
(* K *)
Inductive K (A : Type) (a : A) (B : Type) (b : list B) : Type :=
| c1 : K A a B b
| c2 : A -> K A a B b -> K A a B b.

Inductive K_param1 (A : Type) (PA : A -> Type) (a : A) (aP : PA a)
                   (B : Type) (PB : B -> Type) (lb : list B) (bP : list_param1 _ PB lb)
                  : K A a B lb -> Type :=
| c1_param1 : K_param1 A PA a aP B PB lb bP (c1 A a B lb)
| c2_param1 : forall a0, PA a0 ->
              forall x : K A a B lb, K_param1 A PA a aP B PB lb bP x ->
              K_param1 A PA a aP B PB lb bP (c2 A a B lb a0 x).

(* No hyp for lb ? *)
Definition K_param1_term A PA (HPA : forall a : A, PA a) a aP
                         B PB (HPB : forall b : B, PB b) lb bP
          : forall k, K_param1 A PA a aP B PB lb bP k.
Proof.
  induction k; constructor; easy.
Defined.

Definition K_param12 (A : Type) (PA : A -> Type) (a : A) (aP : PA a)
                     (B : Type) (lb : list B) :=
          K_param1 A PA a aP B (fun _ => True) lb
            (list_param1_term _ (fun _ => True) (fun _ => I) lb).

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
          forall lb : list B,
          K (M A B) a B lb -> M A B.


Inductive M_param1 (A : Type) (PA : A -> Type)
                   (B : Type) (PB : B -> Type)
                   : M A B -> Type :=
| Mleaf_param1 : forall a, (PA a) -> M_param1 A PA B PB (Mleaf A B a)
| Mcons_param1 :
    forall a, forall aP : M_param1 A PA B PB a,
    forall lb, forall lbP : list_param1 B PB lb,
    forall k, K_param1 (M A B) (M_param1 A PA B PB) a aP
                        B PB lb lbP
                        k ->
    M_param1 A PA B PB (Mcons A B a lb k).


Inductive M_param1_bis (A : Type)
                       (B : Type)

                       : M A B -> Type :=
| Mleaf_param1_bis : forall a, forall aP : True, M_param1_bis A B (Mleaf A B a)
| Mcons_param1_bis :
    forall a, forall aP : M_param1_bis A B a,
    forall lb, forall lbP : list_param1 B (fun _ => True) lb,
    forall k, K_param1 (M A B) (M_param1_bis A B) a aP
                       B (fun _ => True) lb lbP
                       k ->
    M_param1_bis A B (Mcons A B a lb k).


Inductive M_param1_bis2 (A : Type)
                        (B : Type)

                        : M A B -> Type :=
| Mleaf_param1_bis2 : forall a, M_param1_bis2 A B (Mleaf A B a)
| Mcons_param1_bis2 :
    forall a, forall aP : M_param1_bis2 A B a,
    forall lb,
    forall k, K_param1 (M A B) (M_param1_bis2 A B) a aP
              B (fun _ => True) lb (list_param1_term _ _ (fun _ => I) lb)
              k ->
    M_param1_bis2 A B (Mcons A B a lb k).


Definition M_ind (A B : Type) (P : M A B -> Type)
  (HMleaf : forall a, P (Mleaf A B a))
  (HMcons : forall m, forall mP : P m,
            forall lb,
            forall k, K_param1 (M A B) P a aP
            B (fun _ => True) lb (list_param1_term _ _ (fun _ => I) lb)
                      k ->
            P (Mcons A B a lb k))
  : forall m : M A B, P m.
  fix rec 1. intro m; destruct m.
  - apply HMleaf.
  - unshelve eapply HMcons.
    -- now apply rec.
    -- apply K_param1_term; easy.
Qed.
