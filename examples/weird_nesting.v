Require Import nesting_param.

Inductive nulist (A : Type) : Type :=
| nu_nil : nulist A
| nu_cons : A -> nulist (A * A) -> nulist A.




(* 1. Non Types only context *)
(* K *)
Inductive K (A : Type) (l : list A) : Type :=
| c1 : K A l
| c2 : A -> K A l -> K A l.

Inductive K_param1 (A : Type) (PA : A -> Type) (l : list A)
  (lP : list_param1 A PA l) : K A l -> Type :=
| c1_param1 : K_param1 A PA l lP (c1 A l)
| c2_param1 : forall a, PA a ->
              forall x : K A l, K_param1 A PA l lP x ->
              K_param1 A PA l lP (c2 A l a x).

Unset Elimination Schemes.

(* N *)
Inductive N (A : Type) :=
| Nleaf : N A
| Ncons : K (N A) (@nil (N A)) -> N A.

(* Inductive N_mut (A : Type) :=
| Nleaf_mut : N_mut A
| Ncons_mut : K_mut A -> N_mut A
with M_list (A : Type) :=
| N_nil : M_list A
| N_cons : N_mut A -> M_list A -> M_list A
with K_mut (A : Type) : Type :=
| N_c1 : K_mut A
| N_c2 : A -> K_mut A -> K_mut A. *)

Definition N_indc (A : Type) (P : N A -> Type)
  (HNleaf : P (Nleaf A))
  (HNcons :
            forall x : K (N A) (@nil (N A)),
              K_param1 (N A) P (@nil (N A)) (nil_param1  _ P) x
              ->
            P (Ncons A x))
  : forall n : N A, P n.
  fix rec 1.
  intro n; destruct n.
  - apply HNleaf.
  - apply HNcons.
    induction k; cbn.
    -- apply c1_param1.
    -- apply c2_param1. apply rec. apply IHk.
Qed.

(* M *)
Inductive M (A : Type) :=
| Mleaf : M A
| Mcons : forall (l : list (M A)), K (M A) l -> M A.

(* M_mut = N_mut as l is not used ?  *)
Definition M_indc (A : Type) (P : M A -> Type)
  (HMleaf : P (Mleaf A))
  (HMcons : forall l, forall (lP : list_param1 (M A) P l) ,
            forall x : K (M A) l,
              K_param1 (M A) P l lP x
              ->
            P (Mcons A l x))
  : forall m : M A, P m.
  fix rec 1. intro m; destruct m.
  - apply HMleaf.
  - apply (HMcons l (list_param1_term _ _ rec _)). induction k.
    -- apply c1_param1.
    -- apply c2_param1. apply rec. apply IHk.
Qed.


(* 2. Nesting with Vec *)
Inductive VecTree A n : Type :=
| Vleaf (a : A) : VecTree A n
| Vnode (p : (vec (VecTree A n) n)) : VecTree A n.

(* Mutual but with a param and an indice *)
Inductive VecTree_Mut A m : Type :=
| Vleaf_Mut : A -> VecTree_Mut A m
| Vnode_Mut : vec_Mut A m m -> VecTree_Mut A m
with vec_Mut A m : nat -> Type :=
| vnil_Mut : vec_Mut A m 0
| vcons_Mut : forall n, VecTree_Mut A m -> vec_Mut A m n -> vec_Mut A m (S n).

Definition VecTree_ind A n
  (P : VecTree A n -> Type)
  (HVleaf: forall a, P (Vleaf A n a))
  (HVnode : forall p, vec_param1 _ P n (nat_param1_term n) p -> P (Vnode A n p))
  : forall (t : VecTree A n), P t.
Proof.
  fix rec 1. intro t; destruct t.
  - apply HVleaf.
  - apply HVnode.
  apply vec_param1_term. exact rec.
Qed.




(* 2. Nesting on non-uniforma param *)






Inductive nulist_param1 (A : Type) (P : A -> Type) : nulist A -> Type :=
| nu_nil_param1 : nulist_param1 A P (nu_nil A)
| nu_cons_param1 : forall a, P a
                  -> forall l, nulist_param1 (A * A) (prod_param1 _ P _ P) l
                  -> nulist_param1 A P (nu_cons A a l).

Definition nulist_param1_term (A : Type) (P : A -> Type) (HPA : forall a, P a)
  (nul : nulist A) : nulist_param1 A P nul.
Proof.
  induction nul ; constructor; cbn; auto using prod_param1_term.
Defined.

Unset Positivity Checking.

Inductive NuRoseTree A : Type :=
| NuRTleaf : A -> NuRoseTree A
| NuRTcons : nulist (NuRoseTree A) -> NuRoseTree A.

Set Positivity Checking.

(* Does not work *)
Definition NuRoseTree_ind (A : Type) (P : NuRoseTree A -> Type)
  (HNuRTleaf : forall a, P (NuRTleaf A a))
  (HNuRTcons : forall (nul : nulist (NuRoseTree A)),
                nulist_param1 _ P nul -> P (NuRTcons A nul))
    : forall t : NuRoseTree A, P t.
Proof.
  fix rec 1. intro t; destruct t.
  - apply HNuRTleaf.
  - apply HNuRTcons. apply nulist_param1_term. exact rec.
Admitted.

(* Try interca

Fixpoint compn {A} n (f : A -> A) a : A :=
  match n with
  | 0 => a
  | S n => compn n f (f a)
  end.

Definition prod2 := (fun X : Type => (X * X)%type).
Definition prod2n := fun n => compn n (fun X : Type => (X * X)%type).

Inductive nuRT_mut (A : Type) :=
| nuRTleaf_mut : A -> nuRT_mut A
| nuRTcons_mut : nulist_mut A 0 -> nuRT_mut A
with nulist_mut (A : Type) : nat -> Type :=
| nunil_mut : nulist_mut A 0
| nucons_mut n : prod2n n (nuRT_mut A) -> nulist_mut A (S n) -> nulist_mut A n


Scheme nuRT_nulist_mut_rec := Induction for nuRT_mut Sort Type
  with nulist_mut_nuRT_rec := Induction for nulist_mut Sort Type.

Definition nuRT := nuRT_mut.
Definition nuRTleaf : forall A, A -> nuRT A := nuRTleaf_mut.



Definition nulist_to_nulist_mut {A} : nulist (nuRT A) -> nulist_mut A .
Admitted.



Definition nulist_mut_to_nulist {A} : forall n, nulist_mut (prod2n n A) -> nulist (prod2n n (nuRT A)).
  intros n x. destruct x.
  - apply nu_nil.
  - induction n; cbn in *.
    -- apply nu_cons. 1: exact n0.
Admitted.


Definition nuRTcons A : nulist (nuRT A) -> nuRT A :=
  fun nl => nuRTcons_mut _ (nulist_to_nulist_mut nl).

Definition nuRoseTree_ind (P : forall A, nuRT A -> Type)
  (HNuRTleaf : forall A a, P _ (nuRTleaf A a))
  (HNuRTcons : forall A (nul : nulist (nuRT A)),
               nulist_param1 (nuRT A) (P _) nul -> P _ (nuRTcons A nul))
    : forall A (t : nuRT A), P A t.
Proof.
  unshelve eapply nuRT_nulist_mut_rec with
    (P := P)
    (P0 := fun A0 l => nulist_param1 _ (P A0) (nulist_mut_to_nulist l));
  eauto; cbn; intros A0.
  1: { intros lmut H. replace lmut with (nulist_to_nulist_mut (nulist_mut_to_nulist lmut)) by admit.
       apply HNuRTcons. assumption. }
  - replace (nulist_mut_to_nulist (nunil_mut A0)) with (nu_nil (nuRT A0)) by admit.
    constructor.
  - intros nrt Hnrt lmut Hlmut .
Admitted.

Print list.



(* Definition nulist_mut_to_nulist {A B} (f : A -> B) (l : nulist_mut A) : (nulist B).
  revert f l. revert B. revert A.
  fix rec 4. intros A B f l; destruct l.
  - apply nu_nil.
  - apply nu_cons. exact n. apply rec.
  match l with
  | nu_nil_mut => nu_nil _
  | nu_cons_mut t l => nu_cons _ t (nulist_mut_to_nulist l)
  end. *)



  (* OLD VERSION *)
  (*

Fixpoint compn {A} n (f : A -> A) a : A :=
  match n with
  | 0 => a
  | S n => compn n f (f a)
  end.


Definition prod2 := (fun X : Type => (X * X)%type).
Definition prod2n := fun n => compn n (fun X : Type => (X * X)%type).

Definition prod2n_pred n : forall A (P : A -> Type), prod2n n A -> Type.
Proof.
  induction n; intros A P; cbn.
  - assumption.
  - apply IHn. apply prod_param1; apply P.
Defined.

  Inductive nulist_param1 (A : Type) (P : forall n, prod2n n A -> Type) : nulist A -> Type :=
  | nu_nil_param1 : nulist_param1 A P (nu_nil A)
  | nu_cons_param1 : forall a, P 0 a
                    -> forall l, nulist_param1 (A * A) (fun n Z => P (S n) Z) l
                    -> nulist_param1 A P (nu_cons A a l).

  Definition nulist_param1_term (A : Type) (P : A -> Type) (HPA : forall a, P a)
    (nul : nulist A) : nulist_param1 A (fun n => prod2n_pred n _ P) nul.
  Proof.
    induction nul ; constructor; cbn; auto using prod_param1_term.
  Defined.

  (* Positivity check catch it *)
  Unset Positivity Checking.

  Inductive NuRoseTree A : Type :=
  | NuRTleaf : A -> NuRoseTree A
  | NuRTcons : nulist (NuRoseTree A) -> NuRoseTree A.

  Definition NuRoseTree_ind (A : Type) (P : forall A, NuRoseTree A -> Type)
    (HNuRTleaf : forall a, P _ (NuRTleaf A a))
    (HNuRTcons : forall (nul : nulist (NuRoseTree A)),
                  nulist_param1 (NuRoseTree A) (fun n => prod2n_pred n _ (P A)) nul ->
                  P _ (NuRTcons A nul))
      : forall t : NuRoseTree A, P A t.
  Proof.
  Admitted.
    (* fix rec 1.
    intro t; destruct t.
    - apply HNuRTleaf.
    - apply HNuRTcons. apply nulist_param1_term, rec.
    Show Proof.
  Qed. *)
  *)



(* Try to define an interface (ish) for RT *)
Inductive RT_mut (A : Type) :=
| RTleaf_mut : A -> RT_mut A
| RTcons_mut : list_mut A -> RT_mut A
with list_mut (A : Type) :=
| nil_mut : list_mut A
| cons_mut : RT_mut A -> list_mut A -> list_mut A.

Scheme RT_list_mut_rec := Induction for RT_mut Sort Type
  with list_mut_RT_rec := Induction for list_mut Sort Type.

Definition RT := RT_mut.
Definition RTleaf : forall A, A -> RT A := RTleaf_mut.

Fixpoint list_to_list_mut {A} (l : list (RT A)) : list_mut A :=
  match l with
  | nil => nil_mut _
  | cons a l => cons_mut _ a (list_to_list_mut l)
  end.

Fixpoint list_mut_to_list {A} (l : list_mut A) : list (RT A) :=
  match l with
  | nil_mut => nil _
  | cons_mut a l => cons a (list_mut_to_list l)
  end.

Definition RTcons : forall A, list (RT A) -> RT A :=
  fun A l => RTcons_mut _ (list_to_list_mut l).

(* Requires an inverse *)
Definition RT_ind A (P : RT A -> Type)
  (HRTleaf: forall a, P (RTleaf A a))
  (HRTnode : forall l, list_param1 _ P l -> P (RTcons A l)) : forall rt, P rt.
Proof.
  apply RT_list_mut_rec with
    (P := P)
    (P0 := fun l => list_param1 _ P (list_mut_to_list l));
  eauto; cbn.
  1: { intro lmut. intro H. replace lmut with (list_to_list_mut (list_mut_to_list lmut)) by admit.
       apply HRTnode. assumption. }
  all: intros; constructor; auto.
Admitted.