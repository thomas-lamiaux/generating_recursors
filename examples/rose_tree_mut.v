Set Universe Polymorphism.

Require Import rose_tree.

Inductive RoseTreeMut A : Type :=
  | leaf_mut (a : A) : RoseTreeMut A
  | node_mut (l : list_RoseTreeMut A) : RoseTreeMut A
with
  list_RoseTreeMut A : Type :=
  | nil_rose : list_RoseTreeMut A
  | cons_rose : RoseTreeMut A -> list_RoseTreeMut A -> list_RoseTreeMut A.

Scheme RoseTreeMut_rec' := Induction for RoseTreeMut Sort Type
  with list_RoseTreeMut_rec' := Induction for list_RoseTreeMut Sort Type.

Lemma RoseTree_RoseTreeMut_rec' : forall (A : Type) (P : RoseTree A -> Type)
  (P0 : list (RoseTree A) -> Type),
(forall a : A, P (leaf A a)) ->
(forall l : list (RoseTree A), P0 l -> P (node A l)) ->
P0 nil ->
(forall (a : RoseTree A) (l : list (RoseTree A)), P0 l -> P0 (cons a l)) ->
forall r : RoseTree A, P r.
Proof.
  intros.
  induction r using RoseTree_elim.
  - eauto.
  - eapply X0. clear X3. induction l ; eauto.
Qed.

Lemma RoseTree_list_RoseTreeMut_rec'
: forall (A : Type) (P : RoseTree A -> Type)
      (P0 : list (RoseTree A) -> Type),
    (forall a : A, P (leaf A a)) ->
    (forall l : list (RoseTree A), P0 l -> P (node A l)) ->
    P0 (nil) ->
    (forall r : RoseTree A,
     P r -> forall l : list (RoseTree A), P0 l -> P0 (cons r l)) ->
    forall l : list (RoseTree A), P0 l.
Proof.
  intros. induction l; eauto.
  eapply X2; eauto.
  induction a using RoseTree_elim; eauto.
  eapply X0. induction X3; eauto.
Qed.

Fixpoint list_RoseTreeMut_map A (l:list_RoseTreeMut A) : list (RoseTreeMut A) :=
  match l with
  | nil_rose _ => nil
  | cons_rose _ a l => cons a (list_RoseTreeMut_map _ l)
  end.

Lemma RoseTree_elim_Mut : forall A (P : RoseTreeMut A -> Type) (Pleaf: forall a, P (leaf_mut A a))
   (Pnode : forall l, Listϵ (RoseTreeMut A) P (list_RoseTreeMut_map _ l) -> P (node_mut A l)), forall r, P r.
Proof.
  intros.
  eapply RoseTreeMut_rec' with (P := P) (P0 := fun l => Listϵ (RoseTreeMut A) P (list_RoseTreeMut_map _ l)); eauto.
  - cbn. econstructor.
  - cbn. intros. econstructor; eauto.
Qed.