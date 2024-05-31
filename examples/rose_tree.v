Set Universe Polymorphism.

Inductive RoseTree A : Type :=
  | leaf (a : A) : RoseTree A
  | node (l : list (RoseTree A)) : RoseTree A.

Inductive Listϵ A (Aϵ : A -> Type) : list A -> Type :=
  | nil_ : Listϵ A Aϵ nil
  | cons_ : forall a (aϵ : Aϵ a) l (lϵ : Listϵ A Aϵ l), Listϵ A Aϵ (cons a l).

Definition List_fun A (Aϵ : A -> Type) (aϵ: forall a, Aϵ a) (l : list A) : Listϵ A Aϵ l.
  induction l; econstructor; eauto.
Defined.

Lemma RoseTree_elim : forall A (P : RoseTree A -> Type) (Pleaf: forall a, P (leaf A a))
   (Pnode : forall l, Listϵ (RoseTree A) P l -> P (node A l)), forall r, P r.
Proof.
  intros ? ? ? ?. fix RoseTree_elim 1.
  intro r; destruct r.
  - apply Pleaf.
  - apply Pnode. exact (List_fun (RoseTree A) P RoseTree_elim l).
Defined.