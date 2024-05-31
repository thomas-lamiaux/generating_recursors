Set Universe Polymorphism.

Require Import rose_tree.
Require Import Bool.

Definition eq_correct A (f: A -> A -> bool) (x:A) := forall y , Is_true (f x y) -> x = y.

Definition list_eq A (A_eq : A -> A -> bool) :=
  fix rec (l1 l2 : list A) {struct l1} : bool :=
    match l1, l2 with
  | nil, nil => true
  | cons x xs, cons y ys => A_eq x y && rec xs ys
  | _, _ => false
  end.

Definition rtree_eq B (B_eq : B -> B -> bool) := fix rec (t1 t2 : RoseTree B) {struct t1} : bool :=
match t1, t2 with
| leaf _ x, leaf _ y => B_eq x y
| node _ l1, node _ l2 => list_eq (RoseTree B) rec l1 l2
| _, _ => false
end.

Lemma list_eq_correct A A_eq (HA: forall a, eq_correct A A_eq a) :
  forall l, eq_correct _ (list_eq A A_eq) l.
Proof.
  induction l; intros [] H; eauto; cbn in H; try inversion H.
  eapply andb_prop_elim in H. destruct H; f_equal; eauto. eapply HA; eauto.
Qed.

Fixpoint rtree_eq_correct A A_eq (HA: forall a, eq_correct A A_eq a) l : eq_correct _ (rtree_eq A A_eq) l.
Proof.
destruct l; intros [] H; eauto; try inversion H.
all: f_equal.
- eapply HA; eauto.
- eapply list_eq_correct; eauto.
Fail Guarded.
Abort.

Lemma list_eq_correct_loc A A_eq : forall l,
  Listϵ A (eq_correct A A_eq) l -> eq_correct _ (list_eq A A_eq) l.
Proof.
  intros l H. induction H; intros [] H'; eauto; cbn in H'; try inversion H'.
  eapply andb_prop_elim in H'. destruct H'; f_equal; eauto.
Qed.

Lemma list_eq_correct'' A A_eq (HA: forall a, eq_correct A A_eq a) :
  forall l, eq_correct _ (list_eq A A_eq) l.
  intros; eapply list_eq_correct_loc.
  induction l; econstructor; eauto.
Qed.

Lemma rtree_eq_correct A A_eq (HA: forall a, eq_correct A A_eq a) l : eq_correct _ (rtree_eq A A_eq) l.
 induction l using RoseTree_elim; intros [] H; eauto; cbn in H; try inversion H.
 all: f_equal.
 - eapply HA; eauto.
 - eapply list_eq_correct_loc; eauto.
Qed.




