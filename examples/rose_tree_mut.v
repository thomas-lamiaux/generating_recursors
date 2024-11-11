Set Universe Polymorphism.

Inductive list_param1 A (PA : A -> Type) : list A -> Type :=
  | nil_param1 : list_param1 A PA nil
  | cons_param1 : forall a (ap : PA a) l (lp : list_param1 A PA l), list_param1 A PA (cons a l).

Definition list_param1_term A (PA : A -> Type) (aϵ: forall a, PA a) (l : list A) : list_param1 A PA l.
  induction l; econstructor; eauto.
Defined.

Unset Elimination Schemes.


(* 1.1 NESTED Definition of the RoseTree and induction principle *)
Inductive RoseTree A : Type :=
  | leaf (a : A) : RoseTree A
  | node (l : list (RoseTree A)) : RoseTree A.

Arguments leaf {_}.
Arguments node {_} _.

Lemma RoseTree_rect A (P : RoseTree A -> Type) (Pleaf: forall a, P (leaf a))
   (Pnode : forall l, list_param1 (RoseTree A) P l -> P (node l)) : forall r, P r.
Proof.
  fix rec 1.
  intro r; destruct r.
  - apply Pleaf.
  - apply Pnode. apply list_param1_term. exact rec.
Defined.


(* 1.2 MUTUAL Definition of the RoseTree and induction principle *)
Inductive RoseTreeMut A : Type :=
  | leaf_mut (a : A) : RoseTreeMut A
  | node_mut (l : listMut A) : RoseTreeMut A
with
  listMut A : Type :=
  | nil_mut : listMut A
  | cons_mut : RoseTreeMut A -> listMut A -> listMut A.

Arguments leaf_mut {_} _.
Arguments node_mut {_} _.
Arguments nil_mut {_}.
Arguments cons_mut {_} _ _.

Scheme RoseTreeMut_rect := Induction for RoseTreeMut Sort Type
  with listMut_rect := Induction for listMut Sort Type.

(* 2. f : RoseTree -> RoseTreeMut *)
Definition RT_to_RTMut {A} : forall (RT : RoseTree A), RoseTreeMut A.
  eapply RoseTree_rect.
    - intros a; apply leaf_mut, a.
    - intros l lp. apply node_mut.
      induction lp.
      + apply nil_mut.
      + apply cons_mut. apply ap. apply IHlp.
Defined.

(* 3. g : RoseTreeMut -> RoseTree *)
Definition RTMut_to_RT {A} : forall (RTMut : RoseTreeMut A), RoseTree A.
  eapply (RoseTreeMut_rect _ _ (fun l => list (RoseTree A))).
  - intros a; apply leaf, a.
  - intros l lp. apply node. exact lp.
  - apply nil.
  - intros r lr l lp. apply cons. apply lr. apply lp.
Defined.

(* 4. sec : forall x, x = g (f x) *)
Definition sec : forall {A} (RT : RoseTree A), RT = RTMut_to_RT (RT_to_RTMut RT).
  intros A. apply RoseTree_rect.
  - (* computes on leaf cause recursors *)
    intros a. cbn. reflexivity.
  - (* computes on node cause recursors *)
    intros l lp. cbn. f_equal.
    induction lp; cbn.
    -- reflexivity.
    -- f_equal. apply ap. apply IHlp.
Qed.

(* 5 Prove Mutual Rec rewritten with the section *)

(* Mutual Recusor Rewrited with RoseTree *)
Definition RecMutRT := forall (A : Type) (P : RoseTree A -> Type)
  (P0 : list (RoseTree A) -> Type),
  (forall a : A, P (leaf a)) ->
  (forall l : list (RoseTree A), P0 l -> P (node l)) ->
  P0 nil ->
  (forall r : RoseTree A,
  P r -> forall l : list (RoseTree A), P0 l -> P0 (cons r l)) ->
  forall r : RoseTree A, P r.

Definition RecMut_to_RecMutRT : RecMutRT.
Proof.
  intros A P P0 Pleaf Pnode P0nil P0cons.
  intros r. rewrite sec. generalize (RT_to_RTMut r); clear r.
  eapply RoseTreeMut_rect.
  - cbn. apply Pleaf.
  - intros l lp. cbn. apply Pnode. apply lp.
  - apply P0nil.
  - intros r lr l lp. apply P0cons. apply lr. apply lp.
Qed.

(* 6. Prove the latter implies the nested *)
Definition RecNested := forall (A : Type) (P : RoseTree A -> Type),
  (forall a : A, P (leaf a)) ->
  (forall l : list (RoseTree A),
  list_param1 (RoseTree A) P l -> P (node l)) ->
  forall r : RoseTree A, P r.

Definition Rec : RecMutRT -> RecNested.
  unfold RecMutRT, RecNested.
  intros RecRT. intros A P Pleaf Pnode.
  (* Instantiate with the parametricty *)
  eapply (RecRT _ P (list_param1 _ P)).
  (* Nested case are trivial *)
  - apply Pleaf.
  - apply Pnode.
  (* the two others cases corresponds to the fundamental theorem for list *)
  - apply nil_param1.
  - apply cons_param1; assumption.
Qed.

