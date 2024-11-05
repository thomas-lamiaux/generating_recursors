Set Universe Polymorphism.

(* 1.1 NESTED Definition of the RoseTree and induction principle *)
Inductive RoseTree A : Type :=
  | leaf (a : A) : RoseTree A
  | node (l : list (RoseTree A)) : RoseTree A.

Arguments leaf {_}.
Arguments node {_} _.

Inductive list_param1 A (PA : A -> Type) : list A -> Type :=
  | nil_param1 : list_param1 A PA nil
  | cons__param1 : forall a (aϵ : PA a) l (lϵ : list_param1 A PA l), list_param1 A PA (cons a l).

Definition list_param1_term A (PA : A -> Type) (aϵ: forall a, PA a) (l : list A) : list_param1 A PA l.
  induction l; econstructor; eauto.
Defined.

Lemma RoseTree_elim A (P : RoseTree A -> Type) (Pleaf: forall a, P (leaf a))
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
  | node_mut (l : list_RoseTreeMut A) : RoseTreeMut A
with
  list_RoseTreeMut A : Type :=
  | nil_mut : list_RoseTreeMut A
  | cons_mut : RoseTreeMut A -> list_RoseTreeMut A -> list_RoseTreeMut A.

Arguments leaf_mut {_} _.
Arguments node_mut {_} _.
Arguments nil_mut {_}.
Arguments cons_mut {_} _ _.

Scheme RoseTreeMut_rec' := Induction for RoseTreeMut Sort Type
  with list_RoseTreeMut_rec' := Induction for list_RoseTreeMut Sort Type.

Combined Scheme RoseTreeMut_combined from RoseTreeMut_rec',list_RoseTreeMut_rec'.

From Equations Require Import Equations.
From Coq Require Import List.

Set Equations Transparent.

(* 3. f : RoseTree -> RoseTreeMuT *)
Equations list_to_listMut {A} (l : list (RoseTreeMut A)) : list_RoseTreeMut A by struct l :=
| nil => nil_mut
| cons a l => cons_mut a (list_to_listMut l).

Equations listMut_to_list {A} (l : list_RoseTreeMut A) : list (RoseTreeMut A) :=
| nil_mut => nil
| cons_mut a l => cons a (listMut_to_list l).

Equations RT_to_RTMut {A} (RT : RoseTree A) : RoseTreeMut A by struct RT :=
| leaf a => leaf_mut a
| node l => node_mut (list_to_listMut (map RT_to_RTMut l)).

(* 4. g : RoseTreeMut -> RoseTree *)
Equations RTMut_to_RT {A} (RTM : RoseTreeMut A) : RoseTree A by struct RTM :=
| leaf_mut a => leaf a
| node_mut l => node (lRTMut_to_lRT l)
with lRTMut_to_lRT {A} (lRTM : list_RoseTreeMut A) : list (RoseTree A) :=
| nil_mut => nil
| cons_mut a l => cons (RTMut_to_RT a) (lRTMut_to_lRT l).


(* 5. Prove the section *)

(* to fix doesn't pass the guard *)
Definition sec : forall {A} (RT : RoseTree A), RT = RTMut_to_RT (RT_to_RTMut RT).
  intros A. fix rec 1.
  intros RT; destruct RT; cbn.
  - easy.
  - f_equal. induction l; cbn. easy. f_equal. apply rec. apply IHl.
Admitted.

(* 6. Prove Nested Rec *)

(* 6.1 Rewrite the mutual recursor to get one on RoseTree *)

(* Mutual Recusor *)
Definition RecMut := forall (A : Type) (P : RoseTreeMut A -> Type)
(P0 : list_RoseTreeMut A -> Type),
(forall a : A, P (leaf_mut a)) ->
(forall l : list_RoseTreeMut A, P0 l -> P (node_mut l)) ->
P0 nil_mut ->
(forall r : RoseTreeMut A,
P r -> forall l : list_RoseTreeMut A, P0 l -> P0 (cons_mut r l)) ->
forall r : RoseTreeMut A, P r.

(* Mutual Recusor Rewrited with RoseTree *)
Definition RecMutRT := forall (A : Type) (P : RoseTree A -> Type)
(P0 : list (RoseTree A) -> Type),
(forall a : A, P (leaf a)) ->
(forall l : list (RoseTree A), P0 l -> P (node l)) ->
P0 nil ->
(forall r : RoseTree A,
P r -> forall l : list (RoseTree A), P0 l -> P0 (cons r l)) ->
forall r : RoseTree A, P r.

Definition RecMut_to_RecRT : RecMut -> RecMutRT.
  unfold RecMut, RecMutRT.
  intros RecMut. intros A P P0 Pleaf Pnode P0nil P0cons.
  intros r. rewrite sec. generalize (RT_to_RTMut r); clear r.
  eapply (RecMut _ _ (fun l => P0 (lRTMut_to_lRT l))); clear RecMut.
  (* lRTMut_to_lRT relabel constructors*)
  all: cbn.
  (* it is possible to apply Pleaf etc... which hypothesis follows by recursivity *)
  all: eauto.
Qed.


(* 6.2 Mutual Rewrited to Nested Rec *)

(* Nested Recursor *)
Definition RecNested := forall (A : Type) (P : RoseTree A -> Type),
  (forall a : A, P (leaf a)) ->
  (forall l : list (RoseTree A),
  list_param1 (RoseTree A) P l -> P (node l)) ->
  forall r : RoseTree A, P r.

Definition Rec : RecMutRT -> RecNested.
  unfold RecMutRT, RecNested.
  intros RecRT. intros.
  (* Instantiate with the parametricty *)
  eapply (RecRT _ P (list_param1 _ P)).
  (* Nested case are trivial *)
  - assumption.
  - assumption.
  (* the two others cases corresponds to the fundamental theorem for list *)
  - constructor; assumption.
  - constructor; assumption.
Qed.