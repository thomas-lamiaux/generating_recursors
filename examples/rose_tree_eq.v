Set Universe Polymorphism.

Check eq_ind.

Module ParamInd.

  Inductive eq_param1 A (PA : A -> Type) (x : A) (Px : PA x) :
    forall (y : A) (Py : PA y), x = y -> Type :=
  | eq_reflP : eq_param1 A PA x Px x Px eq_refl.

  Definition eq_param1_term A (PA : A -> Type) (HPA : forall a, PA a) x y e :
      eq_param1 A PA x (HPA x) y (HPA y) e.
  destruct e; econstructor.
  Defined.

  Inductive Fnat@{u} : Type@{u} :=
    | Leaf : Fnat
    | Node : forall (x y : Fnat), x = y -> Fnat.

  Unset Guard Checking.

  Lemma Fnat_elim (P : Fnat -> Type)
    (PLeaf : P Leaf)
    (PNode: forall x (xP : P x) y (yP : P y) e
    (Pe : eq_param1 _ P x xP y yP e), P (Node x y e))
    : forall t , P t.
  Proof.
  fix Fnat_elim 1.
  intro t; destruct t.
  - exact PLeaf.
  - unshelve eapply PNode.
    + apply (Fnat_elim t1).
    + apply (Fnat_elim t2).
    + apply eq_param1_term.
  Defined.

End ParamInd.

Module NoPInd.

  Inductive eq_param1 A (PA : A -> Type) (x : A) (Px : PA x) :
    forall (y : A), x = y -> Type :=
  | eq_reflP : eq_param1 A PA x Px x eq_refl.

  Definition eq_param1_term A (PA : A -> Type) (HPA : forall a, PA a) x y e :
      eq_param1 A PA x (HPA x) y e.
  destruct e; econstructor.
  Defined.

  Inductive Fnat@{u} : Type@{u} :=
    | Leaf : Fnat
    | Node : forall (x y : Fnat), x = y -> Fnat.

  Lemma Fnat_elim (P : Fnat -> Type)
    (PLeaf : P Leaf)
    (PNode: forall x (xP : P x) y e
    (Pe : eq_param1 _ P x xP y e), P (Node x y e))
    : forall t , P t.
  Proof.
  fix Fnat_elim 1.
  intro t; destruct t.
  - exact PLeaf.
  - unshelve eapply PNode.
    + apply (Fnat_elim t1).
    + apply eq_param1_term.
  Defined.

End NoPInd.


(*
Definition eq_param1_fund A (PA : A -> Type) (PA: forall a, PA a) x y e
 : eq_param1 A PA x (PA x) y (PA y) e.
  destruct e; econstructor.
Defined.
*)

(* Notation "e # x" := (eq_rect _ _ x _ e) (at level 50). *)

(* Definition eq_param1_fund' A (PA : A -> Type) x (Px: PA x) y (Py: PA y) e (eϵ : e # Px = Py)
 : eq_param1 A PA x Px y Py e.
  destruct eϵ, e. econstructor.
Defined. *)

(* Definition eqP_fun A (P Q : A -> Type) (HP: forall a, P a)
  (HPQ: forall a, P a -> Q a) x Px Qx y e :
  eq_param1 A P x (Px) y (eq_rect _ _ (Px) _ e) e ->
  eq_param1 A Q x (Qx) y (eq_rect _ _ (Qx) _ e) e.
destruct e; econstructor.
Defined. *)

(*
Definition eqP_param A (P : A -> Type) x y e (HP: forall a', x = a' -> P a')
 : eqP A P x (HP x eq_refl) y (HP y e) e.
destruct e; econstructor.
Qed.
*)

(* Inductive eq' A (x y : A) : Type :=
    box : x = y -> eq' A x y.

Inductive eqP' A (P : A -> Type) (x : A) (xP : P x) (y : A) (yP : P y) :
     eq' A x y -> Type :=
 | boxP : forall (e : x = y) (eP : eq_param1 A P x xP y yP e), eqP' A P x xP y yP (box A x y e). *)

(* Definition eqP'_param A (P : A -> Type) x y e (HP: forall a', x = a' -> P a')
    : eqP' A P x (HP x x eq_refl) y (HP x y e) e.
  destruct e; econstructor.
  eapply eqP_param.
Qed.
 *)



(* Check (fun (A:Set) => list A).

Print list_rect. *)



Goal forall (P : Fnat -> Type) (PLeaf : P Leaf)
  (PNode: forall x (xP : P x) y (yP : P y) e (Pe : eq_param1 _ P x xP y yP e), P (Node x y e))
  t1 t2 e, Fnat_elim P PLeaf PNode (Node t1 t2 e) =
  PNode t1 (Fnat_elim P PLeaf PNode t1) t2 (Fnat_elim P PLeaf PNode t2) e
           (eq_param1_fund Fnat P (Fnat_elim P PLeaf PNode) t1 t2 e).
  reflexivity.
Abort.


Inductive eq_param1' A (PA : A -> Type) (x : A) (Px : PA x) :
forall (y : A), x = y -> Type :=
| eq_reflP : eq_param1 A PA x Px x Px eq_refl.