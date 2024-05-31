Set Universe Polymorphism.

Inductive eqϵ A (Aϵ : A -> Type) (x : A) (xϵ : Aϵ x) :
  forall (y : A) (yϵ : Aϵ y), x = y -> Type :=
 | eq_reflP : eqϵ A Aϵ x xϵ x xϵ eq_refl.

(*
Definition eqϵ_fund A (Aϵ : A -> Type) (aϵ: forall a, Aϵ a) x y e
 : eqϵ A Aϵ x (aϵ x) y (aϵ y) e.
  destruct e; econstructor.
Defined.
*)

Notation "e # x" := (eq_rect _ _ x _ e) (at level 50).

Definition eqϵ_fund A (Aϵ : A -> Type) (aϵ : forall a, Aϵ a) x y e :
    eqϵ A Aϵ x (aϵ x) y (aϵ y) e.
destruct e; econstructor.
Defined.

Definition eqϵ_fund' A (Aϵ : A -> Type) x (xϵ: Aϵ x) y (yϵ: Aϵ y) e (eϵ : e # xϵ = yϵ)
 : eqϵ A Aϵ x xϵ y yϵ e.
  destruct eϵ, e. econstructor.
Defined.

Definition eqP_fun A (P Q : A -> Type) (HP: forall a, P a)
  (HPQ: forall a, P a -> Q a) x Px Qx y e :
  eqϵ A P x (Px) y (eq_rect _ _ (Px) _ e) e ->
  eqϵ A Q x (Qx) y (eq_rect _ _ (Qx) _ e) e.
destruct e; econstructor.
Defined.

(*
Definition eqP_param A (P : A -> Type) x y e (HP: forall a', x = a' -> P a')
 : eqP A P x (HP x eq_refl) y (HP y e) e.
destruct e; econstructor.
Qed.
*)

Inductive eq' A (x y : A) : Type :=
    box : x = y -> eq' A x y.

Inductive eqP' A (P : A -> Type) (x : A) (xP : P x) (y : A) (yP : P y) :
     eq' A x y -> Type :=
 | boxP : forall (e : x = y) (eP : eqϵ A P x xP y yP e), eqP' A P x xP y yP (box A x y e).

(* Definition eqP'_param A (P : A -> Type) x y e (HP: forall a', x = a' -> P a')
    : eqP' A P x (HP x x eq_refl) y (HP x y e) e.
  destruct e; econstructor.
  eapply eqP_param.
Qed.
 *)



Check (fun (A:Set) => list A).

Print list_rect.

Inductive Fnat@{u} : Type@{u} :=
  | Leaf : Fnat
  | Node : forall (x y : Fnat), x = y -> Fnat.

Unset Guard Checking.

Lemma Fnat_elim (P : Fnat -> Type)
  (PLeaf : P Leaf)
  (PNode: forall x (xP : P x) y (yP : P y) e (Pe : eqϵ _ P x xP y yP e), P (Node x y e))
  :
  forall t , P t.
Proof.
fix Fnat_elim 1.
intro t; destruct t.
- exact PLeaf.
- unshelve eapply PNode.
  + apply (Fnat_elim t1).
  + apply (Fnat_elim t2).
  + apply eqϵ_fund.
Defined.

Set Guard Checking.

Goal forall (P : Fnat -> Type) (PLeaf : P Leaf)
  (PNode: forall x (xP : P x) y (yP : P y) e (Pe : eqϵ _ P x xP y yP e), P (Node x y e))
  t1 t2 e, Fnat_elim P PLeaf PNode (Node t1 t2 e) =
  PNode t1 (Fnat_elim P PLeaf PNode t1) t2 (Fnat_elim P PLeaf PNode t2) e
           (eqϵ_fund Fnat P (Fnat_elim P PLeaf PNode) t1 t2 e).
  reflexivity.
Abort.