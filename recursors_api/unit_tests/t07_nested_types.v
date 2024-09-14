From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import All.

From RecAPI Require Import unit_tests.
From RecAPI Require Import nesting_param.

Unset Elimination Schemes.


(* ################################################# *)
(* Basic full nesting                                *)

Inductive RoseTree A : Type :=
| RTleaf (a : A) : RoseTree A
| RTnode (l : list (RoseTree A)) : RoseTree A.

Definition RoseTree_ind A (P : RoseTree A -> Type) (HRTleaf: forall a, P (RTleaf A a))
  (HRTnode : forall l, list_param1 _ P l -> P (RTnode A l))
  (* : forall (t : RoseTree A), P t.
  fix rec 1.
  destruct t.
  - apply HRTleaf.
  - apply HRTnode. apply list_param1_term. exact rec.
Qed. *)
  :=
  fix rec (t : RoseTree A) {struct t} : P t :=
  match t with
  | RTleaf a => HRTleaf a
  | RTnode l => HRTnode l ((list_param1_term (RoseTree A) P rec l))
  end.

Redirect "unit_tests/tests/07_01_RoseTree_custom" MetaCoq Run (print_rec "RoseTree").
Redirect "unit_tests/tests/07_01_RoseTree_gen"    MetaCoq Run (gen_rec E RoseTree).



Inductive PairTree A : Type :=
| Pleaf (a : A) : PairTree A
| Pnode (p : (PairTree A) * (PairTree A)) : PairTree A.

Definition PairTree_ind A (P : PairTree A -> Type) (HPleaf: forall a, P (Pleaf A a))
  (HPnode : forall p, prod_param1 _ P _ P p -> P (Pnode A p)) :=
  fix rec (t : PairTree A) {struct t} : P t :=
  match t with
  | Pleaf a => HPleaf a
  | Pnode p => HPnode p ((prod_param1_term _ P rec _ P rec p))
  end.

Redirect "unit_tests/tests/07_02_PairTree_custom" MetaCoq Run (print_rec "PairTree").
Redirect "unit_tests/tests/07_02_PairTree_gen"    MetaCoq Run (gen_rec E PairTree).


(* ################################################# *)
(* Partial nesting                                   *)

Inductive LeftTree A : Type :=
| Lleaf (a : A) : LeftTree A
| Lnode (p : (LeftTree A) * nat) : LeftTree A.

Definition LeftTree_ind A
  (P : LeftTree A -> Type)
  (HLleaf: forall a, P (Lleaf A a))
  (HLnode : forall p, prod_param1 _ P _ (fun _ => True) p -> P (Lnode A p)) :=
  fix rec (t : LeftTree A) {struct t} : P t :=
  match t with
  | Lleaf a => HLleaf a
  | Lnode p => HLnode p ((prod_param1_term (LeftTree A) P rec nat (fun _ => True) (fun _ => I) p))
  end.

Redirect "unit_tests/tests/07_03_LeftTree_custom" MetaCoq Run (print_rec "LeftTree").
Redirect "unit_tests/tests/07_03_LeftTree_gen"    MetaCoq Run (gen_rec E LeftTree).

Inductive RightTree A : Type :=
| Rleaf (a : A) : RightTree A
| Rnode (p : nat * (RightTree A)) : RightTree A.

Redirect "unit_tests/tests/07_04_RightTree_custom" MetaCoq Run (print_rec "RightTree").
Redirect "unit_tests/tests/07_04_RightTree_gen"    MetaCoq Run (gen_rec E RightTree).



(* ################################################# *)
(* Nested nesting                                    *)

Inductive NestedTree A : Type :=
| Nleaf (a : A) : NestedTree A
| Nnode (p : (list (list (NestedTree A)))) : NestedTree A.

Definition NestedTree_ind A
  (P : NestedTree A -> Type)
  (HNleaf: forall a, P (Nleaf A a))
  (HNnode : forall ll, list_param1 _ (list_param1 _ P) ll -> P (Nnode A ll)) :=
  fix rec (t : NestedTree A) {struct t} : P t :=
  match t with
  | Nleaf a => HNleaf a
  | Nnode ll => HNnode ll (list_param1_term _ _ (list_param1_term _ P rec ) ll)
  end.

Redirect "unit_tests/tests/07_05_NestedTree_custom" MetaCoq Run (print_rec "NestedTree").
Redirect "unit_tests/tests/07_05_NestedTree_gen"    MetaCoq Run (gen_rec E NestedTree).


(* ################################################# *)
(* Nesting with non uniform parameters               *)

(*
Inductive VecTree A n : Type :=
| Vleaf (a : A) : VecTree A n
| Vnode (p : (vec (VecTree A n) n)) : VecTree A n.

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


(* From Param Require Import Param.

Definition natimp :=
  forall (X : Prop), X -> (X -> X) -> X.

Parametricity natimp as foo arity 1. *)

(* Print foo. *)

Redirect "unit_tests/tests/07_07_VecTree_custom" MetaCoq Run (print_rec "VecTree").
Redirect "unit_tests/tests/07_07_VecTree_gen"    MetaCoq Run (gen_rec E VecTree).

*)


(* ################################################# *)
(* Nesting with indices                              *)





