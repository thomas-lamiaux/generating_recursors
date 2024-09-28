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
  :=
  fix rec (t : RoseTree A) {struct t} : P t :=
  match t with
  | RTleaf a => HRTleaf a
  | RTnode l => HRTnode l ((list_param1_term (RoseTree A) P rec l))
  end.

Redirect "recursors_api/unit_tests/tests/07_01_RoseTree_custom" MetaCoq Run (print_rec "RoseTree").
Redirect "recursors_api/unit_tests/tests/07_01_RoseTree_gen"    MetaCoq Run (gen_rec E RoseTree).

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

Redirect "recursors_api/unit_tests/tests/07_02_PairTree_custom" MetaCoq Run (print_rec "PairTree").
Redirect "recursors_api/unit_tests/tests/07_02_PairTree_gen"    MetaCoq Run (gen_rec E PairTree).


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

Redirect "recursors_api/unit_tests/tests/07_03_LeftTree_custom" MetaCoq Run (print_rec "LeftTree").
Redirect "recursors_api/unit_tests/tests/07_03_LeftTree_gen"    MetaCoq Run (gen_rec E LeftTree).

Inductive RightTree A : Type :=
| Rleaf (a : A) : RightTree A
| Rnode (p : nat * (RightTree A)) : RightTree A.

Redirect "recursors_api/unit_tests/tests/07_04_RightTree_custom" MetaCoq Run (print_rec "RightTree").
Redirect "recursors_api/unit_tests/tests/07_04_RightTree_gen"    MetaCoq Run (gen_rec E RightTree).



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

Redirect "recursors_api/unit_tests/tests/07_05_NestedTree_custom" MetaCoq Run (print_rec "NestedTree").
Redirect "recursors_api/unit_tests/tests/07_05_NestedTree_gen"    MetaCoq Run (gen_rec E NestedTree).


(* ################################################# *)
(* Nesting with indices                              *)

Inductive VecTree A : Type :=
| VNleaf (a : A) : VecTree A
| VNnode n (p : vec (VecTree A) n) : VecTree A.

Definition VecTree_ind A
  (P : VecTree A -> Type)
  (HVNleaf: forall a, P (VNleaf A a))
  (HVNnode : forall n v, vec_param1 _ P n v -> P (VNnode A n v)) :=
  fix rec (t : VecTree A) {struct t} : P t :=
  match t with
  | VNleaf a => HVNleaf a
  | VNnode n v => HVNnode n v (vec_param1_term _ _ rec n v)
  end.

Redirect "recursors_api/unit_tests/tests/07_06_VecTree_custom" MetaCoq Run (print_rec "VecTree").
Redirect "recursors_api/unit_tests/tests/07_06_VecTree_gen"    MetaCoq Run (gen_rec E VecTree).


(* ################################################# *)
(* Nesting when non strpos uparams                   *)

Inductive WTree A : Type :=
| WTleaf (a : A) : WTree A
| WTnode (ns : non_strpos10 nat (WTree A) 0) : WTree A.

(* INHABITABLE ??? > bug guard *)
(* Definition WTree_ind A (P : WTree A -> Type) (HWTleaf: forall a, P (WTleaf A a))
  (HWTnode : forall ns, non_strpos10_param1 nat (WTree A) P 0 ns -> P (WTnode A ns))
  : forall t, P t.
  fix rec 1. intro t; destruct t. apply HWTleaf. apply HWTnode.
  apply non_strpos10_param1_term. exact rec.
  Defined.
  :=
  fix rec (t : WTree A) {struct t} : P t :=
  match t with
  | WTleaf a => HWTleaf a
  | WTnode ns => HWTnode ns (non_strpos10_param1_term _ _ P rec _ ns)
  end. *)

Redirect "recursors_api/unit_tests/tests/07_07_WTree_custom" MetaCoq Run (print_rec "WTree").
Redirect "recursors_api/unit_tests/tests/07_07_WTree_gen"    MetaCoq Run (gen_rec E WTree).


(* FAILS *)
Inductive ArrowTree A : Type :=
| ATleaf (a : A) : ArrowTree A
| ATnode (l : list (nat -> ArrowTree A)) : ArrowTree A.

Definition ArrowTree_ind A (P : ArrowTree A -> Type) (HATleaf: forall a, P (ATleaf A a))
  (HATnode : forall l, list_param1 _ (fun f => forall (n : nat), P (f n)) l -> P (ATnode A l)) :=
  fix rec (t : ArrowTree A) {struct t} : P t :=
  match t with
  | ATleaf a => HATleaf a
  | ATnode l => HATnode l ((list_param1_term _ _ (fun f n => rec (f n)) l))
  end.

Redirect "recursors_api/unit_tests/tests/07_08_ArrowTree_custom" MetaCoq Run (print_rec "ArrowTree").
Redirect "recursors_api/unit_tests/tests/07_08_ArrowTree_gen"    MetaCoq Run (gen_rec E ArrowTree).


