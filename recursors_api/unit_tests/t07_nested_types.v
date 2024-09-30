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
  (HRTnode : forall l, list_param1 _ (fun x => P x) l -> P (RTnode A l))
  :=
  fix rec (t : RoseTree A) {struct t} : P t :=
  match t with
  | RTleaf a => HRTleaf a
  | RTnode l => HRTnode l ((list_param1_term (RoseTree A) P rec l))
  end.

Redirect "recursors_api/unit_tests/tests/07_01_RoseTree_coq" MetaCoq Run (print_rec "RoseTree").
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

Redirect "recursors_api/unit_tests/tests/07_02_PairTree_coq" MetaCoq Run (print_rec "PairTree").
Redirect "recursors_api/unit_tests/tests/07_02_PairTree_gen"    MetaCoq Run (gen_rec E PairTree).


Inductive ArrowTree1 A : Type :=
| ATleaf1 (a : A) : ArrowTree1 A
| ATnode1 (l : (bool -> list (ArrowTree1 A))) : ArrowTree1 A.

Definition ArrowTree1_ind A (P : ArrowTree1 A -> Type) (HATleaf1: forall a, P (ATleaf1 A a))
  (HATnode1 : forall l, (forall b : bool, list_param1 _ (fun x => P x) (l b)) -> P (ATnode1 A l)) :=
  fix rec (t : ArrowTree1 A) {struct t} : P t :=
  match t with
  | ATleaf1 a => HATleaf1 a
  | ATnode1 l => HATnode1 l (fun b => (list_param1_term _ _ (fun f => rec f) (l b)))
  end.

Redirect "recursors_api/unit_tests/tests/07_03_ArrowTree1_coq" MetaCoq Run (print_rec "ArrowTree1").
Redirect "recursors_api/unit_tests/tests/07_03_ArrowTree1_gen"    MetaCoq Run (gen_rec E ArrowTree1).


Inductive ArrowTree2 A : Type :=
| ATleaf2 (a : A) : ArrowTree2 A
| ATnode2 (l : list (nat -> ArrowTree2 A)) : ArrowTree2 A.

Definition ArrowTree2_ind A (P : ArrowTree2 A -> Type) (HATleaf2: forall a, P (ATleaf2 A a))
  (HATnode2 : forall l, list_param1 _ (fun f => forall (n : nat), P (f n)) l -> P (ATnode2 A l)) :=
  fix rec (t : ArrowTree2 A) {struct t} : P t :=
  match t with
  | ATleaf2 a => HATleaf2 a
  | ATnode2 l => HATnode2 l ((list_param1_term _ _ (fun f n => rec (f n)) l))
  end.

Redirect "recursors_api/unit_tests/tests/07_04_ArrowTree2_coq" MetaCoq Run (print_rec "ArrowTree2").
Redirect "recursors_api/unit_tests/tests/07_04_ArrowTree2_gen"    MetaCoq Run (gen_rec E ArrowTree2).

Inductive ArrowTree3 A : Type :=
| ATleaf3 (a : A) : ArrowTree3 A
| ATnode3 (l : (bool -> list (nat -> ArrowTree3 A))) : ArrowTree3 A.

Definition ArrowTree3_ind A (P : ArrowTree3 A -> Type) (HATleaf3: forall a, P (ATleaf3 A a))
  (HATnode3 : forall l, (forall b, list_param1 _ (fun f => forall (n : nat), P (f n)) (l b)) -> P (ATnode3 A l)) :=
  fix rec (t : ArrowTree3 A) {struct t} : P t :=
  match t with
  | ATleaf3 a => HATleaf3 a
  | ATnode3 l => HATnode3 l (fun b => (list_param1_term _ _ (fun f n => rec (f n)) (l b)))
  end.

Redirect "recursors_api/unit_tests/tests/07_05_ArrowTree3_coq" MetaCoq Run (print_rec "ArrowTree3").
Redirect "recursors_api/unit_tests/tests/07_05_ArrowTree3_gen"    MetaCoq Run (gen_rec E ArrowTree3).

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

Redirect "recursors_api/unit_tests/tests/07_06_LeftTree_coq" MetaCoq Run (print_rec "LeftTree").
Redirect "recursors_api/unit_tests/tests/07_06_LeftTree_gen"    MetaCoq Run (gen_rec E LeftTree).

Inductive RightTree A : Type :=
| Rleaf (a : A) : RightTree A
| Rnode (p : nat * (RightTree A)) : RightTree A.

Definition RightTree_ind A
  (P : RightTree A -> Type)
  (HRleaf: forall a, P (Rleaf A a))
  (HRnode : forall p, prod_param1 _ (fun _ => True) _  P p -> P (Rnode A p)) :=
  fix rec (t : RightTree A) {struct t} : P t :=
  match t with
  | Rleaf a => HRleaf a
  | Rnode p => HRnode p ((prod_param1_term nat (fun _ => True) (fun _ => I) (RightTree A) P rec p))
  end.

Redirect "recursors_api/unit_tests/tests/07_07_RightTree_coq" MetaCoq Run (print_rec "RightTree").
Redirect "recursors_api/unit_tests/tests/07_07_RightTree_gen"    MetaCoq Run (gen_rec E RightTree).



(* ################################################# *)
(* Nested nesting                                    *)

Inductive NestedTree A : Type :=
| Nleaf (a : A) : NestedTree A
| Nnode (p : (list (list (NestedTree A)))) : NestedTree A.

Definition NestedTree_ind A
  (P : NestedTree A -> Type)
  (HNleaf: forall a, P (Nleaf A a))
  (HNnode : forall ll, list_param1 _ (fun l => list_param1 _ (fun x => P x) l) ll -> P (Nnode A ll)) :=
  fix rec (t : NestedTree A) {struct t} : P t :=
  match t with
  | Nleaf a => HNleaf a
  | Nnode ll => HNnode ll (list_param1_term _ _ (list_param1_term _ _ rec ) ll)
  end.

Redirect "recursors_api/unit_tests/tests/07_08_NestedTree_coq" MetaCoq Run (print_rec "NestedTree").
Redirect "recursors_api/unit_tests/tests/07_08_NestedTree_gen"    MetaCoq Run (gen_rec E NestedTree).


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

Redirect "recursors_api/unit_tests/tests/07_09_VecTree_coq" MetaCoq Run (print_rec "VecTree").
Redirect "recursors_api/unit_tests/tests/07_09_VecTree_gen"    MetaCoq Run (gen_rec E VecTree).


(* ################################################# *)
(* Nesting when non strpos uparams                   *)

Inductive WTree A : Type :=
| WTleaf (a : A) : WTree A
| WTnode (ns : non_strpos10 nat (WTree A) 0) : WTree A.

Definition WTree_ind A (P : WTree A -> Type) (HWTleaf: forall a, P (WTleaf A a))
  (HWTnode : forall ns, non_strpos10_param1 nat (WTree A) P 0 ns -> P (WTnode A ns))
  : forall t, P t.
  fix rec 1. intro t; destruct t. apply HWTleaf. apply HWTnode.
  apply non_strpos10_param1_term. exact rec.
Defined.

Redirect "recursors_api/unit_tests/tests/07_10_WTree_coq" MetaCoq Run (print_rec "WTree").
Redirect "recursors_api/unit_tests/tests/07_10_WTree_gen"    MetaCoq Run (gen_rec E WTree).





