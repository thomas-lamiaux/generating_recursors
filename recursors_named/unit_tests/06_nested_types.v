From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import All.

Require Import unit_tests.
Require Import nesting_param.

Unset Elimination Schemes.


(* ################################################# *)
(* Basic full nesting                                *)

Inductive RoseTree A : Type :=
| Rleaf (a : A) : RoseTree A
| Rnode (l : list (RoseTree A)) : RoseTree A.

Definition RoseTree_ind A (P : RoseTree A -> Type) (HRleaf: forall a, P (Rleaf A a))
  (HRnode : forall l, list_param1 _ P l -> P (Rnode A l)) :=
  fix rec (t : RoseTree A) {struct t} : P t :=
  match t with
  | Rleaf a => HRleaf a
  | Rnode l => HRnode l ((list_param1_term (RoseTree A) P rec l))
  end.

Redirect "recursors_named/tests/06_01_RoseTree_custom" MetaCoq Run (print_rec "RoseTree").
Redirect "recursors_named/tests/06_01_RoseTree_gen"    MetaCoq Run (gen_rec E <% RoseTree %>).



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

Redirect "recursors_named/tests/06_02_PairTree_custom" MetaCoq Run (print_rec "PairTree").
Redirect "recursors_named/tests/06_02_PairTree_gen"    MetaCoq Run (gen_rec E <% PairTree %>).


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

Redirect "recursors_named/tests/06_03_LeftTree_custom" MetaCoq Run (print_rec "LeftTree").
Redirect "recursors_named/tests/06_03_LeftTree_gen"    MetaCoq Run (gen_rec E <% LeftTree %>).


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

Redirect "recursors_named/tests/06_04_NestedTree_custom" MetaCoq Run (print_rec "NestedTree").
Redirect "recursors_named/tests/06_04_NestedTree_gen"    MetaCoq Run (gen_rec E <% NestedTree %>).


(* ################################################# *)
(* Nesting with indices                              *)

(* Inductive VecTree A : Type :=
| Vleaf (a : A) : VecTree A
| Vnode (n : nat) (p : (vec (VecTree A) n)) : VecTree A.

Redirect "recursors_named/tests/06_05_VecTree_custom" MetaCoq Run (print_rec "VecTree").
Redirect "recursors_named/tests/06_05_VecTree_gen"    MetaCoq Run (gen_rec E <% VecTree %>). *)



