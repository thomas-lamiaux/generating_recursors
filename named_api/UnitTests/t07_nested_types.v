From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import All.

From NamedAPI Require Import unit_tests.
From NamedAPI Require Import nesting_param.

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
  | RTnode l => HRTnode l ((list_param1_term (RoseTree A) (fun x => P x) (fun x => rec x) l))
  end.

Inductive RoseTree_param1 A (PA : A -> Type) : RoseTree A -> Type :=
| RTleaf_param1 : forall a, PA a -> RoseTree_param1 A PA (RTleaf A a)
| RTnode_param1 : forall l, list_param1 _ (fun x => RoseTree_param1 A PA x) l ->
                  RoseTree_param1 A PA (RTnode A l).

MetaCoq Run (tmMsg "01/15 RoseTree").
Redirect "named_api/UnitTests/tests/07_01_RoseTree_coq" MetaCoq Run (print_rec "RoseTree").
Redirect "named_api/UnitTests/tests/07_01_RoseTree_gen" MetaCoq Run (generate Ep RoseTree).

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

Inductive PairTree_param1 A (PA : A -> Prop) : PairTree A -> Type :=
| Pleaf_param1 : forall a, PA a -> PairTree_param1 A PA (Pleaf A a)
| Pnode_param1 : forall p, prod_param1 _ (fun x => PairTree_param1 A PA x)
                                        _ (fun x => PairTree_param1 A PA x) p ->
                  PairTree_param1 A PA (Pnode A p).

MetaCoq Run (tmMsg "02/15 PairTree").
Redirect "named_api/UnitTests/tests/07_02_PairTree_coq" MetaCoq Run (print_rec "PairTree").
Redirect "named_api/UnitTests/tests/07_02_PairTree_gen" MetaCoq Run (generate Ep PairTree).

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

Inductive ArrowTree1_param1 A (PA : A -> Prop) : ArrowTree1 A -> Type :=
| ATleaf1_param1 : forall a, PA a -> ArrowTree1_param1 A PA (ATleaf1 A a)
| ATnode1_param1 : forall f, (forall b, list_param1 _ (fun x => ArrowTree1_param1 A PA x) (f b)) ->
                   ArrowTree1_param1 A PA (ATnode1 A f).

MetaCoq Run (tmMsg "03/15 ArrowTree1").
Redirect "named_api/UnitTests/tests/07_03_ArrowTree1_coq" MetaCoq Run (print_rec "ArrowTree1").
Redirect "named_api/UnitTests/tests/07_03_ArrowTree1_gen" MetaCoq Run (generate Ep ArrowTree1).

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

Inductive ArrowTree2_param1 A (PA : A -> Prop) : ArrowTree2 A -> Type :=
| ATleaf2_param1 : forall a, PA a -> ArrowTree2_param1 A PA (ATleaf2 A a)
| ATnode2_param1 : forall l, list_param1 _ (fun f => forall b, ArrowTree2_param1 A PA (f b)) l ->
                    ArrowTree2_param1 A PA (ATnode2 A l).

MetaCoq Run (tmMsg "04/15 ArrowTree2").
Redirect "named_api/UnitTests/tests/07_04_ArrowTree2_coq" MetaCoq Run (print_rec "ArrowTree2").
Redirect "named_api/UnitTests/tests/07_04_ArrowTree2_gen" MetaCoq Run (generate Ep ArrowTree2).

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

Inductive ArrowTree3_param1 A (PA : A -> Prop) : ArrowTree3 A -> Type :=
| ATleaf3_param1 : forall a, PA a -> ArrowTree3_param1 A PA (ATleaf3 A a)
| ATnode3_param1 : forall f, (forall b, list_param1 _ (fun g => forall n, ArrowTree3_param1 A PA (g n)) (f b)) ->
                    ArrowTree3_param1 A PA (ATnode3 A f).

MetaCoq Run (tmMsg "05/15 ArrowTree3").
Redirect "named_api/UnitTests/tests/07_05_ArrowTree3_coq" MetaCoq Run (print_rec "ArrowTree3").
Redirect "named_api/UnitTests/tests/07_05_ArrowTree3_gen" MetaCoq Run (generate Ep ArrowTree3).

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

Inductive LeftTree_param1 A (PA : A -> Prop) : LeftTree A -> Type :=
| Lleaf_param1 : forall a, PA a -> LeftTree_param1 A PA (Lleaf A a)
| Lnode_param1 : forall p, prod_param1 _ (fun x => LeftTree_param1 A PA x) _ (fun _ => True) p ->
                 LeftTree_param1 A PA (Lnode A p).

MetaCoq Run (tmMsg "06/15 LeftTree").
Redirect "named_api/UnitTests/tests/07_06_LeftTree_coq" MetaCoq Run (print_rec "LeftTree").
Redirect "named_api/UnitTests/tests/07_06_LeftTree_gen" MetaCoq Run (generate Ep LeftTree).

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

Inductive RightTree_param1 A (PA : A -> Prop) : RightTree A -> Type :=
| Rleaf_param1 : forall a, PA a -> RightTree_param1 A PA (Rleaf A a)
| Rnode_param1 : forall p, prod_param1 _ (fun _ => True) _ (fun x => RightTree_param1 A PA x) p ->
                  RightTree_param1 A PA (Rnode A p).

MetaCoq Run (tmMsg "07/15 RightTree").
Redirect "named_api/UnitTests/tests/07_07_RightTree_coq" MetaCoq Run (print_rec "RightTree").
Redirect "named_api/UnitTests/tests/07_07_RightTree_gen" MetaCoq Run (generate Ep RightTree).

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

Inductive NestedTree_param1 A (PA : A -> Type) : NestedTree A -> Type :=
| Nleaf_param1 : forall a, PA a -> NestedTree_param1 A PA (Nleaf A a)
| Nnode_param1 : forall ll, list_param1 _ (fun l => list_param1 _ (fun x => NestedTree_param1 A PA x) l) ll ->
                 NestedTree_param1 A PA (Nnode A ll).

MetaCoq Run (tmMsg "08/15 NestedTree").
Redirect "named_api/UnitTests/tests/07_08_NestedTree_coq" MetaCoq Run (print_rec "NestedTree").
Redirect "named_api/UnitTests/tests/07_08_NestedTree_gen" MetaCoq Run (generate Ep NestedTree).

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

Inductive VecTree_param1 A (PA : A -> Type) : VecTree A -> Type :=
| VNleaf_param1 : forall a, PA a -> VecTree_param1 A PA (VNleaf A a)
| VNnode_param1 : forall n,
                  forall p, vec_param1 _ (fun x => VecTree_param1 A PA x) n p ->
                  VecTree_param1 A PA (VNnode A n p).

(* Inductive VecTree_mut A : Type :=
| VNleaf_mut (a : A) : VecTree_mut A
| VNnode_mut n : vec_mut A n -> VecTree_mut A
with vec_mut A : nat -> Type :=
| vnil_mut  : vec_mut A 0
| vcons_mut : VecTree_mut A -> forall n, vec_mut A n -> vec_mut A (S n). *)

MetaCoq Run (tmMsg "09/15 VecTree").
Redirect "named_api/UnitTests/tests/07_09_VecTree_coq" MetaCoq Run (print_rec "VecTree").
Redirect "named_api/UnitTests/tests/07_09_VecTree_gen"    MetaCoq Run (generate Ep VecTree).

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

Inductive WTree_param1 A (PA : A -> Prop) : WTree A -> Type :=
| WTleaf_param1 : forall a, PA a -> WTree_param1 A PA (WTleaf A a)
| WTnode_param1 : forall ns, non_strpos10_param1 nat (WTree A) (fun x => WTree_param1 A PA x) 0 ns ->
                  WTree_param1 A PA (WTnode A ns).

MetaCoq Run (tmMsg "10/15 WTree").
Redirect "named_api/UnitTests/tests/07_10_WTree_coq" MetaCoq Run (print_rec "WTree").
Redirect "named_api/UnitTests/tests/07_10_WTree_gen" MetaCoq Run (generate Ep WTree).

Inductive nu_nested (A B C : Type) : Type :=
| nu_nested_nil : A -> nu_nested A B C
| nu_nested_cons : list (nu_nested A (B * B) C) -> nu_nested A B C.

Definition nu_nested_ind A (P : forall B C, nu_nested A B C -> Type)
(Hnu_nested_nil: forall B C a, P B C (nu_nested_nil A B C a))
  (Hnu_nested_cons : forall B C l, list_param1 _ (fun x => P (B * B) C x) l -> P B C (nu_nested_cons A B C l)) :
   forall B C t, P B C t.
Proof.
  fix rec 3. intros B C t; destruct t. apply Hnu_nested_nil. apply Hnu_nested_cons.
  apply list_param1_term. apply rec.
Defined.

Inductive nu_nested_param1 A (PA : A -> Prop) B C : nu_nested A B C -> Type :=
| nu_nested_nil_param1 : forall a, PA a ->
                         nu_nested_param1 A PA B C (nu_nested_nil A B C a)
| nu_nested_cons_pram1 : forall l, list_param1 _ (nu_nested_param1 A PA (B * B) C) l ->
                         nu_nested_param1 A PA B C (nu_nested_cons A B C l).

MetaCoq Run (tmMsg "11/15 nu_nested").
Redirect "named_api/UnitTests/tests/07_11_nu_nested_coq" MetaCoq Run (print_rec "nu_nested").
Redirect "named_api/UnitTests/tests/07_11_nu_nested_gen" MetaCoq Run (generate Ep nu_nested).

(* ################################################# *)
(* Nesting on the uniform parameter                  *)

Set Elimination Schemes.

Inductive tricky1 A : Type :=
| tricky11 : A * nat -> tricky1 A.

Inductive tricky1_param1 A (PA : A -> Prop) : tricky1 A -> Type :=
| tricky11_param1 : forall x, prod_param1 A (fun a => PA a) nat (fun _ => True) x ->
                   tricky1_param1 A PA (tricky11 A x).

(* MetaCoq Run (tmMsg "12/15 tricky1"). *)
Redirect "named_api/UnitTests/tests/07_12_tricky1_coq" MetaCoq Run (print_rec "tricky1").
(* BUGS ISSUE UNIVERSE LEVEL *)
(* Redirect "named_api/UnitTests/tests/07_12_tricky1_gen" MetaCoq Run (generate Ep tricky1). *)

Inductive tricky2 A : Type :=
| tricky21 : list A -> tricky2 A.

Inductive tricky2_param1 A (PA : A -> Prop) : tricky2 A -> Type :=
| tricky21_param1 : forall l, list_param1 A (fun a => PA a) l ->
                   tricky2_param1 A PA (tricky21 A l).

(* MetaCoq Run (tmMsg "13/15 tricky2"). *)
Redirect "named_api/UnitTests/tests/07_13_tricky3_coq" MetaCoq Run (print_rec "tricky2").
(* BUGS ISSUE UNIVERSE LEVEL *)
(* Redirect "named_api/UnitTests/tests/07_13_tricky_gen" MetaCoq Run (generate Ep tricky2). *)

Inductive tricky3 A : Type :=
| tricky31 : A * A -> tricky3 A
| tricky32 : (list A) * A -> tricky3 A.

Inductive tricky3_param1 A (PA : A -> Prop) : tricky3 A -> Type :=
| tricky31_param1 : forall x, prod_param1 A (fun a => PA a) A (fun a => PA a) x ->
                   tricky3_param1 A PA (tricky31 A x)
| tricky32_param1 : forall x, prod_param1 (list A) (fun l => list_param1 A (fun a => PA a) l) A (fun a => PA a) x ->
            tricky3_param1 A PA (tricky32 A x).

(* MetaCoq Run (tmMsg "14/15 tricky3"). *)
Redirect "named_api/UnitTests/tests/07_14_tricky3_coq" MetaCoq Run (print_rec "tricky3").
(* BUGS ISSUE UNIVERSE LEVEL *)
(* Redirect "named_api/UnitTests/tests/07_14_tricky_gen" MetaCoq Run (generate Ep tricky3). *)

Unset Elimination Schemes.

(* Nesting with a function *)
Inductive typing A B (n : nat) (a : A) (b : B) : Type :=
| typ_nil  : typing A B n a b
| typ_cons : forall (lA : list A) (lB : list B),
             All2i A B (typing A B) n lA lB -> typing A B n a b.

(* It means correcting the computation of uparams of Coq  *)
Definition typing_ind A B (P : forall n a b, typing A B n a b -> Prop)
  (Htyp_nil  : forall n a b, P n a b (typ_nil A B n a b))
  (Htyp_cons : forall n a b,
               forall lA lB,
               forall x, All2i_param1 A B (typing A B) (fun n a b x => P n a b x) n lA lB x ->
               P n a b (typ_cons A B n a b lA lB x)) :
  forall n a b t, P n a b t.
Proof.
  fix rec 4. intros n a b t; destruct t.
  - apply Htyp_nil.
  - apply Htyp_cons.
  apply All2i_param1_term. apply rec.
Defined.

Inductive typing_param1 A B : forall n a b, typing A B n a b -> Prop :=
| typ_nil_param1  : forall n a b, typing_param1 A B n a b (typ_nil A B n a b)
| typ_cons_param1 : forall n a b, forall (lA : list A) (lB : list B),
                    forall x, All2i_param1 A B (typing A B) (fun n a b x => typing_param1 A B n a b x) n lA lB x ->
                    typing_param1 A B n a b (typ_cons A B n a b lA lB x).

(* MetaCoq Run (tmMsg "11/15 typing"). *)
Redirect "named_api/UnitTests/tests/07_15_typing_coq" MetaCoq Run (print_rec "typing").
Redirect "named_api/UnitTests/tests/07_15_typing_gen" MetaCoq Run (generate Ep (@typing)).

