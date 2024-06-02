From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import All.

Require Import unit_tests.


(* ################################################# *)
(* Aux                                               *)


Inductive list_param1 A (P : A -> Type) : list A -> Type :=
| nil_param1 : list_param1 A P (@nil A)
| cons_param1 : forall a, P a -> forall l, list_param1 A P l -> list_param1 A P (cons a l).

Definition list_param1_term A (P : A -> Type) (HP : forall r : A, P r) (l : list A) : list_param1 A P l :=
  list_rect (list_param1 A P)
            (nil_param1 A P)
            (fun a l0 IHl => cons_param1 A P a (HP a) l0 IHl) l.

MetaCoq Run (get_paramE "list").


Inductive prod_param1 A (PA : A -> Type) B (PB : B -> Type) : A * B -> Type :=
| pair_param1 : forall a, PA a -> forall b, PB b -> prod_param1 A PA B PB (pair a b).

Definition prod_param1_term A (PA : A -> Type) (HPA : forall a : A, PA a)
                            B (PB : B -> Type) (HPB : forall b : B, PB b)
                            : forall (x : A * B), prod_param1 A PA B PB x :=
  prod_rect (prod_param1 A PA B PB)
            (fun a b => pair_param1 A PA B PB a (HPA a) b (HPB b)).

MetaCoq Run (get_paramE "prod").


Inductive vec A : nat -> Type :=
| vnil : vec A 0
| vcons : A -> forall n, vec A n -> vec A (S n).

Inductive vec_param1 A (PA : A -> Type) : forall n, vec A n -> Type :=
| vnil_param1 : vec_param1 A PA 0 (@vnil A)
| vcons_param1 : forall a, PA a -> forall n v, vec_param1 A PA n v ->
              vec_param1 A PA (S n) (vcons A a n v).

Definition vec_param1_term A (PA : A -> Type) (HPA : forall a : A, PA a)
            n v : vec_param1 A PA n v :=
  vec_rect _ (vec_param1 A PA)
             (vnil_param1 A PA)
             (fun a n v IHv => vcons_param1 A PA a (HPA a) n v IHv) n v.

MetaCoq Run (get_paramE "vec").

Definition E := [kmplist; kmpprod ; kmpvec].

(* ################################################# *)
(* Basic full nesting                                *)

Inductive RoseTree A : Type :=
| Rleaf (a : A) : RoseTree A
| Rnode (l : list (RoseTree A)) : RoseTree A.

Definition RoseTree_elim A (P : RoseTree A -> Type) (HRleaf: forall a, P (Rleaf A a))
  (HRnode : forall l, list_param1 _ P l -> P (Rnode A l)) :=
  fix rec (t : RoseTree A) {struct t} : P t :=
  match t with
  | Rleaf a => HRleaf a
  | Rnode l => HRnode l ((list_param1_term (RoseTree A) P rec l))
  end.

Redirect "recursors_named/tests/05_01_RoseTree_custom" MetaCoq Run (print_rec "RoseTree_elim").
Redirect "recursors_named/tests/05_01_RoseTree_gen"    MetaCoq Run (gen_rec E <% RoseTree %>).



Inductive PairTree A : Type :=
| Pleaf (a : A) : PairTree A
| Pnode (p : (PairTree A) * (PairTree A)) : PairTree A.

Definition PairTree_elim A (P : PairTree A -> Type) (HPleaf: forall a, P (Pleaf A a))
  (HPnode : forall p, prod_param1 _ P _ P p -> P (Pnode A p)) :=
  fix rec (t : PairTree A) {struct t} : P t :=
  match t with
  | Pleaf a => HPleaf a
  | Pnode p => HPnode p ((prod_param1_term _ P rec _ P rec p))
  end.

Redirect "recursors_named/tests/05_02_PairTree_custom" MetaCoq Run (print_rec "PairTree_elim").
Redirect "recursors_named/tests/05_02_PairTree_gen"    MetaCoq Run (gen_rec E <% PairTree %>).


(* ################################################# *)
(* Partial nesting                                   *)

Inductive LeftTree A : Type :=
| Lleaf (a : A) : LeftTree A
| Lnode (p : (LeftTree A) * nat) : LeftTree A.

  Definition LeftTree_elim A
    (P : LeftTree A -> Type)
    (HLleaf: forall a, P (Lleaf A a))
    (HLnode : forall p, prod_param1 _ P _ (fun _ => True) p -> P (Lnode A p)) :=
    fix rec (t : LeftTree A) {struct t} : P t :=
    match t with
    | Lleaf a => HLleaf a
    | Lnode p => HLnode p ((prod_param1_term (LeftTree A) P rec nat (fun _ => True) (fun _ => I) p))
    end.

Redirect "recursors_named/tests/05_03_LeftTree_custom" MetaCoq Run (print_rec "LeftTree_elim").
Redirect "recursors_named/tests/05_03_LeftTree_gen"    MetaCoq Run (gen_rec E <% LeftTree %>).


(* ################################################# *)
(* Nested nesting                                    *)

Inductive NestedTree A : Type :=
| Nleaf (a : A) : NestedTree A
| Nnode (p : (list (list (NestedTree A)))) : NestedTree A.

  Definition NestedTree_elim A
    (P : NestedTree A -> Type)
    (HNleaf: forall a, P (Nleaf A a))
    (HNnode : forall ll, list_param1 _ (list_param1 _ P) ll -> P (Nnode A ll)) :=
    fix rec (t : NestedTree A) {struct t} : P t :=
    match t with
    | Nleaf a => HNleaf a
    | Nnode ll => HNnode ll (list_param1_term _ _ (list_param1_term _ P rec ) ll)
    end.

Redirect "recursors_named/tests/05_04_NestedTree_custom" MetaCoq Run (print_rec "NestedTree_elim").
Redirect "recursors_named/tests/05_04_NestedTree_gen"    MetaCoq Run (gen_rec E <% NestedTree %>).


(* ################################################# *)
(* Nesting with indices                              *)

Inductive VecTree A : Type :=
| Vleaf (a : A) : VecTree A
| Vnode (n : nat) (p : (vec (VecTree A) n)) : VecTree A.

Redirect "recursors_named/tests/05_06_VecTree_custom" MetaCoq Run (print_rec "VecTree_elim").
Redirect "recursors_named/tests/05_06_VecTree_gen"    MetaCoq Run (gen_rec E <% VecTree %>).



(* ################################################# *)
(* MetaCoq Examples                                  *)


Redirect "recursors_named/tests/05_07_TemplateTerm_custom" MetaCoq Run (print_rec "term_forall_list_ind").
Redirect "recursors_named/tests/05_07_TempalteTerm_gen"  MetaCoq Run (gen_rec E <% term %>).

(* Bugs: Issue with let in ? *)
(* Redirect "recursors_named/tests/05_08_TemplateRed1_custom" MetaCoq Run (print_rec "red1_ind_all").
Redirect "recursors_named/tests/05_08_TempalteRed1_gen"  MetaCoq Run (gen_rec E <% red1 %>). *)


(* Bugs : Issue with flags *)
(* From MetaCoq.Common Require Import config.
Redirect "recursors_named/tests/05_09_TemplateTyping_custom" MetaCoq Run (print_rec "typing_ind_env").
Redirect "recursors_named/tests/05_09_TempalteTyping_gen"  MetaCoq Run (gen_rec E <% typing %>). *)
