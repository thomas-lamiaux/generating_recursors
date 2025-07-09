From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.

From NamedAPI Require Import unit_tests.
(* From NamedAPI Require Import nesting_param. *)

(* to generate too *)
Inductive list_param1 A (PA : A -> Type) : list A -> Type :=
| nil_param1 : list_param1 A PA ( @nil A)
| cons_param1 : forall a, PA a -> forall l, list_param1 A PA l -> list_param1 A PA (cons a l).

Definition list_param1_term A (PA : A -> Type) (HPA : forall r : A, PA r) (l : list A) : list_param1 A PA l :=
  list_rect (list_param1 A PA)
            (nil_param1 A PA)
            (fun a l0 IHl => cons_param1 A PA a (HPA a) l0 IHl) l.

Definition list_func A A_bis (fA : A -> A_bis) : list A -> list A_bis :=
  fix rec (l : list A) :=
  match l with
  | nil => nil
  | cons a l => cons (fA a) (rec l)
  end.

(* get it for the env *)
MetaRocq Run (get_paramEp list []).
Print kmp_list.

Definition Ep1 := [kmp_list].

Inductive All {A : Type} (P : A -> Type) : list A -> Type :=
| All_nil : All P []
| All_cons a l : P a -> All P l -> All P (a::l).

Arguments All_nil {_ _}.
Arguments All_cons {_ _}.

(* to generate *)
Inductive All_param1 {A} {P : A -> Type} (PP : forall a, P a -> Type)
  : forall {l}, All P l -> Type :=
| All_param1_nil : All_param1 PP All_nil
| All_param1_cons a l : forall (ra : P a), PP a ra -> forall (x : All P l), All_param1 PP x ->
                  All_param1 PP (All_cons a l ra x).

Arguments All_param1_nil {_ _ _}.
Arguments All_param1_cons {_ _ _}.

Fixpoint All_param1_term {A} {P : A -> Type} {PP : forall a, P a -> Type} (HPP : forall a ra, PP a ra)
    : forall l (t : All P l), All_param1 PP t :=
  fun l t => match t with
  | All_nil => All_param1_nil
  | All_cons a l ra x => All_param1_cons a l ra (HPP a ra) x (All_param1_term HPP l x)
  end.

Axiom All_func : Type.

(* It needs to know the strictly postive uniform parameters of list
   to compute striclty postive uniform parameters for All *)
MetaRocq Run (get_paramEp ( @All ) Ep1).
Print kmp_All.

(* Nesting context *)
Definition Ep := [kmp_list; kmp_All].

Unset Elimination Schemes.




(* RoseTree *)
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

Redirect "named_api/UnitTests/tests/10_01_RoseTree_gen" MetaRocq Run (generate Ep RoseTree).

(* typing *)
Inductive term : Type :=
| tCase : term -> list term -> term.

Inductive typing : term -> term -> Type :=
| typing_tCase (discr ind : term) (branches : list term) (return_type : term) :
          typing discr ind -> All (fun a => typing a return_type) branches ->
          typing (tCase discr branches) return_type.

Fixpoint typing_elim (P : forall t T, typing t T -> Type)
  (PtCase : forall discr ind branches return_type,
            forall (ty_discr : typing discr ind), P discr ind ty_discr ->
            forall (ty_branches : All (fun a => typing a return_type) branches),
              All_param1 (fun (a : term) (ty_a : typing a return_type) => P a return_type ty_a) ty_branches ->
            P _ _ (typing_tCase discr ind branches return_type ty_discr ty_branches)) :
    forall t T ty_tT, P t T ty_tT :=
  fun t T ty_tT => match ty_tT with
  | typing_tCase discr ind br return_type ty_discr ty_branches =>
      PtCase discr ind br return_type ty_discr (typing_elim P PtCase _ _ ty_discr)
        ty_branches (All_param1_term (fun t => typing_elim P PtCase t return_type) _ ty_branches)
  end.

(* stack overflow! no idea why *)
(* Redirect "named_api/UnitTests/tests/10_02_typing_coq" MetaRocq Run (print_rec "typing"). *)
Redirect "named_api/UnitTests/tests/10_02_typing_gen" MetaRocq Run (generate Ep ( @typing)).
