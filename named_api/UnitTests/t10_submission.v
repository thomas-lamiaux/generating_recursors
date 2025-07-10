From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.

From NamedAPI Require Import unit_tests.


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
MetaRocq Run (get_paramEp ( @All ) [kmp_list]).

(* Nesting context *)
Definition Ep := [kmp_list; kmp_All].

Unset Elimination Schemes.

Definition generate_sparse_param {A} Ep na u : A -> _ := generate_options false false TestSparseParam
                                        false false false false true false false Ep (Some na) (Some u).

Unset MetaRocq Strict Unquote Universe Mode.


(* Example 1: RoseTree *)
Inductive RoseTree A : Type :=
| RTleaf (a : A) : RoseTree A
| RTnode (l : list (RoseTree A)) : RoseTree A.

MetaRocq Run (generate_elim Ep "RoseTree_elim" (sType fresh_universe) RoseTree).

Check RoseTree_elim.
Print RoseTree_elim.

Fixpoint list_param1_size {A} (s : A -> nat) {l} (r : list_param1 A (fun _ => nat) l) : nat :=
  match r with
  | nil_param1 => 0
  | cons_param1 a sa l sl => S (sa + list_param1_size s sl)
  end.

Fixpoint rose_tree_size {A} (s : A -> nat) (r : RoseTree A) : nat :=
  RoseTree_elim A (fun _ => nat)
    (fun _ => 1)
    (fun l hpar => S (list_param1_size (rose_tree_size s) hpar)) r.


(* Example 2: typing *)
Inductive term : Type :=
| tCase : term -> list term -> term.

Inductive typing : term -> term -> Type :=
| typing_tCase (discr ind : term) (branches : list term) (return_type : term) :
          typing discr ind -> All (fun a => typing a return_type) branches ->
          typing (tCase discr branches) return_type.

MetaRocq Run (generate_elim Ep "typing_elim" (sType fresh_universe) typing).

Check typing_elim.
Print typing_elim.
