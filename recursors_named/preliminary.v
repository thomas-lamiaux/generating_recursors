From MetaCoq.Utils Require Import utils.
From MetaCoq.Utils Require Import MCString.
From MetaCoq.Template Require Import All.

Import MCMonadNotation.


(* A fold_right_i *)
Fixpoint fold_right_i_aux {A B} (f : nat -> B -> A -> A) (a0 : A) (l : list B)
  (i : nat) : A :=
   match l with
   | [] => a0
   | h :: q => f i h (fold_right_i_aux f a0 q (S i))
   end.

Definition fold_right_i {A B} (f : nat -> B -> A -> A) (a0 : A) (l : list B) : A
  := fold_right_i_aux f a0 l 0.



(* Printing functions *)
Definition printInductive (q : qualid): TemplateMonad unit :=
  kn <- tmLocate1 q ;;
  match kn with
  | IndRef ind => (tmQuoteInductive ind.(inductive_mind)) >>= tmPrint
  | _ => tmFail ("[" ^ q ^ "] is not an inductive")
  end.

Definition printConstantBody (q : qualid) b : TemplateMonad unit :=
  kn <- tmLocate1 q ;;
  match kn with
  | ConstRef kn => x <- (tmQuoteConstant kn b) ;;
                   y <- tmEval all x.(cst_body) ;;
                   tmPrint y
  | _ => tmFail ("[" ^ q ^ "] is not a constant")
  end.

Definition printConstantType (q : qualid) b : TemplateMonad unit :=
  kn <- tmLocate1 q ;;
  match kn with
  | ConstRef kn => x <- (tmQuoteConstant kn b) ;;
                   y <- tmEval all x.(cst_type) ;;
                   tmPrint y
  | _ => tmFail ("[" ^ q ^ "] is not a constant")
  end.

(* Gathering all the constructors of the form (cb_block, cb_ctor, ctor) *)
Definition gather_ctors (mdecl : mutual_inductive_body) : _ :=
  concat( mapi (fun cb_block indb =>
            mapi (fun cb_ctor ctor => (cb_block, cb_ctor, ctor))
            indb.(ind_ctors))
          mdecl.(ind_bodies)).

Definition AnonRel := {| binder_name := nAnon; binder_relevance := Relevant |}.

Definition tProdAnon t1 t2 := tProd AnonRel t1 t2.

Infix "t->" := tProdAnon (at level 60, right associativity).


Definition make_raname (s : ident) := mkBindAnn (nNamed s) Relevant.

(* Functions to create names *)
Definition make_name (s : ident) (n : nat) :=
  String.append s (string_of_nat n).

Definition make_name0 (s : ident) (n : nat) : ident :=
  match n with
  | 0 => s
  | S n => make_name s n
  end.

Definition get_ident (x : aname) : ident :=
  match x.(binder_name) with
  | nNamed s => s
  | _ => "Error"
  end.

Definition make_list {A} (f : nat -> A) (n : nat) : list A :=
  mapi (fun i a => f i) (repeat 0 n).

(* Computes the list [tVar "A1", ..., tVar "Ak"] where A1, ... Ak are the parameters *)
Definition gen_list_param (params : context) : list term :=
  map (fun param => tVar (get_ident param.(decl_name)))
      (rev params). (*Pamaters need to be inversed as context are inversed *)

(* Computes the list [tVar "i1", ..., tVar "ik"] representing indices *)
Definition gen_list_indices (indices : context) : list term :=
  mapi (fun i _ => tVar (make_name "i" i)) indices.

(* Computes the list [tVar "x1", ..., tVar "xk"] representing arguments *)
Definition gen_list_args (args : context) : list term :=
  mapi (fun i _ => tVar (make_name "x" i)) args.