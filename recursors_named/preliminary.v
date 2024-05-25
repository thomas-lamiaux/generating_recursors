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

(* Definition make_name0 (s : ident) (n : nat) : ident :=
  match n with
  | 0 => s
  | S n => make_name s n
  end. *)

Definition make_name_bin (s : ident) (n m : nat) :=
  String.append s (String.append (string_of_nat n) (string_of_nat m)).

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


(* 1. Different closure functions *)
Section ComputeClosure.

  Context (binder : aname -> term -> term -> term).

  Definition compute_closure {A} (l : list A) (op_fold : nat -> term -> term -> term)
    (naming : nat -> A -> aname) (typing : nat -> A -> term) (next : term) : term :=
    fold_right_i
    (fun i a next_closure =>
      binder (naming i a) (typing i a) (op_fold i (typing i a) next_closure))
    next
    l.

  Definition op_fold_id : nat -> term -> term -> term := fun _ _ x => x.

  Definition closure_param (params : context) : term -> term  :=
    compute_closure (rev params) op_fold_id
                    (fun _ param => param.(decl_name))
                    (fun _ param => param.(decl_type)).

  Definition closure_indices (indices : context) : term -> term :=
    compute_closure (rev indices) op_fold_id
                    (fun i indice => make_raname (make_name "i" i))
                    (fun _ indice => indice.(decl_type)).

  Definition closure_args_op (args : context) (op_fold : nat -> term -> term -> term) :=
    compute_closure (rev args) op_fold
                    (fun i arg => make_raname (make_name "x" i))
                    (fun _ arg => arg.(decl_type)).

End ComputeClosure.


Section MakeTerms.

  Context (kname : kername).
  Context (params : context).
  Context (pos_block : nat).

  (* Builds: Ind A1 ... An i1 ... il *)
  Definition make_ind (pos_block : nat) (indices : context) : term :=
    tApp (tInd (mkInd kname pos_block) [])
          (gen_list_param params ++ gen_list_indices indices).

  (* Builds: P_i i1 ... il *)
  Definition make_pred (pos_block : nat) (tindices : list term) : term :=
    tApp (tVar (make_name "P" pos_block)) tindices.

  (* Builds: Cst A1 ... An *)
  Definition make_cst (pos_block pos_ctor : nat) : term :=
    tApp (tConstruct (mkInd kname pos_block) pos_ctor [])
          (gen_list_param params).

End MakeTerms.