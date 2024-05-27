From MetaCoq.Template Require Import All.

Require Import preliminary.
Require Import namming.

Require Import List.
Import ListNotations.

Definition AnonRel := {| binder_name := nAnon; binder_relevance := Relevant |}.
Definition tProdAnon t1 t2 := tProd AnonRel t1 t2.
Infix "t->" := tProdAnon (at level 60, right associativity).

(* Gathering all the constructors of the form (cb_block, cb_ctor, ctor) *)
Definition gather_ctors (mdecl : mutual_inductive_body) : _ :=
  concat( mapi (fun cb_block indb =>
            mapi (fun cb_ctor ctor => (cb_block, cb_ctor, ctor))
            indb.(ind_ctors))
          mdecl.(ind_bodies)).

Section MakeTerms.

  Context (kname : kername).
  Context (params : context).
  Context (pos_block : nat).

  (* Builds: Ind A1 ... An i1 ... il *)
  Definition make_ind (pos_block : nat) (indices : context) : term :=
    tApp (tInd (mkInd kname pos_block) [])
          (list_tVar naming_param params ++ list_tVar naming_indice indices).

  (* Builds: P_i i1 ... il *)
  Definition make_pred (pos_block : nat) (tindices : list term) : term :=
    tApp (tVar (naming_pred pos_block)) tindices.

  (* Builds: Cst A1 ... An *)
  Definition make_cst (pos_block pos_ctor : nat) : term :=
    tApp (tConstruct (mkInd kname pos_block) pos_ctor [])
         (list_tVar naming_param params).

End MakeTerms.


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
                    (fun i param => aname_param i)
                    (fun _ param => param.(decl_type)).

  Definition closure_indices (indices : context) : term -> term :=
    compute_closure (rev indices) op_fold_id
                    (fun i _ => aname_indice i)
                    (fun _ indice => indice.(decl_type)).

  Definition closure_args_op (args : context) (op_fold : nat -> term -> term -> term) :=
    compute_closure (rev args) op_fold
                    (fun i _ => aname_arg i)
                    (fun _ arg => arg.(decl_type)).

End ComputeClosure.


