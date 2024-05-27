From MetaCoq.Template Require Import All.

Require Import preliminary.
Require Import naming.

Require Import List.
Import ListNotations.

Definition list_tVar (naming : nat -> ident) (cxt :context) : list term :=
  mapi (fun i a => tVar (naming i)) cxt.

Section MakeTerms.

  Context (kname : kername).
  Context (params : context).
  Context (pos_block : nat).

  (* Builds: Ind A1 ... An i1 ... il *)
  Definition make_ind (indices : context) : term :=
    tApp (tInd (mkInd kname pos_block) [])
          (list_tVar naming_param params ++ list_tVar naming_indice indices).

  (* Builds: P_i i1 ... il *)
  Definition make_pred (tindices : list term) : term :=
    tApp (tVar (naming_pred pos_block)) tindices.

  (* Builds: Cst A1 ... An *)
  Definition make_cst (pos_ctor : nat) : term :=
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

  Definition closure_context (naming : nat -> context_decl -> aname)
   (op_fold : nat -> term -> term -> term) (cxt : context) : term -> term :=
  compute_closure (rev cxt) op_fold naming (fun _ a => decl_type a) .

  Definition closure_params := closure_context aname_param op_fold_id.
  Definition closure_indices := closure_context aname_indice op_fold_id.
  Definition closure_args_op op_fold   := closure_context aname_arg op_fold.

End ComputeClosure.

Definition decide_rec_call (kname : kername) (nb_params : nat) (arg_type : term) : option (nat * list term) :=
  let '(hd, iargs) := decompose_app arg_type in
  match hd with
  | tInd {|inductive_mind := s; inductive_ind := pos_indb' |} _
      => if eq_constant kname s
        then Some (pos_indb', skipn nb_params iargs)
        else None
  | _ => None
  end.
