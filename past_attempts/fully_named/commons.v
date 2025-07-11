From MetaRocq.Template Require Import All.

From RecNamed Require Import naming.

Require Import List.
Import ListNotations.


(* Records *)
Record one_param_env : Type := mk_one_param_env
 { ep_kname : kername ;
   ep_body : mutual_inductive_body ;
   ep_pkname : kername ;
   ep_tkname : kername;
}.

Definition param_env := list one_param_env.

Record output_univ : Type := mk_output_univ
  { out_univ  : term;
    out_relev : relevance
  }.

Record preprocess_mutual_inductive_body : Type := mk_mdecl
  { (* The inductive type being considered *)
    pmb_kname     : kername ;
    pmb_pos_idecl : nat ;
    (* uniform parameters *)
    pmb_uparams    : context ;
    pmb_nb_uparams : nat ;
    (* non uniform parameters *)
    pmb_nuparams    : context;
    pmb_nb_nuparams : nat;
    (* rest inductive *)
    pmb_ind_bodies : list one_inductive_body;
  }.


(* Lemma *)

Definition isSome {A} (x : option A) : bool :=
  match x with
  | None => false
  | Some _ => true
  end.

Fixpoint fold_right_i_aux {A B} (f : nat -> B -> A -> A) (a0 : A) (l : list B)
  (i : nat) : A :=
   match l with
   | [] => a0
   | h :: q => f i h (fold_right_i_aux f a0 q (S i))
   end.

Definition fold_right_i {A B} (f : nat -> B -> A -> A) (a0 : A) (l : list B) : A
  := fold_right_i_aux f a0 l 0.

Definition list_tVar (naming : nat -> ident) (cxt :context) : list term :=
  mapi (fun i a => tVar (naming i)) cxt.

Definition list_tVar_let (naming : nat -> ident) (cxt :context) : list term :=
  fold_right_i (fun pos arg next =>
    if isSome arg.(decl_body) then next else tVar (naming pos) :: next
  ) [] (rev cxt).


Section MakeTerms.

  Context (kname : kername).
  Context (pos_block : nat).

  (* Builds: Ind A1 ... An B0 ... Bm i1 ... il *)
  Definition make_ind (uparams nuparams indices : context) : term :=
    mkApps (tInd (mkInd kname pos_block) [])
           (   list_tVar naming_uparam uparams
            ++ list_tVar naming_nuparam nuparams
            ++ list_tVar naming_indice indices).


  (* Builds: P_i B0 ... Bm i1 ... il *)
  Definition make_predc (nuparams : context) (tindices : list term) : term :=
    mkApps (tVar (naming_pred pos_block))
           (list_tVar naming_nuparam nuparams ++ tindices).

  (* Builds: P_i B0 ... Bm i1 ... il *)
  Definition make_predt (tnuparams tindices : list term) : term :=
    mkApps (tVar (naming_pred pos_block))
           (tnuparams ++ tindices).

  (* Builds: Cst A1 ... An B0 ... Bm *)
  Definition make_cst (pos_ctor : nat) (uparams nuparams : context) : term :=
    mkApps (tConstruct (mkInd kname pos_block) pos_ctor [])
         (   list_tVar naming_uparam uparams
          ++ list_tVar naming_nuparam nuparams ).

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

  Definition closure_uparams  := closure_context aname_uparam op_fold_id.
  Definition closure_nuparams := closure_context aname_nuparam op_fold_id.
  Definition closure_indices  := closure_context aname_indice op_fold_id.
  Definition closure_args_op op_fold := closure_context aname_arg op_fold.

End ComputeClosure.

Definition relev_sort (U : term) : relevance :=
  match U with
  | tSort sSProp => Irrelevant
  | _ => Relevant
  end.