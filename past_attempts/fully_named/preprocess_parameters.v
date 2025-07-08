From MetaRocq.Template Require Import All.

Require Import Bool Nat List.
Import ListNotations.

From RecNamed Require Import naming.
From RecNamed Require Import commons.


Unset Guard Checking.

Section PreprocessParameters.

  Context (kname : kername).
  Context (pos_idecl : nat).
  Context (mdecl : mutual_inductive_body).

  Definition nb_params := mdecl.(ind_npars).

  (* Note DeBruijn => nb_block -1 + nb_params >-> nb_params
     Note Param    => nb_params - 1 <-> 0
     Shift        <=> nb arg seen
  *)

  (* Collects arguments and turn them to telescope *)
  Definition args_ctors : list context :=
    map (fun x => rev x.(cstr_args)) (concat (map ind_ctors mdecl.(ind_bodies))).


(* 1. Compute which parameters are uniform *)
Fixpoint check_uniform_aux (pos_arg : nat) (pos_param : nat) (params : list term) : nat :=
  match params with
  | nil => nb_params
  | p ::l =>
    match p with
    | tRel k => if k =? (pos_arg + (nb_params - pos_param -1))
                then check_uniform_aux pos_arg (S pos_param) l
                else pos_param
    | _ => pos_param
    end
  end.

Definition check_uniform (pos_arg : nat) (params : list term) :=
  check_uniform_aux pos_arg 0 params.

Fixpoint preprocess_types (pos_arg : nat) (ty : term) {struct ty} : nat :=
  let (hd, iargs) := decompose_app ty in
  match hd with
    | tRel k =>
        (* If it is the inductive type at hand *)
        if pos_arg + nb_params <=? k
        then check_uniform pos_arg (firstn nb_params iargs)
        else nb_params
        (* If it is nested *)
    | tInd _ _ => fold_right min nb_params (map (fun ty => preprocess_types pos_arg ty) iargs)
    | _ => nb_params
    end.

(* 2. Returns the number of uniform parameters *)
Fixpoint preprocess_args_aux (pos_arg : nat) (args : context) (cxt : context) :=
  match args with
  | [] => nb_params
  | arg::args =>
      if isSome arg.(decl_body)
      then preprocess_args_aux (S pos_arg) args (arg::cxt)
      (* Lets and hnf ??? Where ??? How ??? *)
      else
      let ht := arg.(decl_type) in
      (* let ht := expand_lets cxt arg.(decl_type) in *)
           min (preprocess_types pos_arg ht)
               (preprocess_args_aux (S pos_arg) args (arg::cxt))
  end.

Definition preprocess_args args := preprocess_args_aux 0 args [].

Definition preprocess_ctors : nat :=
  fold_right min nb_params (map preprocess_args args_ctors).


(* 3. Return *)
Definition preprocess_parameters : preprocess_mutual_inductive_body :=
  let n := preprocess_ctors in
  let revparams := rev mdecl.(ind_params) in
  {| pmb_kname := kname ;
     pmb_pos_idecl := pos_idecl ;
     (* uniform parameters *)
     pmb_uparams    := rev (firstn n revparams) ;
     pmb_nb_uparams := n ;
     (* non uniform parameters *)
     pmb_nuparams    := rev (skipn n revparams)  ;
     pmb_nb_nuparams := nb_params - n ;
     (* rest inductive *)
     pmb_ind_bodies := mdecl.(ind_bodies);
  |}.






(* DEBUG functions: accumulates value rather than taking the min *)
Fixpoint debug_args_aux (pos_arg : nat) (args : context) (lets : context) :=
  match args with
  | [] => []
  | arg::args =>
      if isSome arg.(decl_body)
      then debug_args_aux (S pos_arg) args (arg::lets)
      (* Lets and hnf ??? Where ??? How ??? *)
      else cons (preprocess_types pos_arg arg.(decl_type))
                (debug_args_aux (S pos_arg) args lets)
  end.

Definition debug_args args := debug_args_aux 0 args [].

Definition debug_nuparams : _ := map debug_args args_ctors.

End PreprocessParameters.
