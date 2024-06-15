From MetaCoq.Template Require Import All.

Require Import Bool Nat List.
Import ListNotations.

Require Import naming.
Require Import commons.


Section PreprocessParameters.

  Context (kname : kername).
  Context (pos_idecl : nat).
  Context (mdecl : mutual_inductive_body).

  Definition nb_params := mdecl.(ind_npars).

  (* Collects arguments and turn them to telescope *)
  Definition args_ctors : list context :=
    map (fun x => rev x.(cstr_args)) (concat (map ind_ctors mdecl.(ind_bodies))).



(* 1. Compute which parameters are uniform *)
Fixpoint check_uniform_aux (shift : nat) (pos_param : nat) (params : list term) : nat :=
  match params with
  | nil => nb_params
  | p ::l =>
    match p with
    | tRel k => if k =? (shift + (nb_params - pos_param))
                then check_uniform_aux shift (S pos_param) l
                else S pos_param
    | _ => S pos_param
    end
  end.

Definition check_uniform (shift : nat) (params : list term) := 0.
(* check_uniform_aux shift 0 params. *)

Definition preprocess_types (shift : nat) (ty : term) : nat :=
  let (hd, iargs) := decompose_app ty in
  match hd with
    | tRel k =>
        if shift + nb_params <=? k
        then check_uniform shift (firstn nb_params iargs)
        else nb_params
    | _ => 0
    end.


(* 2. Returns the number of uniform parameters *)
Fixpoint preprocess_args_aux (pos_ctor pos_arg : nat) (args : context) (lets : context) :=
  match args with
  | [] => nb_params
  | arg::args => if isSome arg.(decl_body)
              then preprocess_args_aux pos_ctor (S pos_arg) args (arg::lets)
              (* Lets and hnf ??? Where ??? How ??? *)
              else min (preprocess_types (pos_ctor + pos_arg) arg.(decl_type))
                       (preprocess_args_aux pos_ctor (S pos_arg) args lets)
  end.

Definition preprocess_args pos_ctor args := preprocess_args_aux pos_ctor 0 args [].

Definition preprocess_ctors : nat := 0.
  (* fold_right min nb_params (mapi preprocess_args args_ctors). *)


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

End PreprocessParameters.