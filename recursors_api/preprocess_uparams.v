From RecAPI Require Import api_debruijn.
From RecAPI Require Import commons.


Unset Guard Checking.

Section PreprocessParameters.

  Context (kname : kername).
  Context (pos_indb : nat).
  Context (mdecl : mutual_inductive_body).

  Definition nb_params := mdecl.(ind_npars).


  (* Note DeBruijn => nb_block -1 + nb_params >-> nb_params
     Note Param    => nb_params - 1 <-> 0
     Shift        <=> nb arg seen
  *)

(* 0. Collects the arguments and turn them to telescope *)
Definition args_ctors : list context :=
  map (fun x => rev x.(cstr_args)) (concat (map ind_ctors mdecl.(ind_bodies))).


(* 1. Compute which parameters are uniform *)
Definition check_uniform (pos_arg : nat) (params : list term) : nat :=
  let fix aux pos_param params :=
  match params with
  | nil => nb_params
  | p ::l =>
    match p with
    | tRel k => if k =? (pos_arg + (nb_params - pos_param -1))
                then aux (S pos_param) l
                else pos_param
    | _ => pos_param
    end
  end
  in aux 0 params.


(* 2. Compute the number of uniform parameters of an argument *)
Fixpoint preprocess_types (pos_arg : nat) (ty : term) {struct ty} : nat :=
  let (hd, iargs) := decompose_app ty in
  match hd with
    (* 1. If it is a function *)
    | tProd _ _ B => preprocess_types (S pos_arg) B
    (* 2. If it is the inductive type at hand *)
    | tRel k => if pos_arg + nb_params <=? k
                then check_uniform pos_arg (firstn nb_params iargs)
                else nb_params
    (* 3. If it is nested *)
    | tInd _ _ => fold_right min nb_params (map (fun ty => preprocess_types pos_arg ty) iargs)
    | _ => nb_params
  end.


(* 3. Compute the number of uniform parameters of a constructor *)
Definition preprocess_args (args : context) :=
  let fix aux pos_arg args cxt :=
  match args with
  | [] => nb_params
  | arg::args =>
      if isSome arg.(decl_body)
      then aux (S pos_arg) args (arg::cxt)
      (* Lets and hnf ??? Where ??? How ??? *)
      else
      let ht := arg.(decl_type) in
      (* let ht := expand_lets cxt arg.(decl_type) in *)
           min (preprocess_types pos_arg ht)
               (aux (S pos_arg) args (arg::cxt))
  end
  in aux 0 args [].


(* 4. Compute the number of uniform parameters of an inductive type *)
Definition preprocess_ctors : nat :=
  fold_right min nb_params (map preprocess_args args_ctors).


(* 5. Preprocess an inductive type *)
Definition preprocess_parameters : preprocess_mutual_inductive_body :=
  let n := preprocess_ctors in
  let revparams := rev mdecl.(ind_params) in
  {| pmb_kname := kname ;
     pmb_pos_indb := pos_indb ;
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
Definition debug_args (args : context) :=
  let fix debug_args_aux pos_arg args lets :=
  match args with
  | [] => []
  | arg::args =>
      if isSome arg.(decl_body)
      then debug_args_aux (S pos_arg) args (arg::lets)
      (* Lets and hnf ??? Where ??? How ??? *)
      else cons (preprocess_types pos_arg arg.(decl_type))
                (debug_args_aux (S pos_arg) args lets)
  end
  in debug_args_aux 0 args [].

Definition debug_nuparams : _ := map debug_args args_ctors.

End PreprocessParameters.
