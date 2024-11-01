From RecAPI Require Import api_debruijn.


Unset Guard Checking.

Section PreprocessParameters.

  Context (kname : kername).
  Context (mdecl : mutual_inductive_body).
  Context (E : global_env).

  Definition nb_params := mdecl.(ind_npars).


(* Extra functions as we don't know the number of uparams which is neccassary for the api *)
#[local] Definition get_all_args : mutual_inductive_body -> list context :=
  fun mdelc => map cstr_args (concat (map ind_ctors mdecl.(ind_bodies))).


Definition first_false : list bool -> nat :=
  let fix aux n l :=
  match l with
  | true :: l => aux (S n) l
  | _ => n
  end in
  aux 0.

Definition default_value := nb_params.


Section CheckUniform.

  Context (id_inds   : list ident).
  Context (id_params : list ident).

  (* 1. Compute the number of uniform params for an instance *)
  Definition check_term : ident -> term -> state -> bool :=
    fun id tm s => eqb (get_term id s) tm.

  Definition check_uniform : list ident -> list term -> state -> nat :=
    fun id_params tm s =>
    first_false (map2 (fun x y => check_term x y s) id_params tm).
    (* default_value. *)

  (* 2. Compute the number of uniform parameters of an argument *)
  #[using="All"]
  Fixpoint preprocess_uparams_arg (ty : term) (s : state) {struct ty} : _ :=
    (* default_value. *)
    let (hd, iargs) := decompose_app ty in
    match hd with
    (* Check for local arg *)
    | tProd an A B => let* id_local s := add_old_var (Some "local_arg") (mkdecl an None A) s in
                      preprocess_uparams_arg B s
    | tLetIn an A db B => let* id_local s := add_old_var (Some "local_let") (mkdecl an None A) s in
                          preprocess_uparams_arg B s
    (* Check if is the inductive *)
    | tRel n => if check_ids n id_inds s
                then check_uniform id_params (firstn nb_params iargs) s
                else default_value
    (* Otherwise if it is nested *)
    | tInd (mkInd kname_indb pos_indb) _ =>
        fold_right min default_value (map (fun x => preprocess_uparams_arg x s) iargs)
    | _ => default_value
    end.

End CheckUniform.


(* 3. Compute the number of uniform parameters of an inductive type *)
#[using="All"] Definition preprocess_uparams : nat :=
  let s := init_state in
  let* id_inds s := add_inds mdecl s in
  let* _ id_params _ s := add_old_context (Some "params") mdecl.(ind_params) s in
  check_ctors_by_arg min default_value E (preprocess_uparams_arg id_inds id_params) (get_all_args mdecl) s.


(* 4. Debug functions *)
Section Debug.

  Context (id_inds   : list ident).
  Context (id_params : list ident).

  #[using="All"]
  Fixpoint debug_preprocess_uparams_arg (ty : term) (s : state) {struct ty} : term :=
    let (hd, iargs) := decompose_app ty in
    match hd with
    (* Check for local arg *)
    | tProd an A B => let* id_local s := add_old_var (Some "local_arg") (mkdecl an None A) s in
                      debug_preprocess_uparams_arg B s
    | tLetIn an A db B => let* id_local s := add_old_var (Some "local_let") (mkdecl an None A) s in
                          debug_preprocess_uparams_arg B s
    (* Check if is the inductive *)
    | tRel n => mkApps (tVar "DEBUG CASE tRel:")
                  [ (state_to_term s) ;
                    (mkApp (tVar "DEBUG tRel case, type := ") ty)
                  ]
                (* if check_ids n id_inds s
                then check_uniform id_params (firstn nb_params iargs) s
                else default_value *)
    (* Otherwise if it is nested *)
    | tInd (mkInd kname_indb pos_indb) _ =>
        mkApps (tVar "nested") (map (fun x => debug_preprocess_uparams_arg x s) iargs)
    | _ => mkApp ty (state_to_term s)
        end.

End Debug.

#[using="All"] Definition debug_preprocess_uparams : _ :=
  let s := init_state in
  let* id_inds s := add_inds mdecl s in
  let* _ id_params _ s := add_old_context (Some "params") mdecl.(ind_params) s in
  debug_check_ctors_by_arg E (debug_preprocess_uparams_arg id_inds id_params) (get_all_args mdecl) s.

End PreprocessParameters.
