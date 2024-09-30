From RecAPI Require Import api_debruijn.


Unset Guard Checking.

Section PreprocessParameters.

  Context (kname : kername).
  Context (pos_indb : nat).
  Context (mdecl : mutual_inductive_body).
  Context (E : global_env).

  Definition nb_params := mdecl.(ind_npars).


(* 1. Compute the number of uniform params *)
Definition check_uniform : list term -> info -> nat :=
  let fix aux n args e :=
  match args with
  | [] => nb_params
  | tRel pos_var :: args =>
      if check_var_pos "params" n pos_var e then aux (S n) args e else pos_var
  | _ => n
  end in aux 0.


(* 2. Compute the number of uniform parameters of an argument *)
Fixpoint preprocess_uparams_arg (ty : term) (e : info) {struct ty} :  nat :=
  let (hd, iargs) := decompose_app ty in
  match hd with
  | tProd an A B => let e' := add_old_var (Some "local") (mkdecl an None A) e
                    in preprocess_uparams_arg B e'
  | tInd (mkInd kname_indb pos_indb) _ =>
     if eqb kname kname_indb
     then check_uniform (firstn nb_params iargs) e
     else fold_right min nb_params (map (fun x => preprocess_uparams_arg x e) iargs)
  | _ => nb_params
  end.


(* 3. Compute the number of uniform parameters of an inductive type *)
Definition preprocess_uparams : nat :=
  let e := init_info in
  let e := replace_ind kname mdecl e in
  let e := add_old_context (Some "params") mdecl.(ind_params) e in
  check_ctors_by_arg min nb_params E preprocess_uparams_arg (get_args mdecl) e.


(* 4. Debug functions *)
  (* Fixpoint debug_preprocess_uparams_arg (ty : term) (e : info) {struct ty} : _ :=
    let (hd, iargs) := decompose_app ty in
    match hd with
    | tProd an A B => let e' := add_old_var (Some "local") (mkdecl an None A) e
                      in debug_preprocess_uparams_arg B e'
    | tInd (mkInd kname_indb pos_indb) _ =>
       if eqb kname kname_indb
       then [2000]
       (* (mapi (fun i tm => check_uniform tm i e) (firstn nb_params iargs)) *)
       (* will bug for nesting *)
       else []
    | _ => []
    end. *)

Definition debug_preprocess_uparams : _ :=
  let e := init_info in
  let e := replace_ind kname mdecl e in
  let e := add_old_context (Some "params") mdecl.(ind_params) e in
  debug_check_ctors_by_arg E preprocess_uparams_arg (get_args mdecl) e.

End PreprocessParameters.
