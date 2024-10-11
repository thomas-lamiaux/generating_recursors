From RecAPI Require Import api_debruijn.





Unset Guard Checking.

Section PreprocessParameters.

  Context (kname : kername).
  Context (pos_indb : nat).
  Context (mdecl : mutual_inductive_body).
  Context (E : global_env).

  Definition nb_params := mdecl.(ind_npars).


(* Extra functions as we don't know the number of uparams which is neccassary for the api *)
#[local] Definition ind_to_cxt : context :=
  map (fun indb => mkdecl (mkBindAnn nAnon indb.(ind_relevance)) None indb.(ind_type))
  (rev mdecl.(ind_bodies)).

#[local] Definition ind_to_terms : list term :=
  mapi (fun i _ => (tInd (mkInd kname i) [])) mdecl.(ind_bodies).

#[local] Definition replace_ind : info -> info :=
  fun e =>
  let ' (_ , id_cxt_inds) := fresh_id_context (Some "inds") e ind_to_cxt in
  add_replace_context id_cxt_inds ind_to_terms e.

Definition first_false : list bool -> nat :=
  let fix aux n l :=
  match l with
  | true :: l => aux (S n) l
  | _ => n
  end in
  aux 0.


  Section CheckUniform.

    Context (id_params : list ident).

    (* 1. Compute the number of uniform params for an instance *)
    Definition check_uniform : list ident -> list term -> info -> nat :=
    fun id_params tm e =>
    first_false (map2 (check_term e) id_params tm).

    (* 2. Compute the number of uniform parameters of an argument *)
    Fixpoint preprocess_uparams_arg (ty : term) (e : info) {struct ty} :  nat :=
      let (hd, iargs) := decompose_app ty in
      match hd with
      | tProd an A B => let id_local := fresh_ident (Some "local") e in
                        let e' := add_old_var id_local (mkdecl an None A) e
                        in preprocess_uparams_arg B e'
      | tInd (mkInd kname_indb pos_indb) _ =>
        if eqb kname kname_indb
        then check_uniform id_params (firstn nb_params iargs) e
        else fold_right min nb_params (map (fun x => preprocess_uparams_arg x e) iargs)
      | _ => nb_params
      end.

  End CheckUniform.


  (* 3. Compute the number of uniform parameters of an inductive type *)
  Definition preprocess_uparams : nat :=
    let e := init_info in
    let e := replace_ind e in
    let ' (id_params, id_cxt_params) := fresh_id_context (Some "params") e mdecl.(ind_params) in
    let e := add_old_context id_cxt_params e in
    check_ctors_by_arg min nb_params E (preprocess_uparams_arg id_params) (get_args mdecl) e.


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
    let e := replace_ind e in
    let ' (id_params, id_cxt_params) := fresh_id_context (Some "params") e mdecl.(ind_params) in
    let e := add_old_context id_cxt_params e in
    debug_check_ctors_by_arg E (preprocess_uparams_arg id_params) (get_args mdecl) e.

End PreprocessParameters.
