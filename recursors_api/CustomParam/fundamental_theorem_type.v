From RecAPI Require Import api_debruijn.
From RecAPI Require Import custom_parametricity.

Section CustomParam.

  Context (kname : kername).
  Context (mdecl : mutual_inductive_body).
  Context (nb_uparams : nat).
  Context (strpos_uparams : list bool).
  Context (knamep : kername).
  Context (E : global_env).
  Context (Ep : param_env).


Definition closure_uparams_preds_hold binder : (list (context_decl * bool)) -> state ->
    (list ident -> list ident -> list ident -> list ident -> state -> term) -> term :=
  fold_right_state_opt4
    (fun _ ' (mkdecl an db ty, b) s t =>
      (* add old_param *)
      let* id_uparam s <- kp_binder binder an ty (Some "uparams") s in
      (* add a predicate and that it holds *)
      match b with
      | false => t [id_uparam] [] [id_uparam] [] s
      | true =>
          (* add pred *)
          let nameP := name_map (fun x => ("P" ^ x)) an.(binder_name) in
          let ty_pred := tProd (mkBindAnn nAnon Relevant) (get_term id_uparam s) (tSort sProp) in
          let* id_pred s <- mk_binder binder (mkBindAnn nameP Relevant) ty_pred (Some "preds") s in
          (* add it holds *)
          let nameHP := name_map (fun x => ("HP" ^ x)) an.(binder_name) in
          let ty_pred_holds :=
            ( let* _ s <- mk_tProd (mkBindAnn nAnon Relevant) (get_term id_uparam s) None s in
              (mkApp (get_term id_pred s) (tRel 0)))
              in
          let* id_pred_holds s <- mk_binder binder (mkBindAnn nameHP Relevant) ty_pred_holds (Some "preds_hold") s in
          t [id_uparam] [id_pred] [id_pred; id_uparam] [id_pred_holds] s
      end
    ).


  (* 2. Return type *)
  Section mkReturnType.

  Context (id_uparams : list ident).
  Context (id_uparams_preds : list ident).

  Definition make_return_type : nat -> state -> term :=
    fun pos_indb s =>
    let* id_nuparams s <- closure_nuparams tProd kname s in
    let* id_indices  s <- closure_indices tProd kname pos_indb s in
    let* id_VarMatch s <- mk_tProd (mkBindAnn (nNamed "x") (get_relevance kname pos_indb s))
        (make_ind kname pos_indb id_uparams id_nuparams id_indices s) (Some "VarMatch") s in
    mkApp (make_ind knamep pos_indb id_uparams_preds id_nuparams id_indices s)
            (get_term id_VarMatch s).

  End mkReturnType.

(* 3. Compute the type of the fundamental theorem *)
Definition fundamental_theorem_type (pos_indb : nat) : term :=
  (* add inds to state *)
  let s := add_mdecl kname nb_uparams mdecl init_state in
  let annoted_uparams := combine (rev (get_uparams kname s)) strpos_uparams in
  let* s <- replace_ind kname s in
  (* 2. add uparams + extra predicate *)
  let* id_uparams id_preds id_uparams_preds _ s <- closure_uparams_preds_hold tProd annoted_uparams s in
  make_return_type id_uparams id_uparams_preds pos_indb s.


End CustomParam.