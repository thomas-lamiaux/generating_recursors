From RecAPI Require Import api_debruijn.
From RecAPI Require Import custom_parametricity.
From RecAPI Require Import custom_parametricty_rec_call.


Section FdTheorem.

  Context (kname : kername).
  Context (mdecl : mutual_inductive_body).
  Context (nb_uparams : nat).
  Context (strpos_uparams : list bool).
  Context (knamep : kername).
  Context (E : global_env).
  Context (Ep : param_env).


  Section GenTypes.

  Context (binder : aname -> term -> term -> term).

  Definition closure_uparams_preds_hold : (list (context_decl * bool)) -> state ->
      (list ident -> list ident -> list ident -> list ident -> state -> term) -> term :=
    fold_right_state_opt4
      (fun _ ' (mkdecl an db ty, b) s t =>
        (* add old_param *)
        let* id_uparam s := kp_binder binder an ty (Some "uparams") s in
        (* add a predicate and that it holds *)
        match b with
        | false => t [id_uparam] [] [id_uparam] [] s
        | true =>
            (* add pred *)
            let nameP := name_map (fun x => ("P" ^ x)) an.(binder_name) in
            let ty_pred := tProd (mkBindAnn nAnon Relevant) (get_term id_uparam s) (tSort sProp) in
            let* id_pred s := mk_binder binder (mkBindAnn nameP Relevant) ty_pred (Some "preds") s in
            (* add it holds *)
            let nameHP := name_map (fun x => ("HP" ^ x)) an.(binder_name) in
            let ty_pred_holds :=
              ( let* id_varPred s := mk_tProd (mkBindAnn nAnon Relevant) (get_term id_uparam s) None s in
                                              (mkApp (get_term id_pred s) (get_term id_varPred s)))
                in
            let* id_pred_holds s := mk_binder binder (mkBindAnn nameHP Relevant) ty_pred_holds (Some "preds_hold") s in
            t [id_uparam] [id_pred] [id_pred; id_uparam] [id_pred_holds] s
        end
      ).


  (* 2. Return type *)
  Section mkReturnType.

  Context (id_uparams : list ident).
  Context (id_uparams_preds : list ident).
  Context (pos_indb : nat).

  Definition make_ccl : list ident -> list ident -> ident -> state -> term :=
    fun id_nuparams id_indices id_VarMatch s =>
    mkApp (make_ind knamep pos_indb id_uparams_preds id_nuparams id_indices s)
    (get_term id_VarMatch s).

  Definition make_return_type : state -> term :=
    fun s =>
    let* id_nuparams s := closure_nuparams tProd kname s in
    let* id_indices  s := closure_indices tProd kname pos_indb s in
    let* id_VarMatch s := mk_tProd (mkBindAnn (nNamed "x") (get_relevance kname pos_indb s))
        (make_ind kname pos_indb id_uparams id_nuparams id_indices s) (Some "VarMatch") s in
    make_ccl id_nuparams id_indices id_VarMatch s.

  End mkReturnType.

  End GenTypes.


(* ############################################### *)
(*    2. Make the type of the fundamental lemma    *)
(* ############################################### *)

Definition fundamental_theorem_type (pos_indb : nat) : term :=
  (* 0. initialise state with inductives *)
  let s := add_mdecl kname nb_uparams mdecl init_state in
  let annoted_uparams := combine (rev (get_uparams kname s)) strpos_uparams in
  let* s := replace_ind kname s in
  (* 1. Closure param + preds *)
  let* id_uparams id_preds id_uparams_preds _ s := closure_uparams_preds_hold tProd annoted_uparams s in
  (* 2. Ccl *)
  make_return_type id_uparams id_uparams_preds pos_indb s.




(* ################################### *)
(*    3. Make the fundamental lemma    *)
(* ################################### *)


  Section GetRecCall.

  Context (id_uparams : list ident).
  Context (id_preds : list ident).
  Context (id_uparams_preds : list ident).
  Context (id_preds_hold : list ident).
  Context (id_fixs : list ident).

  Definition make_indp : nat -> list ident -> list term -> list term -> state -> term :=
    fun pos_indb id_uparams_preds nuparams indices s =>
    mkApps (tInd {| inductive_mind := knamep; inductive_ind := pos_indb |} [])
    (get_terms id_uparams_preds s ++ nuparams ++ indices).

  Definition compute_args_fix : list ident -> state -> list term :=
    fun id_args s =>
    fold_right (fun id_arg t =>
      let red_ty := reduce_except_lets E s (get_type id_arg s) in
      match make_cparam_call make_indp kname Ep id_uparams id_preds
              id_uparams_preds id_preds_hold id_fixs id_arg red_ty s with
      | Some (rc_ty, rc_tm) => (get_term id_arg s) :: rc_tm :: t
      | None => (get_term id_arg s) :: t
      end
    ) [] id_args.

End GetRecCall.


(* 3. Compute the custom parametricty  *)
Definition fundamental_theorem_term (pos_indb : nat) : term :=
  (* 0. initialise state with inductives *)
  let s := add_mdecl kname nb_uparams mdecl init_state in
  let annoted_uparams := combine (rev (get_uparams kname s)) strpos_uparams in
  let* s := replace_ind kname s in
  (* 1. add uparams + extra predicate *)
  let* id_uparams id_preds id_uparams_preds id_preds_hold s :=
        closure_uparams_preds_hold tLambda annoted_uparams s in
  (* 2. fixpoint *)
  let tFix_type pos_indb := make_return_type id_uparams id_uparams_preds pos_indb s in
  let tFix_rarg := tFix_default_rarg kname s in
  let* id_fixs pos_indb s := mk_tFix kname tFix_type tFix_rarg pos_indb s in
  (* 3. closure nuparams + indices + var match *)
  let* id_nuparams s := closure_nuparams tLambda kname s in
  let* id_indices  s := closure_indices  tLambda kname pos_indb s in
  let* id_VarMatch s := mk_tLambda (mkBindAnn (nNamed "x") (get_relevance kname pos_indb s))
                        (make_ind kname pos_indb id_uparams id_nuparams id_indices s)
                        (Some "VarMatch") s in
  (* 4. match VarMatch *)
  let tCase_pred := make_ccl id_uparams_preds pos_indb id_nuparams in
  let* pos_ctor _ id_args _ s := mk_tCase kname pos_indb tCase_pred
                          id_uparams id_nuparams (get_term id_VarMatch s) s in
  (* 5. Conclude *)
  (mkApps (make_cst knamep pos_indb pos_ctor id_uparams_preds id_nuparams s)
          (compute_args_fix id_uparams id_preds id_uparams_preds id_preds_hold
            id_fixs id_args s)).


End FdTheorem.