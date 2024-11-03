From RecAPI Require Import api_debruijn.
From RecAPI Require Import custom_parametricty_rec_call.
From RecAPI Require Import custom_parametricity.
From RecAPI Require Import fundamental_theorem_type.

Definition make_name : ident -> nat -> ident :=
  fun s n => s ^ (string_of_nat n).

Section CustomParam.

  Context (kname : kername).
  Context (mdecl : mutual_inductive_body).
  Context (nb_uparams : nat).
  Context (strpos_uparams : list bool).
  Context (knamep : kername).
  Context (U : output_univ).
  Context (E : global_env).
  Context (Ep : param_env).

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


Definition mk_case_pred knamep id_uparams_preds id_nuparams pos_indb id_indices id_VarMatch s : term :=
  mkApp (make_ind knamep pos_indb id_uparams_preds id_nuparams id_indices s)
        (get_term id_VarMatch s).


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
  let tFix_type pos_indb := make_return_type kname knamep id_uparams id_uparams_preds pos_indb s in
  let tFix_rarg := tFix_default_rarg kname s in
  let* id_fixs pos_indb s := mk_tFix kname tFix_type tFix_rarg pos_indb s in
  (* 3. closure nuparams + indices + var match *)
  let* id_nuparams s := closure_nuparams tLambda kname s in
  let* id_indices  s := closure_indices  tLambda kname pos_indb s in
  let* id_VarMatch s := mk_tLambda (mkBindAnn (nNamed "x") (get_relevance kname pos_indb s))
                        (make_ind kname pos_indb id_uparams id_nuparams id_indices s)
                        (Some "VarMatch") s in
  (* 4. match VarMatch *)
  let tCase_pred := mk_case_pred knamep id_uparams_preds id_nuparams pos_indb in
  let* pos_ctor _ id_args _ s := mk_tCase kname pos_indb tCase_pred
                          id_uparams id_nuparams (get_term id_VarMatch s) s in
  (* 5. Conclude *)
  (mkApps (make_cst knamep pos_indb pos_ctor id_uparams_preds id_nuparams s)
          (compute_args_fix id_uparams id_preds id_uparams_preds id_preds_hold
            id_fixs id_args s)).


End CustomParam.