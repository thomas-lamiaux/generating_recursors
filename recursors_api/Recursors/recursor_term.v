From RecAPI Require Import api_debruijn.
From RecAPI Require Import commons.
From RecAPI Require Import recursor_rec_call.
From RecAPI Require Import generate_types.


Section GenRecTerm.

Context (kname : kername).
Context (mdecl : mutual_inductive_body).
Context (nb_uparams : nat).
Context (U : output_univ).
Context (E : global_env).
Context (Ep : param_env).


(* 1. Get Args and Rec Call *)

Section GetRecCall.

  Context (id_preds : list ident).
  Context (id_fixs : list ident).

  Definition compute_args_fix : list ident -> state -> list term :=
    fun id_args s =>
    fold_right (fun id_arg t =>
      let red_ty := reduce_except_lets E s (get_type id_arg s) in
      match make_rec_call kname Ep id_preds id_fixs id_arg red_ty s with
      | Some (rc_ty, rc_tm) => (get_term id_arg s) :: rc_tm :: t
      | None => (get_term id_arg s) :: t
      end
    ) [] id_args.

End GetRecCall.


  Definition mk_case_pred id_preds id_nuparams pos_indb id_indices id_VarMatch s :=
    mkApp (make_predn id_preds pos_indb id_nuparams (get_terms id_indices s) s)
          (get_term id_VarMatch s).


  (* 3. Generation Type of the Recursor *)
  Definition gen_rec_term (pos_indb : nat) : term :=
    (* 0. Initialise state with inductives *)
    let s := add_mdecl kname nb_uparams mdecl init_state in
    let* s := replace_ind kname s in
    (* 1. Closure Uparams / preds / ctors *)
    let* id_uparams s := closure_uparams tLambda kname s in
    let* id_preds   s := closure_preds tLambda kname U id_uparams s in
    let* id_ctors   s := closure_ctors tLambda kname U E Ep id_uparams id_preds s in
    (* 2. Fixpoint *)
    let tFix_type pos_indb := make_return_type kname pos_indb id_uparams id_preds s in
    let tFix_rarg := tFix_default_rarg kname s in
    let* id_fixs pos_indb s := mk_tFix kname tFix_type tFix_rarg pos_indb s in
    (* 3. Closure Nuparams / Indices / Var *)
    let* id_nuparams s := closure_nuparams tLambda kname s in
    let* id_indices  s := closure_indices tLambda kname pos_indb s in
    let* id_VarMatch s := mk_tLambda (mkBindAnn (nNamed "x") Relevant)
                          (make_ind kname pos_indb id_uparams id_nuparams id_indices s)
                          (Some "VarMatch") s in
    (* 4. Proof of P ... x by match *)
    let tCase_pred := mk_case_pred id_preds id_nuparams pos_indb in
    let* pos_ctor ctor id_args _ s := mk_tCase kname pos_indb
            tCase_pred id_uparams id_nuparams (get_term id_VarMatch s) s in
    (* 5. Make the branch *)
    (mkApps (getij_term id_ctors pos_indb pos_ctor s)
            (get_terms id_nuparams s ++ compute_args_fix id_preds id_fixs id_args s)).


End GenRecTerm.