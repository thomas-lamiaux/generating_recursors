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


    (* Info for Fix and Match *)
    Section FixMatchInfo.

    Context (id_uparams : list ident).
    Context (id_preds : list ident).
    Context (id_uparams_preds : list ident).


  (* 1. Info Fixpoint *)

  Section FixInfo.

    Context (pos_indb : nat).
    Context (indb : one_inductive_body).
    Context (s : state).

    #[using="pos_indb+indb+s"]
    Definition fix_type : term :=
      make_return_type kname knamep id_uparams id_uparams_preds pos_indb s.

  End FixInfo.


  (* 2. Info Match *)

  Section MatchInfo.

    Context (id_nuparams : list ident).
    Context (id_findices : list ident).
    Context (id_fVarMatch : ident).
    Context (pos_indb : nat).
    Context (indb : one_inductive_body).
    Context (s : state).

    #[using="pos_indb+indb+s"]
    Definition mk_case_pred : term :=
      mkApp (make_ind knamep pos_indb id_uparams_preds id_nuparams id_findices s)
            (get_term id_fVarMatch s).

    End MatchInfo.

  End FixMatchInfo.


(* 3. Compute the custom parametricty  *)
Definition fundamental_theorem_term (pos_indb : nat) : term :=
  (* add inds and its param to state *)
  let s := add_mdecl kname nb_uparams mdecl init_state in
  let annoted_uparams := combine (rev (get_uparams kname s)) strpos_uparams in
  let* s := replace_ind kname s in
  (* 1. add uparams + extra predicate *)
  let* id_uparams id_preds id_uparams_preds id_preds_hold s :=
        closure_uparams_preds_hold tLambda annoted_uparams s in
  (* 2. fixpoint *)
  let* id_fixs pos_indb indb s := mk_tFix kname (fix_type id_uparams id_uparams_preds)
                                  (tFix_default_rarg kname) pos_indb s in
  (* 3. closure nuparams + indices + var match *)
  let* id_nuparams s := closure_nuparams tLambda kname s in
  let* id_indices  s := closure_indices  tLambda kname pos_indb s in
  let* id_VarMatch s := mk_tLambda (mkBindAnn (nNamed "x") (get_relevance kname pos_indb s))
                        (make_ind kname pos_indb id_uparams id_nuparams id_indices s)
                        (Some "VarMatch") s in
  (* 4. match VarMatch *)
  let* pos_ctor ctor _ id_args _ s := mk_tCase kname pos_indb indb (mk_case_pred id_uparams_preds id_nuparams)
                          id_uparams id_nuparams (get_term id_VarMatch s) s in
  (* 5. Conclude *)
  (mkApps (make_cst knamep pos_indb pos_ctor id_uparams_preds id_nuparams s)
          (compute_args_fix id_uparams id_preds id_uparams_preds id_preds_hold
            id_fixs id_args s)).


End CustomParam.