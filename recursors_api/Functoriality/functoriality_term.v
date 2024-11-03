From RecAPI Require Import api_debruijn.
From RecAPI Require Import functoriality_type.


Section FuncTerm.

  Context (kname : kername).
  Context (mdecl : mutual_inductive_body).
  Context (nb_uparams : nat).
  Context (strpos_uparams : list bool).
  Context (E : global_env).
  Context (Ep : param_env).


 (* 1. Get Args and Rec Call *)

(* Section GetRecCall.

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

End GetRecCall. *)


(* Info for Fix and Match *)
Section FixMatchInfo.

  Context (id_uparams     : list ident).
  Context (id_uparams_bis : list ident).

(* 1. Info Fixpoint *)

Section FixInfo.

  Context (pos_indb : nat).
  Context (indb : one_inductive_body).
  Context (s : state).

  #[using="pos_indb+indb+s"]
  Definition fix_aname : aname :=
    mkBindAnn (nNamed ("F" ^ string_of_nat pos_indb)) Relevant.

  #[using="pos_indb+indb+s"]
  Definition fix_type : term :=
    make_return_type kname id_uparams id_uparams_bis pos_indb s.

  #[using="pos_indb+indb+s"]
  Definition fix_rarg : nat :=
    get_nb_nuparams kname s + length (get_indices kname pos_indb s).

End FixInfo.


(* 2. Info Match *)

Section MatchInfo.

  Context (id_nuparams : list ident).
  Context (id_findices : list ident).
  Context (id_fVarMatch : ident).
  Context (pos_indb : nat).
  Context (indb : one_inductive_body).
  Context (s : state).

  #[using="pos_indb+indb+s+id_fVarMatch"]
  Definition mk_case_pred : term :=
    make_ind kname pos_indb id_uparams_bis id_nuparams id_findices s.

  End MatchInfo.

End FixMatchInfo.

(* 3. Compute the custom parametricty  *)
Definition fundamental_theorem_term (pos_indb : nat) : term :=
  (* add inds and its param to state *)
  let s := add_mdecl kname nb_uparams mdecl init_state in
  let annoted_uparams := combine (rev (get_uparams kname s)) strpos_uparams in
  let* s := replace_ind kname s in
  (* 1. add uparams + uparam_bis + functions A -> A_bis *)
  let* id_uparams id_uparams_bis s := closure_uparams_func tLambda annoted_uparams s in
  (* 2. fixpoint *)
  let* id_fixs pos_indb indb s := mk_tFix (get_ind_bodies kname s) fix_aname
      (fix_type id_uparams id_uparams_bis) fix_rarg pos_indb s in
  (* 3. closure nuparams + indices + var match *)
  let* id_nuparams s := closure_nuparams tLambda kname s in
  let* id_indices  s := closure_indices  tLambda kname pos_indb s in
  let* id_VarMatch s := mk_tLambda (mkBindAnn (nNamed "x") (get_relevance kname pos_indb s))
                        (make_ind kname pos_indb id_uparams id_nuparams id_indices s)
                        (Some "VarMatch") s in
  (* 4. match VarMatch *)
  let* pos_ctor ctor _ id_args _ s := mk_tCase kname pos_indb indb (mk_case_pred id_uparams_bis id_nuparams)
                          id_uparams id_nuparams (get_term id_VarMatch s) s in
  tRel 0.
  (* 5. Conclude *)
  (mkApps (make_cst knamep pos_indb pos_ctor id_uparams_preds id_nuparams s)
          (compute_args_fix id_uparams id_preds id_uparams_preds id_preds_hold
            id_fixs id_args s)).


End GenRecTerm.