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
Context (Ep : env_param).


(* 1. Get Args and Rec Call *)

Section GetRecCall.

  Context (id_preds : list ident).
  Context (id_fixs : list ident).




  Definition compute_args_fix : context -> state -> (list ident * list ident * state) :=
    fun cxt s =>
    fold_left_state_opt2 (fun i cdecl s t =>
      match cdecl.(decl_body) with
      | Some db => let s := add_old_var "LET" cdecl s in (t [] [] s)
      | None => let id_arg := fresh_ident (Some "arg") s in
                let s := add_old_var id_arg cdecl s in
                let red_ty := reduce_except_lets E s (get_one_type id_arg s) in
                match make_rec_call kname Ep id_preds id_fixs id_arg red_ty s with
                | Some (ty, tm) =>
                    let id_rec := fresh_ident (Some "Rec Call") s in
                    let s := add_unscoped_var id_rec
                              (mkdecl (mkBindAnn nAnon U.(out_relev)) None ty) tm s in
                                  t [] [id_rec; id_arg] s
                | None => t [] [id_arg] s
                end
      end) cxt s (fun id_lets id_args s => (id_lets, id_args, s)).

End GetRecCall.


  (* Info for Fix and Match *)
  Section FixMatchInfo.

    Context (id_uparams : list ident).
    Context (id_preds : list ident).

  (* 1. Info Fixpoint *)

  Section FixInfo.

    Context (pos_indb : nat).
    Context (indb : one_inductive_body).
    Context (s : state).

    #[using="pos_indb+indb+s"]
    Definition fix_aname : aname :=
      mkBindAnn (nNamed (make_name "F" pos_indb)) U.(out_relev).

    #[using="pos_indb+indb+s"]
    Definition fix_type : term :=
      make_return_type kname pos_indb id_uparams id_preds s.

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

    #[using="pos_indb+indb+s"]
    Definition mk_case_info : case_info :=
      mk_case_info (mkInd kname pos_indb) (get_nb_params kname s) U.(out_relev).

    #[using="pos_indb+indb+s"]
    Definition mk_case_pred : term :=
      mkApp (make_predn id_preds pos_indb id_nuparams (get_term id_findices s) s)
            (get_one_term id_fVarMatch s).

    End MatchInfo.

  End FixMatchInfo.



  (* 3. Generation Type of the Recursor *)
  Definition gen_rec_term (pos_indb : nat) : term :=
    (* 1. Closure Uparams / preds / ctors *)
    let s := add_mdecl kname nb_uparams mdecl init_state in
    let ' (id_inds, s) := replace_ind kname s in
    let* id_uparams s <- closure_uparams tLambda kname s in
    let* id_preds   s <- closure_preds tLambda kname U id_uparams s in
    let* id_ctors   s <- closure_ctors tLambda kname U E Ep id_uparams id_preds s in
    (* 2. Fixpoint *)
    let* id_fixs pos_indb indb s <- mk_tFix (get_ind_bodies kname s) fix_aname
                            (fix_type id_uparams id_preds) fix_rarg pos_indb s in
    (* 3. Closure Nuparams / Indices / Var *)
    let* id_nuparams s <- closure_nuparams tLambda kname s in
    let* id_indices  s <- closure_indices tLambda kname pos_indb s in
    let* id_VarMatch s <- mk_tLambda (mkBindAnn (nNamed "x") indb.(ind_relevance))
                            (make_ind kname pos_indb id_uparams id_nuparams id_indices s) (Some "VarMatch") s in
    (* 4. Proof of P ... x by match *)
    let* pos_ctor ctor s <- mk_tCase kname pos_indb indb mk_case_info (mk_case_pred id_preds id_nuparams)
                            id_uparams id_nuparams (get_one_term id_VarMatch s) s in
    (* 5. Make the branch *)
    let ' (_, id_args, s) := compute_args_fix id_preds id_fixs ctor.(cstr_args) s in
    mk_branch (rev (map decl_name ctor.(cstr_args)))
              (mkApps (get_one_of_term2 id_ctors pos_indb pos_ctor s)
                      (get_term id_nuparams s
                      (* ++ Print_state s *)
                      ++ get_term id_args s)).


End GenRecTerm.