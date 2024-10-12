From RecAPI Require Import api_debruijn.
From RecAPI Require Import commons.
From RecAPI Require Import generate_rec_call.
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




  Definition compute_args_fix : context -> info -> (list ident * list ident * info) :=
    fun cxt e =>
    fold_left_info_opt2 (fun i cdecl e t =>
      match cdecl.(decl_body) with
      | Some db => let e := add_old_var "LET" cdecl e in (t [] [] e)
      | None => let id_arg := fresh_ident (Some "arg") e in
                let e := add_old_var id_arg cdecl e in
                let red_ty := reduce_except_lets E e (get_one_type id_arg e) in
                match make_rec_call kname Ep id_preds id_fixs id_arg red_ty e with
                | Some (ty, tm) =>
                    let id_rec := fresh_ident (Some "Rec Call") e in
                    let e := add_unscoped_var id_rec
                              (mkdecl (mkBindAnn nAnon U.(out_relev)) None ty) tm e in
                                  t [] [id_rec; id_arg] e
                | None => t [] [id_arg] e
                end
      end) cxt e (fun id_lets id_args e => (id_lets, id_args, e)).


    Definition make_type_arg : context_decl -> info ->
      (list ident -> list ident -> list ident -> info -> term) -> term :=
    fun '(mkdecl an db ty) e t =>
    match db with
    | Some db => kp_tLetIn an db ty e (fun x => t [x] [] [])
    | None => let* id_arg e <- kp_tProd an ty (Some "args") e in
              let red_ty := reduce_except_lets E e (get_one_type id_arg e) in
              match make_rec_call kname Ep id_preds [] id_arg red_ty e with
              | Some (ty, _) => mk_tProd (mkBindAnn nAnon Relevant) ty (Some "rec_call") e
                                  (fun id_rec => t [] [id_arg] [id_rec])
              | None => t [] [id_arg] [] e
              end
    end.

End GetRecCall.

  (* Info for Fix and Match *)
  Section FixMatchInfo.

    Context (id_uparams : list ident).
    Context (id_preds : list ident).

  (* 1. Info Fixpoint *)

  Section FixInfo.

    Context (pos_indb : nat).
    Context (indb : one_inductive_body).
    Context (e : info).

    #[using="pos_indb+indb+e"]
    Definition fix_aname : aname :=
      mkBindAnn (nNamed (make_name "F" pos_indb)) U.(out_relev).

    #[using="pos_indb+indb+e"]
    Definition fix_type : term :=
      make_return_type kname pos_indb id_uparams id_preds e.

    #[using="pos_indb+indb+e"]
    Definition fix_rarg : nat :=
      get_nb_nuparams kname e + length (get_indices kname pos_indb e).

  End FixInfo.



  (* 2. Info Match *)

  Section MatchInfo.

    Context (id_nuparams : list ident).
    Context (id_findices : list ident).
    Context (id_fVarMatch : ident).
    Context (pos_indb : nat).
    Context (indb : one_inductive_body).
    Context (e : info).

    #[using="pos_indb+indb+e"]
    Definition mk_case_info : case_info :=
      mk_case_info (mkInd kname pos_indb) (get_nb_params kname e) U.(out_relev).

    #[using="pos_indb+indb+e"]
    Definition mk_case_pred : term :=
      mkApp (make_predn id_preds pos_indb id_nuparams (get_term id_findices e) e)
            (get_one_term id_fVarMatch e).

    End MatchInfo.

  End FixMatchInfo.




  (* Generation Type of the Recursor *)
  Definition gen_rec_term (pos_indb : nat) : term :=
    (* 1. Closure Uparams / preds / ctors *)
    let e := add_mdecl kname nb_uparams mdecl init_info in
    let ' (id_inds, e) := replace_ind kname e in
    let* id_uparams e <- closure_uparams tLambda kname e in
    let* id_preds   e <- closure_preds tLambda kname U id_uparams e in
    let* id_ctors   e <- closure_ctors tLambda kname U E Ep id_uparams id_preds e in
    (* 2. Fixpoint *)
    let* id_fixs pos_indb indb e <- mk_tFix (get_ind_bodies kname e) fix_aname
                            (fix_type id_uparams id_preds) fix_rarg pos_indb e in
    (* 3. Closure Nuparams / Indices / Var *)
    let* id_nuparams e <- closure_nuparams tLambda kname e in
    let* id_indices  e <- closure_indices tLambda kname pos_indb e in
    let* id_VarMatch e <- mk_tLambda (mkBindAnn (nNamed "x") indb.(ind_relevance))
                            (make_ind kname pos_indb id_uparams id_nuparams id_indices e) (Some "VarMatch") e in
    (* 4. Proof of P ... x by match *)
    let* pos_ctor ctor e <- mk_tCase kname pos_indb indb mk_case_info (mk_case_pred id_preds id_nuparams)
                            id_uparams id_nuparams (get_one_type id_VarMatch e) e in
    (* 5. Make the branch *)
    let ' (_, id_args, e) := compute_args_fix id_preds id_fixs ctor.(cstr_args) e in
    mk_branch (rev (map decl_name ctor.(cstr_args)))
              (mkApps (get_one_of_term2 id_ctors pos_indb pos_ctor e)
                      (get_term id_nuparams e
                      (* ++ Print_info e *)
                      ++ get_term id_args e)).


End GenRecTerm.