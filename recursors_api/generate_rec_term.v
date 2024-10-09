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


Definition compute_args_fix : context -> info -> info  :=
  fun cxt e =>
  fold_left_ie (fun i cdecl e (t : info -> info) =>
    match cdecl.(decl_body) with
    | Some db => let e := add_old_var None cdecl e in t e
    | None => let e := add_old_var (Some "args") cdecl e in
              match make_rec_pred kname Ep (reduce_except_lets E e (geti_type_rev "args" 0 e)) e with
              | Some (ty, tm) =>
                  let e := add_unscoped_var (Some "args")
                                      (mkdecl (mkBindAnn nAnon U.(out_relev)) None ty) tm e in
                                t e
              | None => t e
              end
    end) cxt e (fun e => e).


  (* Section *)
  Section FixMatch.
    Context (pos_indb : nat).
    Context (indb : one_inductive_body).
    Context (e : info).

  (* 1. Info Fixpoint *)
  #[using="All"]
  Definition fix_aname : aname :=
    mkBindAnn (nNamed (make_name "F" pos_indb)) U.(out_relev).

  #[using="All"]
  Definition fix_type : term :=
    make_return_type kname pos_indb e.

  #[using="All"]
  Definition fix_rarg : nat :=
    (get_pdecl kname e).(info_nb_nuparams) + length (get_indices kname pos_indb e).

  (* 2. Info Match *)
  #[using="All"]
  Definition mk_case_info : case_info :=
    mk_case_info (mkInd kname pos_indb) (get_nb_params kname e) U.(out_relev).

  #[using="All"]
  Definition mk_case_pred : term :=
    mkApps (make_predn pos_indb (get_term "fresh_indices" e) e)
           (get_term "fresh_VarMatch" e).

  End FixMatch.




  (* Generation Type of the Recursor *)
  Definition gen_rec_term (pos_indb : nat) : term :=
    (* 1. Closure Uparams / preds / ctors *)
    let e := add_mdecl kname nb_uparams mdecl init_info in
    let e := replace_ind kname mdecl e in
    let* e <- closure_uparams tLambda kname e in
    let* e <- closure_preds kname U tLambda e in
    let* e <- closure_ctors kname U E Ep tLambda e in
    (* 2. Fixpoint *)
    let* pos_indb indb e <- mk_tFix (get_ind_bodies kname e) fix_aname fix_type fix_rarg pos_indb (Some "fix") e in
    (* 3. Closure Nuparams / Indices / Var *)
    let* e <- closure_nuparams tLambda kname e in
    let* e <- closure_indices tLambda kname pos_indb e in
    let* e <- mk_tLambda (mkBindAnn (nNamed "x") indb.(ind_relevance))
                    (make_ind kname pos_indb e) (Some "VarMatch") e in
    (* 4. Proof of P ... x by match *)
    let* pos_ctor ctor e <- mk_tCase pos_indb indb mk_case_info mk_case_pred kname
                            (geti_term_rev "VarMatch" 0 e) e in
    (* 5. Make the branch *)
    let e := compute_args_fix ctor.(cstr_args) e in
    mk_branch (rev (map decl_name ctor.(cstr_args)))
              (mkApps (geti_term (make_name "f" pos_indb) pos_ctor e)
                      (get_term "nuparams" e
                      (* ++ Print_info e *)
                      ++ get_term "args" e)).


End GenRecTerm.