From RecAPI Require Import api_debruijn.
From RecAPI Require Import commons.
From RecAPI Require Import generate_rec_call.
From RecAPI Require Import generate_types.


Section GenRecTerm.

Context (mdecl : mutual_inductive_body).
Context (pdecl : preprocess_mutual_inductive_body).
Context (U : output_univ).
Context (E : global_env).
Context (Ep : env_param).

  Definition kname := pdecl.(pmb_kname).
  Definition uparams  := pdecl.(pmb_uparams).
  Definition nb_uparams  := pdecl.(pmb_nb_uparams).
  Definition nuparams := pdecl.(pmb_nuparams).
  Definition nb_nuparams  := pdecl.(pmb_nb_nuparams).


Definition compute_args_fix : context -> info -> info  :=
  fun cxt e =>
  fold_left_ie (fun i cdecl e (t : info -> info) =>
    match cdecl.(decl_body) with
    | Some db => let e := add_old_var None cdecl e in t e
    | None => let e := add_old_var (Some "args") cdecl e in
              match make_rec_pred pdecl Ep (reduce_except_lets E e (geti_type_rev "args" 0 e)) e with
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

  (* 1. Info Fixpoint *)
  #[using="All"]
  Definition fix_aname : aname :=
    mkBindAnn (nNamed (make_name "F" pos_indb)) U.(out_relev).

  Definition fix_type : info -> term :=
   fun e => make_return_type pdecl pos_indb indb e.

  #[using="All"]
  Definition fix_rarg : nat :=
    nb_nuparams + length (indb.(ind_indices)).

  (* 2. Info Match *)
  #[using="All"]
  Definition mk_case_info : case_info :=
    mk_case_info (mkInd kname pos_indb)(nb_uparams + nb_nuparams) U.(out_relev).

  Definition get_aname : ident -> info -> list aname :=
    fun s e => map (fun x =>x.(info_def).(decl_name)) (filter (filter_name s) e).

  #[using="All"]
  Definition mk_case_pred : info -> predicate term :=
    fun e =>
    let local_aname := (mkBindAnn (nNamed "y") indb.(ind_relevance) :: get_aname "indices" e) in
    let local_tVar := rev (mapi (fun i _ => tRel i) local_aname) in
    mk_predicate [] (get_term "uparams" e ++ get_term "nuparams" e) local_aname
      (mkApps (lift0 (length local_aname)
                     (mkApps (geti_term "preds" pos_indb e)
                             (get_term "nuparams" e)))
              local_tVar).

  End FixMatch.




  (* Generation Type of the Recursor *)
  Definition gen_rec_term (indb : one_inductive_body) : term :=
    (* 1. Closure Uparams / preds / ctors *)
    let e := replace_ind pdecl.(pmb_kname) mdecl init_info in
    e <- closure_uparams tLambda pdecl.(pmb_uparams) e ;;
    e <- closure_preds pdecl U tLambda e ;;
    e <- closure_ctors pdecl U E Ep tLambda e ;;
    (* 2. Fixpoint *)
    let* pos_indb indb e <- mk_tFix pdecl.(pmb_ind_bodies) fix_aname (fun a b => fix_type a b e)
                                  fix_rarg pdecl.(pmb_pos_indb) (Some "fix") e ;;
    (* 3. Closure Nuparams / Indices / Var *)
    e <- closure_nuparams tLambda nuparams e ;;
    e <- closure_indices tLambda (weaken_context e indb.(ind_indices)) e ;;
    e <- mk_tLambda (mkBindAnn (nNamed "x") indb.(ind_relevance))
                    (make_ind kname pos_indb e) (Some "VarMatch") e ;;
    (* 4. Proof of P ... x by match *)
    let* pos_ctor ctor e <- mk_tCase pos_indb indb mk_case_info (fun x y => mk_case_pred x y e)
                            (geti_term_rev "VarMatch" 0 e) e ;;
    (* 5. Make the branch *)
    let e := compute_args_fix ctor.(cstr_args) e in
    mk_branch (rev (map decl_name ctor.(cstr_args)))
              (mkApps (geti_term (make_name "f" pos_indb) pos_ctor e)
                      (get_term "nuparams" e
                      (* ++ Print_info e *)
                      ++ get_term "args" e)).


End GenRecTerm.