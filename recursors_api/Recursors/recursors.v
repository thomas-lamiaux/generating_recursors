From RecAPI Require Import api_debruijn.
From RecAPI Require Import commons.
From RecAPI Require Import recursor_rec_call.

(*
  Structure:

  1. Make Different Types
    1.1 Make the type of the predicates
    1.2 Make the type of the constructors
    1.3 Make the return type
  2. Make the type of the recursors
  3. Make the the recursors

*)


Section GenRecursors.

Context (kname : kername).
Context (mdecl : mutual_inductive_body).
Context (nb_uparams : nat).
Context (U : output_univ).
Context (E : global_env).
Context (Ep : param_env).


(* ################################# *)
(*    1. Make the different types    *)
(* ################################# *)

Section GenTypes.

  Context (binder : aname -> term -> term -> term).

  (* 1.1 Make Type Predicate(s) *)

  Section MkPreds.

  Context (id_uparams : list ident).

  (* 1.1.1 Builds the type of the predicate for the i-th block
    forall (B0 : R0) ... (Bm : Rm),
    forall (i1 : t1) ... (il : tl),
      (Ind A1 ... An B0 ... Bm i1 ... il) -> U)  *)
  Definition make_type_pred : nat -> state -> term :=
    fun pos_indb s =>
    let* id_nuparams s := closure_nuparams tProd kname s in
    let* id_indices  s := closure_indices  tProd kname pos_indb s in
    tProd (mkBindAnn nAnon (get_relevance kname pos_indb s))
          (make_ind kname pos_indb id_uparams id_nuparams id_indices s)
          U.(out_univ).

  (* 1.2.1 Compute closure predicates *)
  Definition closure_preds : state -> (list ident -> state -> term) -> term :=
    fun s t =>
    closure_binder binder (Some "preds") (get_ind_bodies kname s)
      (fun pos_indb indb => mkBindAnn (nNamed (naming_pred pos_indb)) U.(out_relev))
      (fun pos_indb indb s => make_type_pred pos_indb s)
      s t.

  End MkPreds.



  (* 1.2. Make Type Constructor(s) *)

  Section MkCtor.

  Context (id_uparams : list ident).
  Context (id_preds   : list ident).

  (* 1.2.1 Generates the type associated to an argument *)
  (* forall x, [P x] storing the ident correctly *)
  Definition make_type_arg : context_decl -> state ->
      (list ident -> list ident -> list ident -> state -> term) -> term :=
    fun '(mkdecl an db ty) s t =>
    match db with
    | Some db => kp_tLetIn an db ty s (fun x => t [x] [] [])
    | None => let* id_arg s := kp_tProd an ty (Some "args") s in
              let red_ty := reduce_except_lets E s (get_type id_arg s) in
              match make_rec_call kname Ep id_preds [] id_arg red_ty s with
              | Some (ty, _) => mk_tProd (mkBindAnn nAnon Relevant) ty (Some "rec_call") s
                                  (fun id_rec => t [] [id_arg] [id_rec])
              | None => t [] [id_arg] [] s
              end
    end.

  (* 2.2 Generates the type associated to a constructor *)
  (* forall (B0 : R0) ... (Bm : Rm),
     forall x0 : t0, [P x0], ..., xn : tn, [P n],
     P B0 ... Bm f0 ... fl (cst A0 ... An B0 ... Bm x0 ... xl) *)
  Definition make_type_ctor : nat -> constructor_body -> nat -> state -> term :=
  fun pos_indb ctor pos_ctor s =>
  let* id_nuparams s := closure_nuparams tProd kname s in
  let* _ id_args _ s := fold_left_state_opt3 (fun _ => make_type_arg) ctor.(cstr_args) s in
  mkApp (make_predn id_preds pos_indb id_nuparams (get_ctor_indices kname pos_indb pos_ctor s) s)
        (mkApps (make_cst kname pos_indb pos_ctor id_uparams id_nuparams s)
                (get_terms id_args s)).

  (* 2.3 Closure ctors of one inductive block *)
  Definition closure_ctors_block : nat -> one_inductive_body -> state -> (list ident -> state -> term) -> term :=
    fun pos_indb indb =>
    closure_binder binder (Some "ctors") indb.(ind_ctors)
    (fun pos_ctor ctor => mkBindAnn (nNamed (make_name_bin "f" pos_indb pos_ctor)) U.(out_relev))
    (fun pos_ctor ctor s => make_type_ctor pos_indb ctor pos_ctor s).

  (* 2.4 Closure all ctors *)
  Definition closure_ctors : state -> (list (list ident) -> state -> term) -> term :=
    fun s t => fold_right_state closure_ctors_block (get_ind_bodies kname s) s t.

  End MkCtor.


  (* 1.3 Make Return Type *)

  Section MkCcl.

  Context (id_uparams : list ident).
  Context (id_preds   : list ident).
  Context (pos_indb : nat).

  (* 1.3.1 Make the type of the conclusion *)
  (* P B0 ... Bm i0 ... il x *)
  Definition make_ccl : list ident -> list ident -> ident -> state -> term :=
    fun id_nuparams id_indices id_VarMatch s =>
    mkApp (make_predn id_preds pos_indb id_nuparams (get_terms id_indices s) s)
          (get_term id_VarMatch s).

  (* 1.3.2 Make the return type *)
  (* forall (B0 : R0) ... (Bm : Rm),
     forall (i1 : t1) ... (il : tl),
     forall (x : Ind A0 ... An B0 ... Bm i0 ... il),
      P B0 ... Bm i0 ... il x *)
  Definition make_return_type : state -> term :=
    fun s =>
    let* id_nuparams s := closure_nuparams tProd kname s in
    let* id_indices  s := closure_indices  tProd kname pos_indb s in
    let* id_VarMatch s := mk_tProd (mkBindAnn (nNamed "x") (get_relevance kname pos_indb s))
                            (make_ind kname pos_indb id_uparams id_nuparams id_indices s) (Some "VarMatch") s in
    make_ccl id_nuparams id_indices id_VarMatch s.

  End MkCcl.

  End GenTypes.



(* ####################################### *)
(*    2. Make the type of the recursors    *)
(* ####################################### *)

Definition gen_rec_type (pos_indb : nat) : term :=
  let s := add_mdecl kname nb_uparams mdecl init_state in
  let* s := replace_ind kname s in
  let* id_uparams s := closure_uparams tProd kname s in
  let* id_preds   s := closure_preds   tProd id_uparams s in
  let* id_ctors   s := closure_ctors   tProd id_uparams id_preds s in
  make_return_type id_uparams id_preds pos_indb s.



(* ####################################### *)
(*    3. Make the type of the recursors    *)
(* ####################################### *)

(* 3.1 Compute the arguments of the rec call *)
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


(* 3.2 Generates the recursor *)
Definition gen_rec_term (pos_indb : nat) : term :=
  (* 0. Initialise state with inductives *)
  let s := add_mdecl kname nb_uparams mdecl init_state in
  let* s := replace_ind kname s in
  (* 1. Closure Uparams / preds / ctors *)
  let* id_uparams s := closure_uparams tLambda kname s in
  let* id_preds   s := closure_preds tLambda id_uparams s in
  let* id_ctors   s := closure_ctors tLambda id_uparams id_preds s in
  (* 2. Fixpoint *)
  let tFix_type pos_indb := make_return_type id_uparams id_preds pos_indb s in
  let tFix_rarg := tFix_default_rarg kname s in
  let* id_fixs pos_indb s := mk_tFix kname tFix_type tFix_rarg pos_indb s in
  (* 3. Closure Nuparams / Indices / Var *)
  let* id_nuparams s := closure_nuparams tLambda kname s in
  let* id_indices  s := closure_indices tLambda kname pos_indb s in
  let* id_VarMatch s := mk_tLambda (mkBindAnn (nNamed "x") Relevant)
                        (make_ind kname pos_indb id_uparams id_nuparams id_indices s)
                        (Some "VarMatch") s in
  (* 4. Proof of P ... x by match *)
  let tCase_pred := make_ccl id_preds pos_indb id_nuparams in
  let* pos_ctor ctor id_args _ s := mk_tCase kname pos_indb
          tCase_pred id_uparams id_nuparams (get_term id_VarMatch s) s in
  (* 5. Make the branch *)
  (mkApps (getij_term id_ctors pos_indb pos_ctor s)
          (get_terms id_nuparams s ++ compute_args_fix id_preds id_fixs id_args s)).


End GenRecursors.