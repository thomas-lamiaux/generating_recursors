From RecAPI Require Import api_debruijn.
From RecAPI Require Import commons.
From RecAPI Require Import generate_rec_call.

(*
  Genrates :
  1. Make Type Predicate(s)
  2. Make Type Constructor(s)
  3. Make Return Type
*)

Section GenTypes.

  Context (binder : aname -> term -> term -> term).
  Context (kname : kername).
  Context (U : output_univ).
  Context (E : global_env).
  Context (Ep : env_param).

(* 1. Make Type Predicate(s) *)

  Section MkPreds.

  Context (id_uparams : list ident).

  (* 1.1 Builds the type of the predicate for the i-th block
    forall (B0 : R0) ... (Bm : Rm),
    forall (i1 : t1) ... (il : tl),
      (Ind A1 ... An B0 ... Bm i1 ... il) -> U)  *)
  Definition make_type_pred : nat -> info -> term :=
    fun pos_indb e =>
    let* id_nuparams e <- closure_nuparams tProd kname e in
    let* id_indices  e <- closure_indices  tProd kname pos_indb e in
    tProd (mkBindAnn nAnon (get_relevance kname pos_indb e))
          (make_ind kname pos_indb id_uparams id_nuparams id_indices e)
          U.(out_univ).

  (* 1.2 Compute closure predicates *)
  Definition closure_preds : info -> (list ident -> info -> term) -> term :=
    fun e t =>
    closure_binder binder (Some "preds") (get_ind_bodies kname e)
      (fun pos_indb indb => mkBindAnn (nNamed (naming_pred pos_indb)) U.(out_relev))
      (fun pos_indb indb e => make_type_pred pos_indb e)
      e t.

  End MkPreds.



  (* 2. Make Type Constructor(s) *)

  Section MkCtor.

  Context (id_uparams : list ident).
  Context (id_preds   : list ident).

  (* 2.1 Generates the type associated to an argument *)
  (* forall x, [P x] *)
  Definition make_type_arg : context_decl -> info -> (ident -> info -> term) -> term :=
    fun cdecl e t =>
    let '(mkdecl an db ty) := cdecl in
    match db with
    | Some db => kp_tLetIn an db ty e t
    | None => let* id_arg e <- kp_tProd an ty (Some "args") e in
              let red_ty := reduce_except_lets E e (get_one_type id_arg e) in
              match make_rec_call kname Ep id_preds [] id_arg red_ty e with
              | Some (ty, _) => mk_tProd (mkBindAnn nAnon Relevant) ty (Some "rec_call") e t     (* ISSUES MIXED !*)
              | None => t id_arg e
              end
    end.

  (* 2.2 Generates the type associated to a constructor *)
  (* forall (B0 : R0) ... (Bm : Rm),
     forall x0 : t0, [P x0], ..., xn : tn, [P n],
     P B0 ... Bm f0 ... fl (cst A0 ... An B0 ... Bm x0 ... xl) *)
  Definition make_type_ctor : nat -> constructor_body -> nat -> info -> term :=
    fun pos_indb ctor pos_ctor e =>
    let* id_nuparams e <- closure_nuparams tProd kname e in
    let* id_args    e <- fold_left_info (fun _ => make_type_arg) ctor.(cstr_args) e in
    mkApp (make_predn id_preds pos_indb id_nuparams (get_ctor_indices kname pos_indb pos_ctor e) e)
          (mkApps (make_cst kname pos_indb pos_ctor id_uparams id_nuparams e)
                  (get_term id_args e)).


  (* 2.3 Closure ctors of a block *)            (* CHECK RELEVANCE *)
  Definition closure_ctors_block : nat -> one_inductive_body -> info -> (list ident -> info -> term) -> term :=
    fun pos_indb indb =>
    closure_binder binder (Some "ctors") indb.(ind_ctors)
    (fun pos_ctor ctor => mkBindAnn (nNamed (make_name_bin "f" pos_indb pos_ctor)) U.(out_relev))
    (fun pos_ctor ctor e => make_type_ctor pos_indb ctor pos_ctor e).

  (* 2.4 Closure all ctors *)
  Definition closure_ctors : info -> (list (list ident) -> info -> term) -> term :=
    fun e t => fold_right_info closure_ctors_block (get_ind_bodies kname e) e t.

  End MkCtor.

  (* 3. Make Return Type *)

  Section MkCcl.

  Context (pos_indb : nat).
  Context (id_uparams : list ident).
  Context (id_preds   : list ident).

  (* forall (B0 : R0) ... (Bm : Rm),
     forall (i1 : t1) ... (il : tl),
     forall (x : Ind A0 ... An B0 ... Bm i0 ... il),
      P B0 ... Bm i0 ... il x *)
  Definition make_return_type : info -> term :=
    fun e =>
    let* id_nuparams e <- closure_nuparams tProd kname e in
    let* id_indices  e <- closure_indices  tProd kname pos_indb e in
    let* id_VarMatch e <- mk_tProd (mkBindAnn (nNamed "x") (get_relevance kname pos_indb e))
                            (make_ind kname pos_indb id_uparams id_nuparams id_indices e) (Some "VarMatch") e in
    (mkApp (make_predni id_preds pos_indb id_nuparams id_indices e)
           (get_one_term id_VarMatch e)).

  End MkCcl.

End GenTypes.