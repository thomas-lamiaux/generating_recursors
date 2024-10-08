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

  Context (kname : kername).
  Context (U : output_univ).
  Context (E : global_env).
  Context (Ep : env_param).

(* 1. Make Type Predicate(s) *)

  (* 1.1 Builds the type of the predicate for the i-th block
    forall (B0 : R0) ... (Bm : Rm),
    forall (i1 : t1) ... (il : tl),
      (Ind A1 ... An B0 ... Bm i1 ... il) -> U)  *)
  Definition make_type_pred : nat -> info -> term :=
    fun pos_indb e =>
    let* e <- closure_nuparams tProd kname e in
    let* e <- closure_indices  tProd kname pos_indb e in
    tProd (mkBindAnn nAnon (get_relevance kname pos_indb e))
          (make_ind kname pos_indb e) U.(out_univ).

  (* 1.2 Compute closure predicates *)
  Definition closure_preds binder : info -> (info -> term) -> term :=
    fun e t => let pdecl := get_pdecl kname e in
    closure_binder binder "preds" (get_ind_bodies kname e)
      (fun pos_indb indb => mkBindAnn (nNamed (naming_pred pos_indb)) U.(out_relev))
      (fun pos_indb indb e => make_type_pred pos_indb e)
      e t.



  (* 2. Make Type Constructor(s) *)

  (* 2.1 Generates the type associated to an argument *)
  (* forall x, [P x] *)
  Definition make_type_arg : context_decl -> option ident -> info -> (info -> term) -> term :=
    fun cdecl x e t =>
    let '(mkdecl an db ty) := cdecl in
    match db with
    | Some db => kp_tLetIn an db ty None e t
    | None => let* e <- kp_tProd an ty x e in
              match make_rec_pred kname Ep (reduce_except_lets E e (geti_type_rev "args" 0 e)) e with
              | Some (ty, _) => mk_tProd (mkBindAnn nAnon Relevant) ty None e t
              | None => t e
              end
    end.

  (* 2.2 Generates the type associated to a constructor *)
  (* forall (B0 : R0) ... (Bm : Rm),
     forall x0 : t0, [P x0], ..., xn : tn, [P n],
     P B0 ... Bm f0 ... fl (cst A0 ... An B0 ... Bm x0 ... xl) *)
  Definition make_type_ctor : nat -> constructor_body -> nat -> info -> term :=
    fun pos_indb ctor pos_ctor e =>
    let* e <- closure_nuparams tProd kname e in
    let* e <- fold_left_ie (fun _ cdecl => make_type_arg cdecl (Some "args")) ctor.(cstr_args) e in
    mkApp (make_predn pos_indb (get_ctor_indices kname pos_indb pos_ctor e) e)
          (mkApps (make_cst kname pos_indb pos_ctor e)
                  (get_term "args" e)).


  (* 2.3 Closure ctors of a block *)            (* CHECK RELEVANCE *)
  Definition closure_ctors_block binder : nat -> one_inductive_body -> info -> (info -> term) -> term :=
    fun pos_indb indb =>
    closure_binder binder (make_name "f" pos_indb) indb.(ind_ctors)
    (fun pos_ctor ctor => mkBindAnn (nNamed (make_name_bin "f" pos_indb pos_ctor)) U.(out_relev))
    (fun pos_ctor ctor e => make_type_ctor pos_indb ctor pos_ctor e).

  (* 2.4 Closure all ctors *)
  Definition closure_ctors binder : info -> (info -> term) -> term :=
    fun e t => fold_right_ie (closure_ctors_block binder) (get_ind_bodies kname e) e t.



  (* 3. Make Return Type *)
  (* forall (B0 : R0) ... (Bm : Rm),
     forall (i1 : t1) ... (il : tl),
     forall (x : Ind A0 ... An B0 ... Bm i0 ... il),
      P B0 ... Bm i0 ... il x *)
  Definition make_return_type : nat -> info -> term :=
    fun pos_indb e =>
    let* e <- closure_nuparams tProd kname e in
    let* e <- closure_indices  tProd kname pos_indb e in
    let* e <- mk_tProd (mkBindAnn (nNamed "x") (get_relevance kname pos_indb e))
                  (make_ind kname pos_indb e)
                  (Some "VarCCL") e in
    (mkApps (make_predni pos_indb e) (get_term "VarCCL" e)).


End GenTypes.