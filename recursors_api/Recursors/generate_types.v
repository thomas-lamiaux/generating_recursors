From RecAPI Require Import api_debruijn.
From RecAPI Require Import commons.
From RecAPI Require Import recursor_rec_call.

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
  Definition make_type_pred : nat -> state -> term :=
    fun pos_indb s =>
    let* id_nuparams s <- closure_nuparams tProd kname s in
    let* id_indices  s <- closure_indices  tProd kname pos_indb s in
    tProd (mkBindAnn nAnon (get_relevance kname pos_indb s))
          (make_ind kname pos_indb id_uparams id_nuparams id_indices s)
          U.(out_univ).

  (* 1.2 Compute closure predicates *)
  Definition closure_preds : state -> (list ident -> state -> term) -> term :=
    fun s t =>
    closure_binder binder (Some "preds") (get_ind_bodies kname s)
      (fun pos_indb indb => mkBindAnn (nNamed (naming_pred pos_indb)) U.(out_relev))
      (fun pos_indb indb s => make_type_pred pos_indb s)
      s t.

  End MkPreds.



  (* 2. Make Type Constructor(s) *)

  Section MkCtor.

  Context (id_uparams : list ident).
  Context (id_preds   : list ident).

  (* 2.1 Generates the type associated to an argument *)
  (* forall x, [P x] storing the ident correctly *)
  Definition make_type_arg : context_decl -> state ->
      (list ident -> list ident -> list ident -> state -> term) -> term :=
    fun '(mkdecl an db ty) s t =>
    match db with
    | Some db => kp_tLetIn an db ty s (fun x => t [x] [] [])
    | None => let* id_arg s <- kp_tProd an ty (Some "args") s in
              let red_ty := reduce_except_lets E s (get_one_type id_arg s) in
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
  let* id_nuparams s <- closure_nuparams tProd kname s in
  let* _ id_args _ s <- fold_left_state_opt3 (fun _ => make_type_arg) ctor.(cstr_args) s in
  mkApp (make_predn id_preds pos_indb id_nuparams (get_ctor_indices kname pos_indb pos_ctor s) s)
        (mkApps (make_cst kname pos_indb pos_ctor id_uparams id_nuparams s)
                (get_term id_args s)).

  (* 2.3 Closure ctors of one inductive block *)            (* CHECK RELEVANCE *)
  Definition closure_ctors_block : nat -> one_inductive_body -> state -> (list ident -> state -> term) -> term :=
    fun pos_indb indb =>
    closure_binder binder (Some "ctors") indb.(ind_ctors)
    (fun pos_ctor ctor => mkBindAnn (nNamed (make_name_bin "f" pos_indb pos_ctor)) U.(out_relev))
    (fun pos_ctor ctor s => make_type_ctor pos_indb ctor pos_ctor s).

  (* 2.4 Closure all ctors *)
  Definition closure_ctors : state -> (list (list ident) -> state -> term) -> term :=
    fun s t => fold_right_state closure_ctors_block (get_ind_bodies kname s) s t.

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
  Definition make_return_type : state -> term :=
    fun s =>
    let* id_nuparams s <- closure_nuparams tProd kname s in
    let* id_indices  s <- closure_indices  tProd kname pos_indb s in
    let* id_VarMatch s <- mk_tProd (mkBindAnn (nNamed "x") (get_relevance kname pos_indb s))
                            (make_ind kname pos_indb id_uparams id_nuparams id_indices s) (Some "VarMatch") s in
    (mkApp (make_predni id_preds pos_indb id_nuparams id_indices s)
           (get_one_term id_VarMatch s)).

  End MkCcl.

End GenTypes.