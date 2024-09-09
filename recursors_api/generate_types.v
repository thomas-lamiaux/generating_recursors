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

  Context (pdecl : preprocess_mutual_inductive_body).
  Context (U : output_univ).
  Context (E : env_param).

  Definition kname := pdecl.(pmb_kname).
  Definition uparams  := pdecl.(pmb_uparams).
  Definition nuparams := pdecl.(pmb_nuparams).
  Definition nb_block := #|pdecl.(pmb_ind_bodies)|.

(* 1. Make Type Predicate(s) *)

  (* 1.1 Builds the type of the predicate for the i-th block
    forall (B0 : R0) ... (Bm : Rm),
    forall (i1 : t1) ... (il : tl),
      (Ind A1 ... An B0 ... Bm i1 ... il) -> U)  *)
  Definition make_type_pred : nat -> relevance -> context -> info -> term :=
    fun pos_block relev_ind_sort indices e =>
    e <- closure_nuparams tProd nuparams e ;;
    e <- closure_indices  tProd indices  e ;;
    tProd (mkBindAnn nAnon relev_ind_sort) (make_ind kname pos_block e) U.(out_univ).

  (* 1.2 Compute closure predicates *)
  Definition closure_preds binder : info -> (info -> term) -> term :=
    iterate_binder binder "preds" pdecl.(pmb_ind_bodies)
      (fun pos_block indb => mkBindAnn (nNamed (naming_pred pos_block)) U.(out_relev))
      (fun pos_block indb e => make_type_pred pos_block indb.(ind_relevance) indb.(ind_indices) e).



  (* 2. Make Type Constructor(s) *)

  (* 2.1 Generates the type associated to an argument *)
  (* forall x, [P x] *)
  Definition make_type_arg : context_decl -> option ident -> info -> (info -> term) -> term :=
    fun cdecl x e t =>
    let '(mkdecl an db ty) := cdecl in
    match db with
    | None => let wk_ty := e ↑ ty in
              e <- kp_tProd an ty x e ;;
              (match make_rec_pred pdecl (lift0 1 wk_ty)  e with
              | Some (ty, _) => mk_tProd (mkBindAnn nAnon Relevant)
                                         (mkApp ty (tRel 0))
                                         None e t
              | None => t e
              end)
    | Some db => kp_tLetIn an db ty None e t
    end.

  (* 2.2 Generates the type associated to a constructor *)
  (* forall (B0 : R0) ... (Bm : Rm),
     forall x0 : t0, [P x0], ..., xn : tn, [P n],
     P B0 ... Bm f0 ... fl (cst A0 ... An B0 ... Bm x0 ... xl) *)
  Definition make_type_ctor : nat -> constructor_body -> nat -> info -> term :=
    fun pos_block ctor pos_ctor e =>
    e <- closure_nuparams tProd nuparams e ;;
    e <- fold_left_ie (fun _ cdecl => make_type_arg cdecl (Some "args")) ctor.(cstr_args) e ;;
    mkApp (make_predn pos_block (map (weaken e) ctor.(cstr_indices)) e)
      (mkApps (make_cst kname pos_block pos_ctor e)
              (get "args" e)).


  (* 2.3 Closure ctors of a block *)            (* CHECK RELEVANCE *)
  Definition closure_ctors_block binder : nat -> one_inductive_body -> info -> (info -> term) -> term :=
    fun pos_block indb =>
    iterate_binder binder "f" indb.(ind_ctors)
    (fun pos_ctor ctor => mkBindAnn (nNamed (make_name_bin "f" pos_block pos_ctor)) U.(out_relev))
    (fun pos_ctor ctor e => make_type_ctor pos_block ctor pos_ctor e).

  (* 2.4 Closure all ctors *)
  Definition closure_ctors binder : info -> (info -> term) -> term :=
    fold_right_ie (closure_ctors_block binder) pdecl.(pmb_ind_bodies).



  (* 3. Make Return Type *)
  (* forall (B0 : R0) ... (Bm : Rm),
     forall (i1 : t1) ... (il : tl),
     forall (x : Ind A0 ... An B0 ... Bm i0 ... il),
      P B0 ... Bm i0 ... il x *)
  Definition make_return_type : nat -> one_inductive_body -> info -> term :=
    fun pos_block indb e =>
    e <- closure_nuparams tProd nuparams e ;;
    e <- closure_indices  tProd indb.(ind_indices) e ;;
    e <- mk_tProd (mkBindAnn (nNamed "x") indb.(ind_relevance))
                  (make_ind kname pos_block e)
                  (Some "VarCCL") e ;;
    (mkApps (make_predni pos_block e) (get "VarCCL" e)).


End GenTypes.