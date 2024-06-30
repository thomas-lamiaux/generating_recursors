From MetaCoq.Utils Require Import utils.
From MetaCoq.Utils Require Import MCString.
From MetaCoq.Template Require Import All.

From MetaCoq Require Import BasePrelude.


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
  Definition make_type_pred (pos_block : nat) (relev_ind_sort : relevance) (indices : context) (e : infolocal) : term :=
    e <- closure_nuparams tProd nuparams e ;;
    e <- closure_indices tProd indices e ;;
    tProd (mkBindAnn nAnon relev_ind_sort)
          (make_ind kname pos_block e)
          U.(out_univ).

  (* 1.2 Compute predicate *)
  Definition closure_preds binder : infolocal -> (infolocal -> term) -> term :=
    iterate_binder
      "preds" binder pdecl.(pmb_ind_bodies)
      (fun pos_block indb => mkBindAnn (nNamed (naming_pred pos_block)) U.(out_relev))
      (fun pos_block indb e => make_type_pred pos_block indb.(ind_relevance) indb.(ind_indices) e).



  (* 2. Make Type Constructor(s) *)

  (* 2.1 Make Type Rec Hypothesis *)
  Definition make_rec_ty arg_type e (next_closure : infolocal -> term) : term :=
    match make_rec_pred pdecl E arg_type e with
    | Some (wfP, _) =>
      e <- mktProd NoSave (mkBindAnn nAnon U.(out_relev)) e
                  (mkApp wfP (geti_info "args" e 0)) ;;
      next_closure e
    | None => next_closure e
    end.

  (* Generates the type associated to j-th constructor of the i-th block *)
  (* forall (B0 : R0) ... (Bm : Rm),
     forall x0 : t0, [P x0], ..., xn : tn, [P n],
     P B0 ... Bm f0 ... fl (cst A0 ... An B0 ... Bm x0 ... xl) *)
  Definition make_type_ctor (pos_block : nat) (ctor : constructor_body)
      (pos_ctor : nat) (e : infolocal) : term :=

    (* 1. Closure nuparams *)
    e <- closure_nuparams tProd nuparams e ;;

    (* 2. Closure Arguments and Rec Call *)
    (* (fold_left_ie (fun pos_arg arg e next_closure =>
      kptProd (Savelist "args") arg.(decl_name) e arg.(decl_type) next_closure))
    ( ctor.(cstr_args)) e *)
    e <- it_kptProd (Some "args" ) ctor.(cstr_args) e ;;

    (* 3. Conclusion *)
    (* P B0 ... Bm f0 ... fl (cst A0 ... An B0 ... Bm x0 ... xl) *)
    (* (fun e => *)
      mkApp (make_predn nb_block pos_block e ctor.(cstr_indices))
            (mkApps (make_cst kname pos_block pos_ctor e) (rels_of "args" e))
            (* ). *)
    .

    (* Handle let and rec call
      match arg.(arg_body) with
      | Some bd => kptLetIn arg.(arg_name) bd arg.(arg_type) e next_closure
      | None => let rc := gen_rec_call_ty pos_arg arg_type next_closure in
                kptProd ard.(decl_name) arg.(decl_type) rc
      end
    )*)

  (* Closure all ctors of a block *)            (* CHECK RELEVANCE *)
  Definition closure_ctors_block binder (pos_block : nat) (idecl : one_inductive_body)
      : infolocal -> (infolocal -> term) -> term :=
    iterate_binder
    "f" binder idecl.(ind_ctors)
    (fun pos_ctor ctor => mkBindAnn (nNamed (make_name_bin "f" pos_block pos_ctor)) U.(out_relev))
    (fun pos_ctor ctor e => make_type_ctor pos_block ctor pos_ctor e).

  (* Closure all ctors *)
  Definition closure_ctors binder : infolocal -> (infolocal -> term) -> term :=
    fold_right_ie (closure_ctors_block binder) pdecl.(pmb_ind_bodies).


  (* 3. Make Return Type *)
  (* forall (B0 : R0) ... (Bm : Rm),
     forall (i1 : t1) ... (il : tl),
     forall (x : Ind A0 ... An B0 ... Bm i0 ... il),
      P B0 ... Bm i0 ... il x *)
  Definition make_return_type (pos_block : nat) (idecl : one_inductive_body) (e : infolocal) : term :=
    e <- closure_nuparams tProd nuparams e ;;
    e <- closure_indices tProd idecl.(ind_indices) e ;;
    e <- mktProd (Saveitem "x") (mkBindAnn (nNamed "x") idecl.(ind_relevance)) e
         (make_ind kname pos_block e) ;;
    (mkApp (make_predni nb_block pos_block e) (rel_of "x" e)).


End GenTypes.
