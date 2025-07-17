From TypingSafeAPI Require Import core.

From TypingSafeAPI Require Import context_access.
From TypingSafeAPI Require Import creating_terms.

From TypingSafeAPI Require Import imp_mdecl.

Definition mkApp u v := mkApps u [v].

(* closure functions *)
Definition closure_params : state -> imp_mdecl -> (state -> list key -> term) -> term :=
  fun s pdecl => closure_context s (get_params pdecl).

Definition closure_uparams : state -> imp_mdecl -> (state -> list key -> term) -> term :=
  fun s pdecl => closure_context s (get_uparams pdecl).

Definition closure_nuparams : state -> imp_mdecl -> (state -> list key -> term) -> term :=
  fun s pdecl => closure_context s (get_nuparams pdecl).

Definition closure_indices : state -> imp_mdecl -> nat -> (state -> list key -> term) -> term :=
  fun s pdecl pos_indb => closure_context s (get_indices pdecl pos_indb).



Unset Guard Checking.

Section GenRecursors.

Context (kname : kername).
Context (pdecl : imp_mdecl).
Context (nb_uparams : nat).
Context (E : global_env).

Definition gen_rec_type (pos_indb : nat) : term :=
  (* to deal with  *)
  let s := init_state in
  (* let* s := subst_ind s kname in *)
  let* s key_uparams := closure_uparams s pdecl in
  let* s key_nuparams := closure_nuparams s pdecl in
  let* s key_indices  := closure_indices  s pdecl pos_indb in
  tProd (mkBindAnn nAnon Relevant)
        (make_ind s kname pos_indb key_uparams key_nuparams key_indices)
        (tSort sProp).

Definition closure_uparams_ty s cc :
  let s' := add_old_context s (get_uparams pdecl) in
  let fcxt := subst_context s.(state_subst) 0 (get_uparams pdecl) in
  Σ ;;; s.(state_new_context) ,,, fcxt |- cc s' (fresh_keys s #|get_uparams pdecl|) : tSort sProp ->
  Σ ;;; s.(state_new_context) |- (let* s key_uparams := closure_uparams s pdecl in
                                cc s key_uparams) : tSort sProp.
Proof.
  unfold closure_uparams, closure_context.
  intros H.
  (* Search it_mkProd_or_LetIn. *)
Admitted.


Definition gen_rec_wt (pos_indb : nat) :
  Σ ;;; [] |- gen_rec_type pos_indb : (tSort sProp).
Proof.
  unfold gen_rec_type.
  change (@nil context_decl) with (init_state.(state_new_context)).
  apply closure_uparams_ty. cbn.






















(* Section GenTypes.

  Section MkPreds.

  Context (key_uparams : keys).

  (* 1.1.1 Builds the type of the predicate for the i-th block
    forall (B0 : R0) ... (Bm : Rm),
    forall (i1 : t1) ... (il : tl),
      (Ind A1 ... An B0 ... Bm i1 ... il) -> U)  *)
  Definition make_type_pred : state -> nat -> term :=
    fun s pos_indb =>
    let* s key_nuparams := closure_nuparams s pdecl in
    let* s key_indices  := closure_indices  s pdecl pos_indb in
    tProd (mkBindAnn nAnon Relevant)
          (make_ind s kname pos_indb key_uparams key_nuparams key_indices)
          (tSort sProp).

  (* 1.1.1 Associated continuation *)
  Definition naming_pred pos_indb : ident := "P" ^ string_of_nat pos_indb.

  Definition make_type_pred_cc s pos_indb cc : term :=
    mk_tProd s (mkBindAnn (nNamed (naming_pred pos_indb)) Relevant)
              (make_type_pred s pos_indb) cc.

  End MkPreds.

  Definition closure_preds : state -> keys -> (state -> keys -> term) -> term :=
    fun s key_uparams =>
      fold_right_state s (get_ind_bodies pdecl) (fun s pos_indb _ cc =>
          make_type_pred_cc key_uparams s pos_indb cc
      ).

End GenTypes.

(* ####################################### *)
(*    2. Make the type of the recursors    *)
(* ####################################### *)

Definition gen_rec_type (pos_indb : nat) : term :=
  (* to deal with  *)
  let s := init_state in
  (* let* s := subst_ind s kname in *)
  let* s key_uparams := closure_uparams s pdecl in
  let* s key_preds   := closure_preds   s key_uparams in
  let* s key_nuparams := closure_nuparams s pdecl in
  let* s key_indices  := closure_indices  s pdecl pos_indb in
  let* s key_VarMatch := mk_tProd s (mkBindAnn (nNamed "x") Relevant)
                          (make_ind s kname pos_indb key_uparams key_nuparams key_indices) in
  mkApps (geti_term s key_preds pos_indb)
          (get_terms s key_nuparams ++ get_terms s key_indices ++ [get_term s key_VarMatch]). *)



End GenRecursors.








