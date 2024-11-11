From NamedAPI Require Import api_debruijn.
From NamedAPI Require Import commons.
From NamedAPI Require Import recursor_rec_call.

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

  Context (s : state).
  Context (key_uparams : keys).

  (* 1.1.1 Builds the type of the predicate for the i-th block
    forall (B0 : R0) ... (Bm : Rm),
    forall (i1 : t1) ... (il : tl),
      (Ind A1 ... An B0 ... Bm i1 ... il) -> U)  *)
  Definition make_type_pred : state -> nat -> term :=
    fun s pos_indb =>
    let* s key_nuparams := closure_nuparams tProd s kname in
    let* s key_indices  := closure_indices  tProd s kname pos_indb in
    tProd (mkBindAnn nAnon (get_relevance kname pos_indb s))
          (make_ind s kname pos_indb key_uparams key_nuparams key_indices)
          U.(out_univ).

  (* 1.2.1 Compute closure predicates *)
  Definition closure_preds : (state -> keys -> term) -> term :=
    fun cc =>
    closure_binder binder s (Some "preds") (get_ind_bodies kname s)
      (fun pos_indb indb => mkBindAnn (nNamed (naming_pred pos_indb)) U.(out_relev))
      (fun pos_indb indb s => make_type_pred s pos_indb)
      cc.

  End MkPreds.



  (* 1.2. Make Type Constructor(s) *)

  Section MkCtor.

  Context (s : state).
  Context (key_uparams : keys).
  Context (key_preds   : keys).

  (* 1.2.1 Generates the type associated to an argument *)
  (* forall x, [P x] storing the ident correctly *)
  Definition make_type_arg : context_decl -> state ->
      (state -> keys -> keys -> keys -> term) -> term :=
    fun '(mkdecl an db ty) s cc =>
    match db with
    | Some db => kp_tLetIn s an db ty (fun s x => cc s [x] [] [])
    | None => let* s key_arg := kp_tProd s (Some "args") an ty in
              let red_ty := reduce_full E s (get_type s key_arg) in
              match make_rec_call kname Ep s key_preds [] key_arg red_ty with
              | Some (ty, _) => mk_tProd s (Some "rec_call") (mkBindAnn nAnon Relevant) ty
                                  (fun s key_rec => cc s [] [key_arg] [key_rec])
              | None => cc s [] [key_arg] []
              end
    end.

  (* 2.2 Generates the type associated to a constructor *)
  (* forall (B0 : R0) ... (Bm : Rm),
     forall x0 : t0, [P x0], ..., xn : tn, [P n],
     P B0 ... Bm f0 ... fl (cst A0 ... An B0 ... Bm x0 ... xl) *)
  Definition make_type_ctor : state -> nat -> constructor_body -> nat -> term :=
  fun s pos_indb ctor pos_ctor =>
  let* s key_nuparams := closure_nuparams tProd s kname in
  let* s _ key_args _ := fold_left_state_opt3 (fun _ => make_type_arg) ctor.(cstr_args) s in
  mkApp (make_predn s key_preds pos_indb key_nuparams (get_ctor_indices kname pos_indb pos_ctor s))
        (mkApps (make_cst s kname pos_indb pos_ctor key_uparams key_nuparams)
                (get_terms s key_args)).

  (* 2.3 Closure ctors of one inductive block *)
  Definition closure_ctors_block : nat -> one_inductive_body -> state -> (state -> keys -> term) -> term :=
    fun pos_indb indb s =>
    closure_binder binder s (Some "ctors") indb.(ind_ctors)
    (fun pos_ctor ctor => mkBindAnn (nNamed (make_name_bin "f" pos_indb pos_ctor)) U.(out_relev))
    (fun pos_ctor ctor s => make_type_ctor s pos_indb ctor pos_ctor).

  (* 2.4 Closure all ctors *)
  Definition closure_ctors : (state -> list keys -> term) -> term :=
    fun cc => fold_right_state closure_ctors_block (get_ind_bodies kname s) s cc.

  End MkCtor.


  (* 1.3 Make Return Type *)

  Section MkCcl.

  Context (s :state).
  Context (key_uparams : keys).
  Context (key_preds   : keys).
  Context (pos_indb : nat).

  (* 1.3.1 Make the type of the conclusion *)
  (* P B0 ... Bm i0 ... il x *)
  Definition make_ccl : state -> keys -> keys -> key -> term :=
    fun s key_nuparams key_indices key_VarMatch =>
    mkApp (make_predn s key_preds pos_indb key_nuparams (get_terms s key_indices))
          (get_term s key_VarMatch).

  (* 1.3.2 Make the return type *)
  (* forall (B0 : R0) ... (Bm : Rm),
     forall (i1 : t1) ... (il : tl),
     forall (x : Ind A0 ... An B0 ... Bm i0 ... il),
      P B0 ... Bm i0 ... il x *)
  Definition make_return_type : term :=
    let* s key_nuparams := closure_nuparams tProd s kname in
    let* s key_indices  := closure_indices  tProd s kname pos_indb in
    let* s key_VarMatch := mk_tProd s (Some "VarMatch")
                            (mkBindAnn (nNamed "x") (get_relevance kname pos_indb s))
                            (make_ind s kname pos_indb key_uparams key_nuparams key_indices) in
    make_ccl s key_nuparams key_indices key_VarMatch.

  End MkCcl.

  End GenTypes.



(* ####################################### *)
(*    2. Make the type of the recursors    *)
(* ####################################### *)

Definition gen_rec_type (pos_indb : nat) : term :=
  let s := add_mdecl kname nb_uparams mdecl init_state in
  let* s := replace_ind s kname in
  let* s key_uparams := closure_uparams tProd s kname in
  let* s key_preds   := closure_preds   tProd s key_uparams in
  let* s key_ctors   := closure_ctors   tProd s key_uparams key_preds in
  make_return_type s key_uparams key_preds pos_indb.



(* ####################################### *)
(*    3. Make the type of the recursors    *)
(* ####################################### *)

(* 3.1 Compute the arguments of the rec call *)
Section GetRecCall.

  Context (s : state).
  Context (key_preds : keys).
  Context (key_fixs  : keys).

  Definition compute_args_fix : keys -> list term :=
    fun key_args =>
    fold_right (fun key_arg t =>
      let red_ty := reduce_full E s (get_type s key_arg) in
      match make_rec_call kname Ep s key_preds key_fixs key_arg red_ty with
      | Some (rc_ty, rc_tm) => (get_term s key_arg) :: rc_tm :: t
      | None => (get_term s key_arg) :: t
      end
    ) [] key_args.

End GetRecCall.


(* 3.2 Generates the recursor *)
Definition gen_rec_term (pos_indb : nat) : term :=
  (* 0. Initialise state with inductives *)
  let s := add_mdecl kname nb_uparams mdecl init_state in
  let* s := replace_ind s kname in
  (* 1. Closure Uparams / preds / ctors *)
  let* s key_uparams := closure_uparams tLambda s kname in
  let* s key_preds   := closure_preds   tLambda s key_uparams in
  let* s key_ctors   := closure_ctors   tLambda s key_uparams key_preds in
  (* 2. Fixpoint *)
  let tFix_type pos_indb := make_return_type s key_uparams key_preds pos_indb in
  let tFix_rarg := tFix_default_rarg s kname in
  let* s key_fixs pos_indb := mk_tFix kname tFix_type tFix_rarg s pos_indb in
  (* 3. Closure Nuparams / Indices / Var *)
  let* s key_nuparams := closure_nuparams tLambda s kname in
  let* s key_indices  := closure_indices  tLambda s kname pos_indb in
  let* s key_VarMatch := mk_tLambda s (Some "VarMatch")
                        (mkBindAnn (nNamed "x") Relevant)
                        (make_ind s kname pos_indb key_uparams key_nuparams key_indices) in
  (* 4. Proof of P ... x by match *)
  let tCase_pred := (fun s => make_ccl key_preds pos_indb s key_nuparams) in
  let* s _ key_args _ pos_ctor := mk_tCase kname pos_indb
          tCase_pred key_uparams key_nuparams s (get_term s key_VarMatch) in
  (* 5. Make the branch *)
  (mkApps (getij_term s key_ctors pos_indb pos_ctor)
          (get_terms s key_nuparams ++ compute_args_fix s key_preds key_fixs key_args)).
            (* [state_to_term s])). *)



End GenRecursors.