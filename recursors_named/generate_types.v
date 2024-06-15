From MetaCoq.Utils Require Import utils.
From MetaCoq.Utils Require Import MCString.
From MetaCoq.Template Require Import All.

Require Import naming.
Require Import commons.
Require Import generate_rec_call.

(* Functions in this file:
  - Must be applied to a fully named inductive type
  - Are parametric in (binder : aname -> term -> term -> term) to applied to
    tLambda or tProd depending if we want the recursor or its type

  Genrates :
  1. Make Type Predicate
  2. Make Type Constructor
  3. Make Return Type
  4. Closure Type Predicates and Constructors
*)

Section GenTypes.

  Context (pdecl : preprocess_mutual_inductive_body).
  Context (U : output_univ).
  Context (E : env_param).

  Definition kname := pdecl.(pmb_kname).
  Definition uparams  := pdecl.(pmb_uparams).
  Definition nuparams := pdecl.(pmb_nuparams).

  (* 1. Builds the type of the predicate for the i-th block
     forall (B0 : R0) ... (Bm : Rm),
     forall (i1 : t1) ... (il : tl),
        (Ind A1 ... An B0 ... Bm i1 ... il) -> U)  *)
  Definition make_type_pred (pos_block : nat) (relev_ind_sort : relevance) (indices : context) : term :=
     closure_nuparams tProd nuparams
    (closure_indices  tProd indices
      (tProd (mkBindAnn nAnon relev_ind_sort)
             (make_ind kname pos_block uparams nuparams indices)
             U.(out_univ))).

  (* 2. Generates type of a constructors *)
  Definition gen_rec_call_ty pos_arg arg_type next_closure : term :=
    match rec_pred pdecl E arg_type with
    | Some (wfP, _) =>
      tProd (mkBindAnn nAnon U.(out_relev))
            (mkApps wfP [tVar (naming_arg pos_arg)])
            next_closure
    | None => next_closure
    end.

  (* Generates the type associated to j-th constructor of the i-th block *)
  (* (forall x0 : t0, [P x0], ..., xn : tn, P n, P (cst A0 ... Ak t0 ... tn) *)
  Definition make_type_ctor_db (pos_block : nat) (ctor : constructor_body)
      (pos_ctor : nat) : term :=

    (* Computation Scheme *)
    fold_right_i (fun pos_arg arg next_closure =>
      let arg_name := aname_arg pos_arg arg in
      let ' mkdecl _ arg_body arg_type := arg in
      match arg_body with
      | Some bd => tLetIn arg_name bd arg_type next_closure
      | None => let rc := gen_rec_call_ty pos_arg arg_type next_closure in
                tProd arg_name arg_type rc
      end
    )
    (* Conclusion *)
    (* P B0 ... Bm f0 ... fl (cst A0 ... An B0 ... Bm x0 ... xl) *)
      (* P B0 ... Bm f0 ... fl  *)
      (mkApps (make_predc pos_block nuparams (ctor.(cstr_indices)))
              (* Cst A0 ... Ak B0 ... Bl *)
              [mkApps (make_cst kname pos_block pos_ctor uparams nuparams)
                      (* x0 ... xn *)
                      (list_tVar_let naming_arg ctor.(cstr_args))])
    (* Arguments *)
    (rev ctor.(cstr_args)).

  Definition make_type_ctor (pos_block : nat) (ctor : constructor_body)
    (pos_ctor : nat) : term :=
  closure_nuparams tProd nuparams (make_type_ctor_db pos_block ctor pos_ctor).


  (* 3. Generation Output *)
  (* forall (B0 : R0) ... (Bm : Rm),
     forall (i1 : t1) ... (il : tl),
     forall (x : Ind A0 ... An B0 ... Bm i0 ... il),
      P B0 ... Bm i0 ... il x *)
  Definition make_return_type (pos_block : nat) (relev_ind_sort : relevance) (indices : context) : term :=
     closure_nuparams tProd nuparams
    (closure_indices tProd indices
      (tProd (mkBindAnn (nNamed "x") relev_ind_sort)
             (make_ind kname pos_block uparams nuparams indices)
             (mkApps (make_predc pos_block nuparams (list_tVar naming_indice indices))
                     [tVar "x"]))).


  (* 4. Compute closure *)
  Section Closure.

    Context (binder : aname -> term -> term -> term).

    (* Closure all predicates *)
    Definition closure_type_preds : term -> term :=
      compute_closure binder pdecl.(pmb_ind_bodies) op_fold_id
                      (fun i indb => aname_pred i)
                      (fun i indb => make_type_pred i indb.(ind_relevance) indb.(ind_indices)).

    (* Closure all ctors of a block *)
    Definition closure_type_ctors_block (pos_block : nat) (indb : one_inductive_body) : term -> term :=
      compute_closure binder indb.(ind_ctors) op_fold_id
        (fun pos_ctor ctor => mkBindAnn (nNamed (make_name_bin "f" pos_block pos_ctor)) U.(out_relev))
        (fun pos_ctor ctor => make_type_ctor pos_block ctor pos_ctor).

    (* Closure all ctors *)
    Definition closure_type_ctors (next : term) : term :=
      fold_right_i closure_type_ctors_block next pdecl.(pmb_ind_bodies).

  End Closure.
End GenTypes.


