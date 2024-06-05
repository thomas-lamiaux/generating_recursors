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

  Context (kname : kername).
  Context (mdecl : mutual_inductive_body).
  Context (U : term).
  Context (E : list (kername * mutual_inductive_body * kername * kername)).

  Definition params := mdecl.(ind_params).
  Definition nb_params := #|params|.
  Definition relev_out_sort := relev_sort U.


  (* 1. Builds the type of the predicate for the i-th block
     forall (i1 : t1) ... (il : tl), Ind A1 ... An i1 ... il -> U)  *)
  Definition make_type_pred (pos_block : nat) (relev_ind_sort : relevance) (indices : context) : term :=
    closure_indices tProd indices
      (tProd (mkBindAnn nAnon relev_ind_sort)
             (make_ind kname params pos_block indices)
             U).

  (* 2. Generates type of a constructors *)
  Definition gen_rec_call_ty pos_arg arg_type next_closure : term :=
    match rec_pred kname mdecl E arg_type with
    | Some (P, _) =>
      tProd (mkBindAnn nAnon relev_out_sort)
              (mkApps P [tVar (naming_arg pos_arg)])
              next_closure
    | None => next_closure
    end.

  (* Generates the type associated to j-th constructor of the i-th block *)
  (* (forall x0 : t0, [P x0], ..., xn : tn, P n, P (cst A0 ... Ak t0 ... tn) *)
  Definition make_type_ctor' (pos_block : nat) (ctor : constructor_body)
      (pos_ctor : nat) : term :=

    fold_right_i (fun pos_arg arg next_closure =>
      let arg_name := aname_arg pos_arg arg in
      let ' mkdecl arg_name arg_body arg_type := arg in
      let rc := gen_rec_call_ty pos_arg arg_type next_closure in
      match arg_body with
      | Some bd => tLetIn arg_name bd arg_type rc
      | None => tProd arg_name arg.(decl_type) rc
      end


    )
    (* P (f0 i0) ... (fn in) (cst A0 ... Ak t0 ... tn) *)
      (mkApps (make_pred pos_block (ctor.(cstr_indices)))      (* P (f0 i0) ... (fn in)      *)
            [mkApps (make_cst kname params pos_block pos_ctor) (* Cst A0 ... Ak              *)
                  (list_tVar naming_arg ctor.(cstr_args))])  (* x0 ... xn                  *)
    (* Arguments *)
    (rev ctor.(cstr_args)).


  Definition make_type_ctor (pos_block : nat) (ctor : constructor_body)
      (pos_ctor : nat) : term :=
    closure_args_op tProd gen_rec_call_ty ctor.(cstr_args)   (* forall x0 : t0, [P ... x0] *)
      (mkApps (make_pred pos_block (ctor.(cstr_indices)))      (* P (f0 i0) ... (fn in)      *)
            [mkApps (make_cst kname params pos_block pos_ctor) (* Cst A0 ... Ak              *)
                  (list_tVar naming_arg ctor.(cstr_args))]). (* x0 ... xn                  *)

  (* 3. Generation Output *)
  (* forall i0 : t0, ... il : tl, forall (x : Ind A0 ... An i0 ... il), P i0 ... il x *)
  Definition make_return_type (pos_block : nat) (relev_ind_sort : relevance) (indices : context) : term :=
    closure_indices tProd indices
      (* Definition of forall (x : Ind A0 ... An i0 ... il),  P i0 ... il x  *)
      (tProd (mkBindAnn (nNamed "x") relev_ind_sort)
             (make_ind kname params pos_block indices)
             (mkApps (make_pred pos_block (list_tVar naming_indice indices)) [tVar "x"])).


  (* 4. Compute closure *)
  Section Closure.

    Context (binder : aname -> term -> term -> term).

    (* Closure all predicates *)
    Definition closure_type_preds : term -> term :=
      compute_closure binder mdecl.(ind_bodies) op_fold_id
                      (fun i indb => aname_pred i)
                      (fun i indb => make_type_pred i indb.(ind_relevance) indb.(ind_indices)).

    (* Closure all ctors of a block *)
    Definition closure_type_ctors_block (pos_block : nat) (indb : one_inductive_body) : term -> term :=
      compute_closure binder indb.(ind_ctors) op_fold_id
        (fun pos_ctor ctor => mkBindAnn (nNamed (make_name_bin "f" pos_block pos_ctor)) relev_out_sort)
        (fun pos_ctor ctor => make_type_ctor' pos_block ctor pos_ctor).

    (* Closure all ctors *)
    Definition closure_type_ctors (next : term) : term :=
      fold_right_i closure_type_ctors_block next mdecl.(ind_bodies).

  End Closure.
End GenTypes.


