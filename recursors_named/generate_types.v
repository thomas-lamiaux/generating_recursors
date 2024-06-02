From MetaCoq.Utils Require Import utils.
From MetaCoq.Utils Require Import MCString.
From MetaCoq.Template Require Import All.

Require Import preliminary.
Require Import naming.
Require Import commons.

(* Functions in this file:
  - Must be applied to a fully named inductive type
  - Are parametric in (binder : aname -> term -> term -> term) to applied to
    tLambda or tProd depending if we want the recursor or its type

  Genrates :
  1. Make Type Predicate
  2. Make Type Constructor
     2.1 Rec call
     2.2 Type cst
  3. Make Return Type
  4. Closure Type Predicates and Constructors
*)


Unset Guard Checking.

Section GenTypes.

  Context (kname : kername).
  Context (mdecl : mutual_inductive_body).
  Context (U : term).
  Context (E : list (kername * mutual_inductive_body * kername)).

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

  (* 2. Closure constructors *)
  (* 2.1 Compute Rec Call *)

  (* ATTEMPTED TO HANDLE NESTED *)
  MetaCoq Quote Definition qTrue := True.

  (* Definition mylookup *)

  Definition isSome {A} (x : option A) : bool :=
    match x with
    | None => false
    | Some _ => true
    end.

  Fixpoint add_param (l : list term) (rc : list (option term)) : list term :=
    match l, rc with
    | nil, nil => nil
    | A::l, None :: rc => A :: (tLambda (mkBindAnn nAnon Relevant) A qTrue) :: add_param l rc
    | A::l, Some x :: rc => A :: x :: add_param l rc
    (* Should never happen *)
    | nil, x :: rc => nil
    | A::l, nil => nil
    end.

  Fixpoint rec_pred (ty : term) : option term :=
    let (hd, iargs) := decompose_app ty in
    match hd with
    | tInd (mkInd s pos_s) _ =>
        if eq_constant kname s
        then let s_indices := skipn nb_params iargs in
             (Some (make_pred pos_s s_indices))
        else match find (fun x => eq_constant s (fst (fst x))) E with
        | Some (_, s_medcl, kparam1) =>
             let s_nb_params := s_medcl.(ind_npars) in
             let s_params := firstn 100 iargs in
             let s_indices := skipn 100 iargs in
             let rc := map rec_pred s_params in
             if existsb (isSome (A := term)) rc (* Should be rc but issue WF !!! *)
             then Some (tApp (tInd (mkInd kparam1 pos_s) [])
                       (add_param s_params rc))
             else None
        | None => None
        end
    | _ => None
    end.

  Definition gen_rec_call' (pos_arg : nat) (arg_type : term) (next_closure : term) :  term :=
    match rec_pred arg_type with
    | Some P =>
        tProd (mkBindAnn nAnon relev_out_sort)
              (tApp P [tVar (naming_arg pos_arg)])
              next_closure
    | None => next_closure
    end.
  (* ATTEMPTED TO HANDLE NESTED *)


  (* 2.2 Generates the type associated to j-th constructor of the i-th block *)
  (* (forall x0 : t0, [P x0], ..., xn : tn, P n, P (cst A0 ... Ak t0 ... tn) -> t *)
  Definition make_type_ctor (pos_block : nat) (ctor : constructor_body)
      (pos_ctor : nat) : term :=
    closure_args_op tProd gen_rec_call' ctor.(cstr_args)      (* forall x0 : t0, [P ... x0] *)
      (tApp (make_pred pos_block (ctor.(cstr_indices)))      (* P (f0 i0) ... (fn in)      *)
            [tApp (make_cst kname params pos_block pos_ctor) (* Cst A0 ... Ak              *)
                  (list_tVar naming_arg ctor.(cstr_args))]). (* x0 ... xn                  *)


  (* 3. Generation Output *)
  (* forall i0 : t0, ... il : tl, forall (x : Ind A0 ... An i0 ... il), P i0 ... il x *)
  Definition make_return_type (pos_block : nat) (relev_ind_sort : relevance) (indices : context) : term :=
    closure_indices tProd indices
      (* Definition of forall (x : Ind A0 ... An i0 ... il),  P i0 ... il x  *)
      (tProd (mkBindAnn (nNamed "x") relev_ind_sort)
             (make_ind kname params pos_block indices)
             (tApp (make_pred pos_block (list_tVar naming_indice indices)) [tVar "x"])).


  (* 4. Closure *)
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
        (fun pos_ctor ctor => make_type_ctor pos_block ctor pos_ctor).

    (* Closure all ctors *)
    Definition closure_type_ctors (next : term) : term :=
      fold_right_i closure_type_ctors_block next mdecl.(ind_bodies).

  End Closure.
End GenTypes.


