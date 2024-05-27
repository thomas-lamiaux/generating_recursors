From MetaCoq.Utils Require Import utils.
From MetaCoq.Utils Require Import MCString.
From MetaCoq.Template Require Import All.

Require Import namming.
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


Section GenTypes.

  Context (kname : kername).
  Context (mdecl : mutual_inductive_body).

  Definition params := mdecl.(ind_params).
  Definition nb_params := #|params|.


  (* 1. Builds the type of the predicate for the i-th block
     forall (i1 : t1) ... (il : tl), Ind A1 ... An i1 ... il -> U)  *)
  Definition make_type_pred (pos_block : nat) (indices : context) (U : term) : term :=
    closure_indices tProd indices ((make_ind kname params pos_block indices) t-> U).


  (* 2. Closure constructors *)
  (* 2.1 Compute Rec Call
  Check if the type is one of the inductive block, if so adds a rec call *)
  Definition gen_rec_call (pos_arg : nat) (arg_type : term) (next : term) : term :=
    let '(hd, iargs) := decompose_app arg_type in
    match hd with
    | tInd {|inductive_mind := s; inductive_ind := pos_block |} _
        => if eq_constant kname s
          then tApp (make_pred pos_block (skipn nb_params iargs))
                    [tVar (name_arg pos_arg)]
               t-> next
          else next
    | _ => next
    end.

  (* 2.2 Generates the type associated to j-th constructor of the i-th block *)
  (* (forall x0 : t0, [P x0], ..., xn : tn, P n, P (cst A0 ... Ak t0 ... tn) -> t *)
  Definition make_type_ctor (pos_block : nat) (ctor : constructor_body)
      (pos_ctor : nat) : term :=
    closure_args_op tProd ctor.(cstr_args) gen_rec_call (* forall x0 : t0, [P ... x0] *)
      (tApp (make_pred pos_block (ctor.(cstr_indices))) (* P (f0 i0) ... (fn in) *)
            [tApp (make_cst kname params pos_block pos_ctor) (* Cst A0 ... Ak *)
                  (gen_list_args ctor.(cstr_args))]).


  (* 3. Generation Output *)
  (* forall i0 : t0, ... il : tl, forall (x : Ind A0 ... An i0 ... il), P i0 ... il x *)
  Definition make_return_type (pos_block : nat) (indices : context) : term :=
    closure_indices tProd indices
      (* Definition of forall (x : Ind A0 ... An i0 ... il),  P i0 ... il x  *)
      (tProd (mkBindAnn (nNamed "x") Relevant)
             (make_ind kname params pos_block indices)
             (tApp (make_pred pos_block (gen_list_indices indices)) [tVar "x"])).


  (* 4. Closure *)
  Section Closure.

    Context (binder : aname -> term -> term -> term).

    (* Closure all predicates *)
    Definition closure_type_preds (U : term) : term -> term :=
      compute_closure binder mdecl.(ind_bodies) op_fold_id
                      (fun i indb => aname_pred i)
                      (fun i indb => make_type_pred i indb.(ind_indices) U).

    (* Closure all constructors *)
    Definition closure_type_ctors : term -> term :=
      let all_ctors := gather_ctors mdecl in
      compute_closure binder all_ctors op_fold_id
                      (fun i ijctor => let '(pos_block, pos_ctor, ctor) := ijctor in
                                       make_raname (make_name_bin "f" pos_block pos_ctor))
                      (fun i ijctor => let '(pos_block, pos_ctor, ctor) := ijctor in
                                       make_type_ctor pos_block ctor pos_ctor).

  End Closure.
End GenTypes.


