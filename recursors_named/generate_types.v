From MetaCoq.Utils Require Import utils.
From MetaCoq.Utils Require Import MCString.
From MetaCoq.Template Require Import All.

Require Import preliminary.

(* Functions in this file:
  - Must be applied to a fully named inductive type
  - Are parametric in (binder : aname -> term -> term -> term) to applied to
    tLambda or tProd depending if we want the recursor or its type

  Genrates :
  1. Different closure functions
  2. Generation of types
     2.1 Make Types
  3. Closure Constructors
  4. Return type
*)


(* 1. Different closure functions *)
Section ComputeClosure.

  Context (binder : aname -> term -> term -> term).

  Definition compute_closure {A} (l : list A) (op_fold : nat -> term -> term -> term)
    (naming : nat -> A -> aname) (typing : nat -> A -> term) (next : term) : term :=
    fold_right_i
    (fun i a next_closure =>
      binder (naming i a) (typing i a) (op_fold i (typing i a) next_closure))
    next
    l.

  Definition op_fold_id : nat -> term -> term -> term := fun _ _ x => x.

  Definition closure_param (params : context) : term -> term  :=
    compute_closure (rev params) op_fold_id
                    (fun _ param => param.(decl_name))
                    (fun _ param => param.(decl_type)).

  Definition closure_indices (indices : context) : term -> term :=
    compute_closure (rev indices) op_fold_id
                    (fun i indice => make_raname (make_name "i" i))
                    (fun _ indice => indice.(decl_type)).

  Definition closure_args_op (args : context) (op_fold : nat -> term -> term -> term) :=
    compute_closure (rev args) op_fold
                    (fun i arg => make_raname (make_name "x" i))
                    (fun _ arg => arg.(decl_type)).

End ComputeClosure.


Section MakeTerms.

  Context (kname : kername).
  Context (params : context).
  Context (pos_block : nat).

  (* Builds: Ind A1 ... An i1 ... il *)
  Definition make_ind (pos_block : nat) (indices : context) : term :=
    tApp (tInd (mkInd kname pos_block) [])
          (gen_list_param params ++ gen_list_indices indices).

  (* Builds: P_i i1 ... il *)
  Definition make_pred (pos_block : nat) (tindices : list term) : term :=
    tApp (tVar (make_name0 "P" pos_block)) tindices.

  (* Builds: Cst A1 ... An *)
  Definition make_cst (pos_block pos_ctor : nat) : term :=
    tApp (tConstruct (mkInd kname pos_block) pos_ctor [])
          (gen_list_param params).

End MakeTerms.




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
                    [tVar (make_name "x" pos_arg)]
               t-> next
          else next
    | _ => next
    end.

  (* 2.2 Generates the type associated to j-th constructor of the i-th block *)
  (* (forall x0 : t0, [P x0], ..., xn : tn, P n, P (cst A0 ... Ak t0 ... tn) -> t *)
  Definition make_type_ctor (pos_block : nat) (ctor : constructor_body)
      (pos_ctor : nat) : term :=
    closure_args_op tProd ctor.(cstr_args) gen_rec_call
      (tApp (make_pred pos_block (ctor.(cstr_indices)))
            [tApp (make_cst kname params pos_block pos_ctor)
                  (gen_list_args ctor.(cstr_args))]).

  (* Generation Output *)
  (* forall i0 : t0, ... il : tl, forall (x : Ind A0 ... An i0 ... il), P i0 ... il x *)
  Definition return_type (pos_block : nat) (indices : context) : term :=
    closure_indices tProd indices
      (* Definition of forall (x : Ind A0 ... An i0 ... il),  P i0 ... il x  *)
      (tProd (mkBindAnn (nNamed "x") Relevant)
             (make_ind kname params pos_block indices)
             (tApp (make_pred pos_block (gen_list_indices indices)) [tVar "x"])).

  Section Closure.

    Context (binder : aname -> term -> term -> term).

    (* Closure all predicates *)
    Definition closure_type_preds (U : term) : term -> term :=
      compute_closure binder mdecl.(ind_bodies) op_fold_id
                      (fun i indb => make_raname (make_name0 "P" i))
                      (fun i indb => make_type_pred i indb.(ind_indices) U).

    (* Closure all constructors *)
    Definition closure_type_ctors : term -> term :=
      let all_ctors := gather_ctors mdecl in
      compute_closure binder all_ctors op_fold_id
                      (fun i ijctor => make_raname (make_name0 "f" i))
                      (fun i ijctor => let '(pos_block, pos_ctor, ctor) := ijctor in
                                       make_type_ctor pos_block ctor pos_ctor).

  End Closure.
End GenTypes.


