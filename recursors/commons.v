From MetaCoq.Utils Require Import utils.
From MetaCoq.Utils Require Import MCString.
From MetaCoq.Template Require Import All.
From MetaCoq.Common Require Import Universes.

Import MCMonadNotation.

Require Import preliminary.

(* Functions in this file:
  - Must be applied to a fully named inductive type
  - Are parametric in (binder : aname -> term -> term -> term) to applied to
    tLambda or tProd depending if we want the recursor or its type

  Genrates :
  1. Closure Parameters
  2. Closure Predicates
  3. Closure Constructors
*)


Section ComputeClosure.

  Context (binder : aname -> term -> term -> term).
  Context (kname  : kername).
  Context (mdecl  : mutual_inductive_body).

  Definition params := mdecl.(ind_params).
  Definition nb_params := #|params|.


  (* 1. Closure Parameters *)
  Definition closure_param (next : term) : term :=
  fold_right
    (fun param t' => binder param.(decl_name) (param.(decl_type)) t')
    next
    (rev params).


  (* 2 Closure Predicates *)

  (* 2.1 Generates the type of the predicate for the i-th block
     forall (i1 : t1) ... (il : tl), Ind A1 ... An i1 ... il -> U)  *)
  Definition type_one_pred (pos_block : nat) (indb : one_inductive_body)
    (U : term) : term :=
    (* Closure indices : forall i1 : t1 ... il : tl  *)
    fold_right_i
      (fun pos_index indice next_closure =>
        tProd (mkBindAnn (nNamed (make_name ["i"] pos_index)) Relevant)
              indice.(decl_type)
              next_closure)
      (* Body: definition of Ind A1 ... An i1 ... il -> U  *)
      (tProd AnonRel
        (tApp (tInd (mkInd kname pos_block) [])
              (gen_list_param params ++ gen_list_indices indb.(ind_indices)))
        U)
      (* Indices *)
      (rev indb.(ind_indices)).

  (* 2.2 Closure all predicates *)
  Definition closure_pred (U : term) (next : term) : term :=
    fold_right_i
      (fun pos_block indb next_clos =>
        binder (mkBindAnn (nNamed (make_pred "P" pos_block)) Relevant)
               (type_one_pred pos_block indb U)
               next_clos)
      next
      mdecl.(ind_bodies).


  (* 3. Closure constructors *)

  (* 3.1 Compute Rec Call
  Check if the type is one of the inductive block, if so adds a rec call *)
  Definition gen_rec_call (pos_arg : nat) (arg_type : term) (next : term) : term :=
    let '(hd, iargs) := decompose_app arg_type in
    match hd with
    | tInd {|inductive_mind := s; inductive_ind := pos_block |} _
        => if eq_constant kname s
          then tProd AnonRel
                     (tApp (tVar (make_pred "P" pos_block))
                           ( skipn nb_params iargs ++
                             [tVar (make_name ["x"] pos_arg)]))
                     next
          else next
    | _ => next
    end.

  (* 3.2 Generates the type associated to j-th constructor of the i-th block *)
  (* (forall x0 : t0, [P x0], ..., xn : tn, P n, P (cst A0 ... Ak t0 ... tn) -> t *)
  Definition type_one_ctor (pos_block : nat) (ctor : constructor_body)
      (pos_ctor : nat) : term :=
    (* Closure args and rec call : forall x0 : t0, P x0, ..., xn : tn, P n  *)
    fold_right_i
      (fun pos_arg arg next_closure =>
        tProd (mkBindAnn (nNamed (make_name ["x"] pos_arg)) Relevant)
              arg.(decl_type)
              (* rec call *)
              (gen_rec_call pos_arg arg.(decl_type) next_closure))
      (* Definition of P (i1 ... in) (cst A0 ... Ak x0 ... xn) *)
      (tApp (tVar (make_pred "P" pos_block))
            ((ctor.(cstr_indices)) ++
            (* cst A0 ... Ak x0 ... xn *)
            [tApp (tConstruct (mkInd kname pos_block) pos_ctor [])
                  (gen_list_param params ++ gen_list_args ctor.(cstr_args)  )]))
      (* Arguments *)
      ctor.(cstr_args).

  (* 3.3 Closure all predicates *)
  Definition closure_ctors (next : term) : term :=
  let all_ctors := gather_ctors mdecl in
  fold_right
    (fun ijctor next_closure =>
      let '(pos_block, pos_ctor, ctor) := ijctor in
      binder AnonRel
             (type_one_ctor pos_block ctor pos_ctor)
             next_closure)
    next
    all_ctors.

End ComputeClosure.