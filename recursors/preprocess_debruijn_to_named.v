From MetaCoq.Utils Require Import utils.
From MetaCoq.Utils Require Import MCString.
From MetaCoq.Template Require Import All.
From MetaCoq.Common Require Import Universes.

Import MCMonadNotation.

Require Import preliminary.


(* #################################
   ### DeBruinj Ind => Named Ind ###
   ################################# *)

(* Replace the arguments for a constructor by tVar x1 ... tVar xn  *)
Fixpoint name_args_of_ctor_aux (name_cst : ident) (cxt : context) (pos_arg : nat)
  (l : list term) : context * list term :=
  match cxt with
  | [] => ([],[])
  | decl::q =>
      let new_arg := tVar (make_name ["x"] pos_arg) in
      let '(nCxt, tVarCst) := (name_args_of_ctor_aux name_cst q (S pos_arg) (new_arg::l)) in
      ({| decl_name := decl.(decl_name) ;
          decl_body := decl.(decl_body) ;
          decl_type := subst l 0 decl.(decl_type)
      |} :: nCxt, new_arg :: tVarCst)
  end.

Definition name_args_of_ctor (name_cst : ident) (cxt : context) : context * list term :=
  name_args_of_ctor_aux name_cst cxt 0 [].


(* Preprocess a mutual inductive types by modfiying indices and ctors :
   1. Replace (tRel i) representing inductive blocks by (tInd ...)
   2. Replace (tRel i) representing paramters by (tVar "Ai")
   3. Replace (tRel i) representing arguments of ctors by (tVar "Cst_xi") *)

Section PreProcessing.

  (* 1. Mutual Inductive Body
      1.1 Name paramters dependently
      1.2 >>
    2. One Inductive Body
      2.1 Name param in indices dependently
      2.2 >>
    3. Constructors Body
      3.1 Name Arguments
        3.3.1 Name ind / param in Arg *)

  Context (kname : kername).
  Context (mdecl : mutual_inductive_body).

  Definition nb_blocks := #|mdecl.(ind_bodies)|.
  Definition nb_params := mdecl.(ind_npars).

  (* Replace [tRel (nb_blocks -1 + nb_params), ..., tRel (nb_params)] by tInd ... *)
  Definition ind_to_tVar : context -> context :=
    subst_context (inds kname [] mdecl.(ind_bodies)) nb_params.

   (* Replace [tRel (nb_params-1), ..., tRel (0)] by A0 ... Ak *)
  Definition param_to_tVar : context -> context :=
    subst_context (rev (gen_list_param mdecl.(ind_params))) 0.

  (* WHY ?!?!?!? *)
  Definition ind_param_to_tVar : context -> context :=
    subst_context (    (rev (gen_list_param mdecl.(ind_params)))
                    ++ (inds kname [] mdecl.(ind_bodies)))
                  0.

  Definition preprocess_ctor (ctor : constructor_body) : constructor_body :=
  (* let nargs1 := ind_to_tVar ctor.(cstr_args) in
  let nargs2 := param_to_tVar nargs1 in *)
  let nargs2 := ind_param_to_tVar ctor.(cstr_args) in
  let '(nargs3, tVarArgs) := name_args_of_ctor ctor.(cstr_name) (rev nargs2) in
  {| cstr_name    := ctor.(cstr_name) ;
      cstr_args    := nargs3 ;
      cstr_indices := map (fun indice => subst0 (rev (gen_list_args ctor.(cstr_args))) indice) ctor.(cstr_indices);
      cstr_type    := ctor.(cstr_type);
      cstr_arity   := ctor.(cstr_arity)
  |}.

  Definition preprocess_indb (indb : one_inductive_body) : one_inductive_body :=
    {| ind_name      := indb.(ind_name) ;
      (* 1. Name the parameters in indices *)
       ind_indices   := param_to_tVar indb.(ind_indices) ;
       ind_sort      := indb.(ind_sort) ;
       ind_type      := indb.(ind_type) ;
       ind_kelim     := indb.(ind_kelim) ;
       (* 2. preprocess the different ctors *)
       ind_ctors     := map preprocess_ctor indb.(ind_ctors) ;
       ind_projs     := indb.(ind_projs) ;
       ind_relevance := indb.(ind_relevance) ;
    |}.

Definition preprocessing_mind : _ :=
  {| ind_finite    := mdecl.(ind_finite)   ;
     ind_npars     := mdecl.(ind_npars)    ;
     ind_params    := mdecl.(ind_params)   ;
     ind_bodies    := map preprocess_indb mdecl.(ind_bodies)  ;
     ind_universes := mdecl.(ind_universes) ;
     ind_variance  := mdecl.(ind_variance)
  |}.


End PreProcessing.