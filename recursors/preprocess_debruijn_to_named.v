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
Definition preprocessing_mind (kname : kername) (mdecl : mutual_inductive_body) : _ :=
  (* Preliminaries *)
  let nb_blocks := #|mdecl.(ind_bodies)| in
  let nb_params := mdecl.(ind_npars) in
  (* Replace [tRel (nb_blocks -1 + nb_params), ..., tRel (nb_params)] by tInd ... *)
  let Klist := inds kname [] mdecl.(ind_bodies) in
  let name_ind : context -> context := subst_context Klist nb_params in
  (* Replace [tRel (nb_params-1), ..., tRel (0)] by A0 ... Ak *)
  let namedParams := gen_list_param mdecl.(ind_params) in
  let name_param : context -> context := subst_context (rev namedParams) 0 in

  (* Preprocess ctors :
     1. name inductive types, 2. name parameters, 3. replace args  *)
  let process_ctor : constructor_body -> constructor_body :=
  fun ctor => let nargs1 := name_ind ctor.(cstr_args) in
              let nargs2 := name_param nargs1 in
              let '(nargs3, tVarArgs) := name_args_of_ctor ctor.(cstr_name) (rev nargs2) in

      {| cstr_name    := ctor.(cstr_name) ;
         cstr_args    := nargs3 ;
         cstr_indices := map (fun indice => subst0 (rev tVarArgs) indice) ctor.(cstr_indices);
         cstr_type    := ctor.(cstr_type);
         cstr_arity   := ctor.(cstr_arity)
      |}
  in

  (* Preprocess inductive blocks *)
  let process_indb : one_inductive_body -> one_inductive_body :=
  fun indb =>
    {| ind_name      := indb.(ind_name) ;
      (* 1. Name the parameters in indices *)
       ind_indices   := name_param indb.(ind_indices) ;
       ind_sort      := indb.(ind_sort) ;
       ind_type      := indb.(ind_type) ;
       ind_kelim     := indb.(ind_kelim) ;
       (* 2. preprocess the different ctors *)
       ind_ctors     := map process_ctor indb.(ind_ctors) ;
       ind_projs     := indb.(ind_projs) ;
       ind_relevance := indb.(ind_relevance) ;
    |}
  in

  (* Apply the transformation through the mdecl *)
  modify_ind_bodies process_indb mdecl.