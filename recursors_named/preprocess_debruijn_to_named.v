From MetaCoq.Utils Require Import utils.
From MetaCoq.Utils Require Import MCString.
From MetaCoq.Template Require Import All.

Require Import namming.
Require Import commons.



Fixpoint cxt_to_tVar_aux (f_naming : nat -> ident)
  (cxt : context) (pos_arg : nat) (l : list term) : context :=
  match cxt with
  | [] => []
  | decl::q => let new_arg  := tVar (f_naming pos_arg)  in
               let new_decl :=  {| decl_name := decl.(decl_name) ;
                                   decl_body := decl.(decl_body) ;
                                   decl_type := subst l 0 decl.(decl_type) |} in
               new_decl :: (cxt_to_tVar_aux f_naming q (S pos_arg) (new_arg::l))
  end.

(* Dependently rename a cxt *)
Definition cxt_to_tVar f_naming cxt :=
  rev (cxt_to_tVar_aux f_naming (rev cxt) 0 []).



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


  Definition tVar_ind_params :=
     (rev (list_tVar naming_param mdecl.(ind_params)))
  ++ (inds kname [] mdecl.(ind_bodies)).

  Definition ind_param_to_tVar : context -> context :=
    subst_context tVar_ind_params 0.

  Definition preprocess_ctor (ctor : constructor_body) : constructor_body :=
  {| cstr_name    := ctor.(cstr_name) ;
     cstr_args    := cxt_to_tVar naming_arg (ind_param_to_tVar ctor.(cstr_args)) ;
     cstr_indices := map (fun indice =>
                            subst0 (    rev (list_tVar naming_arg ctor.(cstr_args))
                                     ++ tVar_ind_params) indice)
                          (ctor.(cstr_indices));
     cstr_type    := ctor.(cstr_type);
     cstr_arity   := ctor.(cstr_arity)
  |}.

  Definition preprocess_indb (indb : one_inductive_body) : one_inductive_body :=
    {| ind_name      := indb.(ind_name) ;
      (* 1. Name the parameters in indices *)
       ind_indices   := cxt_to_tVar naming_indice (ind_param_to_tVar indb.(ind_indices)) ;
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
     ind_params    := cxt_to_tVar naming_param mdecl.(ind_params) ;
     ind_bodies    := map preprocess_indb mdecl.(ind_bodies)  ;
     ind_universes := mdecl.(ind_universes) ;
     ind_variance  := mdecl.(ind_variance)
  |}.


End PreProcessing.