From RecAPI Require Import api_debruijn.
From RecAPI Require Import compute_strict_pos_uparams.

Unset Guard Checking.

Section CustomParam.

  Context (kname : kername).
  Context (mdecl : mutual_inductive_body).
  Context (E : global_env).

Definition add_param1 : ident -> ident :=
  fun s => s ^ "_param1".

Definition custom_param_ctor : constructor_body -> constructor_body :=
  fun ctor =>
  {| cstr_name    := add_param1 ctor.(cstr_name) ;
	   cstr_args    := ctor.(cstr_args) ;
     cstr_indices := ctor.(cstr_indices) ;
     cstr_type    := ctor.(cstr_type) ;
     cstr_arity   := ctor.(cstr_arity)
    |}.

Definition custom_param_indb : one_inductive_body -> one_inductive_body :=
  fun indb =>
  {| ind_name      := add_param1 indb.(ind_name);
	   ind_indices   := indb.(ind_indices);
     ind_sort      := indb.(ind_sort);
     ind_type      := indb.(ind_type);
     ind_kelim     := indb.(ind_kelim);
     ind_ctors     := map custom_param_ctor indb.(ind_ctors);
     ind_projs     := indb.(ind_projs);
     ind_relevance := indb.(ind_relevance)
    |}.

Definition custom_param : mutual_inductive_body :=
(* let e:= init_info in *)
  {| ind_finite    := mdecl.(ind_finite);
     ind_npars     := mdecl.(ind_npars);
     (* (length (filter (fun x => eqb true x) strpos_uparams)); *)
     ind_params    := mdecl.(ind_params);
     ind_bodies    := map custom_param_indb mdecl.(ind_bodies);
     ind_universes := mdecl.(ind_universes);
     ind_variance  := mdecl.(ind_variance)
  |}.

End CustomParam.

(* Definition one_i1 : one_inductive_entry :=
{|
  mind_entry_typename := "demoBool";
  mind_entry_arity := tSort sProp;
  mind_entry_consnames := ["demoTrue2"; "demoFalse2"];
  mind_entry_lc := [tProd (mkBindAnn nAnon Relevant) (tRel 0) (tRel 1); tRel 0];
|}.

Definition mut_i : mutual_inductive_entry :=
{|
  mind_entry_record := None;
  mind_entry_finite := Finite;
  mind_entry_params := [];
  mind_entry_inds := [one_i1];
  mind_entry_universes := Monomorphic_entry (LevelSet.empty, ConstraintSet.empty);
  mind_entry_template := false;
  mind_entry_variance := None;
  mind_entry_private := None;
|}.

MetaCoq Unquote Inductive mut_i. *)


(* Definition strpos_uparams := strpos_preprocess_ctors kname mdecl E.


Definition cparam_arg : term -> info -> context :=
  fun x e => []. *)

(* 3. Compute the number of uniform parameters of a constructor *)
(* Definition cparam_args : context -> info -> context :=
  fun args e =>
  fold_left_ie
    ( fun i arg e t =>
        let e' := add_old_var (Some "args") arg e in
        match arg.(decl_body) with
        | None => let rty := reduce_full E e (e ↑ arg.(decl_type)) in
                  (cparam_arg rty e) ++ (t e')
        | Some _ => t e'
        end
  )
  args e (fun _ => []). *)


(* 4. Compute the number of uniform parameters of an inductive type *)
(* Definition preprocess_ctors : mutual_inductive_body :=
  let e := init_info in
  let e := replace_ind kname mdecl e in
  let e := add_context (Some "params") mdecl.(ind_params) e in
  mdecl. *)

