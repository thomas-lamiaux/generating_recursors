From RecAPI Require Import api_debruijn.
From RecAPI Require Import custom_parametricty_rec_call.

Section CustomParam.

  Context (kname : kername).
  Context (mdecl : mutual_inductive_body).
  Context (nb_uparams : nat).
  Context (strpos_uparams : list bool).
  Context (E : global_env).
  Context (Ep : param_env).

Definition mk_entry : context -> list one_inductive_entry -> mutual_inductive_entry :=
  fun params inds_entry =>
  {| mind_entry_record    := None;
	   mind_entry_finite    := Finite;
     mind_entry_params    := params;
     mind_entry_inds      := inds_entry;
     mind_entry_universes := universes_entry_of_decl (ind_universes mdecl);
     mind_entry_template  := false;
     mind_entry_variance  := None;
     mind_entry_private   := None
  |}.


Definition name_map : (string -> string) -> name -> name :=
  fun f name => match name with
  | nNamed s => nNamed (f s)
  | nAnon => nAnon
  end.



(* 1. Make types associated to new inductive *)

Section MkNewTypes.

  Context (annoted_uparams : list (context_decl * bool)).

(* 1.1 Closure by uniform parameters and predicate if strictly positive *)
(* forall A, (PA : A -> Prop), ... *)
Definition closure_uparams_preds : state -> (list ident -> list ident -> list ident -> state -> term) -> term :=
  fold_right_state_opt3
    (fun _ ' (mkdecl an _ ty, b) s t =>
      let* id_uparam s <- kp_tProd an ty (Some "uparams") s in
      (* add a predicate *)
      match b with
      | false => t [id_uparam] [] [id_uparam] s
      | true => let name := name_map (fun x => "P" ^ x) an.(binder_name) in
          let ty_pred := tProd (mkBindAnn nAnon Relevant) (get_term id_uparam s) (tSort sProp) in
          let* id_pred s <- mk_tProd (mkBindAnn name Relevant) ty_pred (Some "preds")  s in
          t [id_uparam] [id_pred] [id_pred; id_uparam] s
      end
    ) annoted_uparams.

  (* 1.2 Make return type of the new inductive with parameters in the context *)
  (* forall i0 ... in, Ind A0 ... Al B0 ... Bm i0 ... in -> Prop *)
  Definition make_type_ind : list ident -> list ident -> nat -> state -> term :=
    fun id_uparams id_nuparams pos_indb s =>
    let* id_indices s <- closure_indices tProd kname pos_indb s in
    tProd (mkBindAnn nAnon Relevant)
          (make_ind kname pos_indb id_uparams id_nuparams id_indices s)
          (tSort sProp).

  Arguments make_type_ind id_uparams id_nuparams _ _ : rename.

  (* 1.3 Make the full new type *)
  (* forall A, (PA : A -> Prop) ... B0 ... forall i0 ... in, Ind A0 ... Al B0 ... Bm i0 ... in -> Prop *)
  Definition make_new_type : nat -> state -> term :=
    fun pos_indb s =>
    let* id_uparams id_preds id_uparams_preds s <- closure_uparams_preds s in
    let* id_nuparams s <- closure_nuparams tProd kname s in
    make_type_ind id_uparams id_nuparams pos_indb s.

  (* 1.4 Make the associated context *)
  Definition make_new_context : state -> context :=
    fun s =>
    let ind_bodies := get_ind_bodies kname s in
    let nb_bodies  := length ind_bodies in
    let an := mkBindAnn nAnon Relevant in
    fold_right_i (fun i _ x => mkdecl an None (make_new_type (nb_bodies -i -1) s) :: x)
      [] ind_bodies.

  (* 1.5 Add uniform parameters and predicate if strictly positive *)
  Definition add_uparams_preds {X} : state -> (list ident -> list ident -> list ident -> state -> X) -> X :=
    fold_right_state_opt3
      (fun _ ' (cdecl, b) s t =>
        let* id_uparam s <- add_old_var (Some "uparams") cdecl s in
        (* add a predicate *)
        match b with
        | false => t [id_uparam] [] [id_uparam] s
        | true => let name := name_map (fun x => "P" ^ x) cdecl.(decl_name).(binder_name) in
            let ty_pred := tProd (mkBindAnn nAnon Relevant) (get_term id_uparam s) (tSort sProp) in
            let* id_pred s <- add_fresh_var (Some "preds") (mkdecl (mkBindAnn name Relevant) None ty_pred) s in
            t [id_uparam] [id_pred] [id_pred; id_uparam] s
        end
      ) annoted_uparams.

  (* 1.6 Given an argument add the custom parametricty if needed *)
  #[local] Definition make_indp : list ident -> nat -> list ident -> list term -> list term -> state -> term :=
      fun id_inds pos_indb id_uparams_preds nuparams indices s =>
      mkApps (geti_term id_inds pos_indb s)
             (get_terms id_uparams_preds s ++ nuparams ++ indices).

End MkNewTypes.

(* 2. Compute custom param of an inductive block *)
Section MkInd.
  Context (id_inds    : list ident).
  Context (id_uparams : list ident).
  Context (id_preds   : list ident).
  Context (id_uparams_preds : list ident).
  Context (id_nuparams : list ident).
  Context (pos_indb : nat).

  (* 2.1 Add the paramtricity of an argument if one *)
  Definition make_type_arg : context_decl -> state ->
      (list ident -> list ident -> list ident -> state -> term) -> term :=
    fun '(mkdecl an db ty) s t =>
    match db with
    | Some db => kp_tLetIn an db ty s (fun x => t [x] [] [])
    | None =>
        let* id_arg s <- kp_tProd an ty (Some "args") s in
        let red_ty := reduce_except_lets E s (get_type id_arg s) in
        match make_cparam_call (make_indp id_inds) kname Ep
                id_uparams id_preds id_uparams_preds [] [] id_arg
                red_ty s with
        | Some (ty, _) => mk_tProd (mkBindAnn nAnon Relevant) ty (Some "rec_call") s
                            (fun id_rec => t [] [id_arg] [id_rec])
        | None => t [] [id_arg] [] s
        end
    end.

  (* 2.2 Build the type of the custom param of a constructor *)
  Definition mk_ty_cparam : nat -> constructor_body -> state -> term :=
    fun pos_ctor ctor s =>
    let* _ id_args _ s <- fold_left_state_opt3 (fun _ => make_type_arg) ctor.(cstr_args) s in
    (* ind_params1 A0 PA ... B0 ... Bn i0 ... im (cst A0 ... B0 ) *)
    mkApp (make_indp id_inds pos_indb id_uparams_preds
            (get_terms id_nuparams s) (get_ctor_indices kname pos_indb pos_ctor s) s)
          (mkApps (make_cst kname pos_indb pos_ctor id_uparams id_nuparams s)
                  (get_terms id_args s)).

  (* 2.3 Compute custom param of the inductive block *)
  Definition mk_ind_entry : one_inductive_body -> state -> one_inductive_entry :=
    fun indb s =>
    {| mind_entry_typename  := indb.(ind_name) ^ "_cparam" ;
       mind_entry_arity     := make_type_ind id_uparams id_nuparams pos_indb s;
       mind_entry_consnames := map (fun ctor => ctor.(cstr_name) ^ "_cparam") indb.(ind_ctors);
       mind_entry_lc        := mapi (fun x y => mk_ty_cparam x y s) indb.(ind_ctors);
    |}.

End MkInd.

(* 3. Compute the custom parametricty  *)
Definition custom_param : mutual_inductive_entry :=
  (* add inds to state *)
  let s := add_mdecl kname nb_uparams mdecl init_state in
  let annoted_uparams := combine (rev (get_uparams kname s)) strpos_uparams in
  (* Add new inds, uprams and pred, nuparams *)
  let* s <- replace_ind kname s in
  let* id_inds s <- add_fresh_context (Some "inds") (make_new_context annoted_uparams s) s in
  let* id_uparams id_preds id_uparams_preds s <- add_uparams_preds annoted_uparams s in
  let* _ id_nuparams _ s <- add_old_context (Some "nuparams") (get_nuparams kname s) s in
  (* get the context associated to the (new) parameters *)
  let params_preds := map state_def (firstn (length id_uparams_preds + length id_nuparams) s.(state_context)) in
  mk_entry params_preds
    (mapi (fun pos_indb indb => mk_ind_entry id_inds id_uparams id_preds id_uparams_preds id_nuparams pos_indb indb s)
          mdecl.(ind_bodies)).

End CustomParam.