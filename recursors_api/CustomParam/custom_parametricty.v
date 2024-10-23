From RecAPI Require Import api_debruijn.
From RecAPI Require Import custom_parametricty_rec_call.

Section CustomParam.

  Context (kname : kername).
  Context (mdecl : mutual_inductive_body).
  Context (nb_uparams : nat).
  Context (strpos_uparams : list bool).
  Context (E : global_env).
  Context (Ep : env_param).

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






(* 1. Add predicate for strpos uparams *)
Definition add_uparams {X} : (list (context_decl * bool)) -> state -> (list ident -> list ident -> list ident -> state -> X) -> X :=
  fold_right_state_opt3
    (fun _ ' (cdecl, b) s t =>
      (* add old_param *)
      let id_uparam := fresh_ident (Some "uparams") s in
      let s := add_old_var id_uparam cdecl s in
      (* add a predicate *)
      match b with
      | false => t [id_uparam] [] [id_uparam] s
      | true =>
          let name := match cdecl.(decl_name).(binder_name) with
                      | nAnon => nAnon
                      | nNamed s => nNamed ("P" ^ s)
                      end in
          let id_pred := fresh_ident (Some "preds") s in
          let ty_pred := tProd (mkBindAnn nAnon Relevant) (get_one_term id_uparam s) (tSort sProp) in
          let s := add_fresh_var id_pred (mkdecl (mkBindAnn name Relevant) None ty_pred) s in
          t [id_uparam] [id_pred] [id_pred; id_uparam] s
      end
    ).


(* 2. Compute custom param of an inductive block *)
Section MkInd.
  Context (id_inds    : list ident).
  Context (id_uparams : list ident).
  Context (id_preds   : list ident).
  Context (id_uparams_preds : list ident).
  Context (id_nuparams : list ident).
  Context (pos_indb : nat).

  (* 2.1 Make new type of the inductive *)
  (* forall i0 ... in, Ind A0 ... Al B0 ... Bm i0 ... in -> Prop *)
  Definition make_type_ind : state -> term :=
    fun s =>
    let* id_indices s <- closure_indices tProd kname pos_indb s in
    tProd (mkBindAnn nAnon Relevant)
          (make_ind kname pos_indb id_uparams id_nuparams id_indices s)
          (tSort sProp).

  (* 2.2 Make the type of the new constructor *)

  (* 2.2.1 Given an argument add the custom parametricty if needed *)
  #[local]
  Definition make_Ind : nat -> list ident -> list term -> list term -> state -> term :=
    fun pos_indb id_uparams_preds nuparams indices s =>
    let id_ind := get_id1 id_inds pos_indb in
    mkApps (get_term_pos id_ind s)
            (get_term id_uparams_preds s ++ nuparams ++ indices).

  Definition make_type_arg : context_decl -> state ->
      (list ident -> list ident -> list ident -> state -> term) -> term :=
    fun '(mkdecl an db ty) s t =>
    match db with
    | Some db => kp_tLetIn an db ty s (fun x => t [x] [] [])
    | None =>
        let* id_arg s <- kp_tProd an ty (Some "args") s in
        let red_ty := reduce_except_lets E s (get_one_type id_arg s) in
        match make_cparam_call make_Ind kname Ep id_inds
                id_uparams id_preds id_uparams_preds [] [] id_arg
                red_ty s with
        | Some (ty, _) => mk_tProd (mkBindAnn nAnon Relevant) ty (Some "rec_call") s
                            (fun id_rec => t [] [id_arg] [id_rec])
        | None => t [] [id_arg] [] s
        end
    end.


  (* 2.2.2 Build the type of the custom param of a constructor *)
  Definition mk_ty_cparam : nat -> constructor_body -> state -> term :=
    fun pos_ctor ctor s =>
    let* _ id_args _ s <- fold_left_state_opt3 (fun _ => make_type_arg) ctor.(cstr_args) s in
    (* ind_params1 A0 PA ... B0 ... Bn i0 ... im (cst A0 ... B0 ) *)
    let id_ind := get_id1 id_inds pos_indb in
    mkApp (mkApps (get_term_pos id_ind s)
                  (get_term id_uparams_preds s ++ get_term id_nuparams s
                    ++ get_ctor_indices kname pos_indb pos_ctor s))
          (mkApps (make_cst kname pos_indb pos_ctor id_uparams id_nuparams s)
                  (get_term id_args s)).



  (* 2.3 Compute custom param of the inductive block *)
  #[using="id_preds"] Definition mk_ind : one_inductive_body -> state -> one_inductive_entry :=
    fun indb s =>
    {| mind_entry_typename := indb.(ind_name) ^ "_cparam" ;
      mind_entry_arity := make_type_ind s;
      mind_entry_consnames := map (fun ctor => ctor.(cstr_name) ^ "_cparam") indb.(ind_ctors);
      mind_entry_lc := mapi (fun x y => mk_ty_cparam x y s) indb.(ind_ctors);
    |}.

End MkInd.


(* 3. Compute the custom parametricty  *)
Definition custom_param : mutual_inductive_entry :=
  (* add inds to state *)
  let s := add_mdecl kname nb_uparams mdecl init_state in
  (* 1. add inds *)
  let ' (id_inds, s) := replace_ind kname s in
  (* 2. add uparams + extra predicate *)
  let* id_uparams id_preds id_uparams_preds s <- add_uparams (combine (rev (get_uparams kname s)) strpos_uparams) s in
  (* 3. add nuparams *)
  let ' (id_nuparams, id_cxt_nuparams) := fresh_id_context (Some "nuparams") s (get_nuparams kname s) in
  let s := add_old_context id_cxt_nuparams s in
  (* get params *)
  let params_preds := map state_def (firstn (length id_uparams_preds + length id_nuparams) s.(state_context)) in
  mk_entry params_preds
  (mapi (fun x y => mk_ind id_inds id_uparams id_preds id_uparams_preds id_nuparams x y s)
        mdecl.(ind_bodies)).

End CustomParam.