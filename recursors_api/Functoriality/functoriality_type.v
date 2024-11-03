From RecAPI Require Import api_debruijn.

Section FuncType.

  Context (kname : kername).
  Context (mdecl : mutual_inductive_body).
  Context (nb_uparams : nat).
  Context (strpos_uparams : list bool).
  Context (E : global_env).
  Context (Ep : param_env).

Definition closure_uparams_func binder : (list (context_decl * bool)) -> state ->
    (list ident -> list ident -> state -> term) -> term :=
  fold_right_state_opt2
    (fun _ ' (mkdecl an db ty, b) s t =>
      (* add old_param *)
      let* id_uparam s := kp_binder binder an ty (Some "uparams") s in
      (* add a function *)
      match b with
      | false => t [id_uparam] [id_uparam] s
      | true =>
          (* add new type *)
          let new_name := name_map (fun x => x ^ "_bis") an.(binder_name) in
          let* id_uparam_bis s := mk_binder binder (mkBindAnn new_name Relevant) (get_type id_uparam s) (Some "uparam'") s in
          (* add pred *)
          let nameP := name_map (fun x => ("f" ^ x)) an.(binder_name) in
          let ty_func := (let* _ s := mk_binder binder (mkBindAnn nAnon Relevant)
                                    (get_term id_uparam s) None s in
                          (get_term id_uparam_bis s)) in
          let* id_func s := mk_binder binder (mkBindAnn nameP Relevant) ty_func (Some "func") s in
          t [id_uparam] [id_uparam_bis] s
      end
    ).


  (* 2. Return type *)
  Section mkReturnType.

  Context (id_uparams : list ident).
  Context (id_uparams_bis : list ident).

  (* forall A0 A0' (A0 -> A0') ...,
     forall B0 ... i ..., Ind A0 .. -> Ind A0' *)
  Definition make_return_type : nat -> state -> term :=
    fun pos_indb s =>
    let* id_nuparams s := closure_nuparams tProd kname s in
    let* id_indices  s := closure_indices  tProd kname pos_indb s in
    let* id_VarMatch  s := mk_tProd (mkBindAnn nAnon Relevant)
              (make_ind kname pos_indb id_uparams id_nuparams id_indices s) None s in
    (make_ind kname pos_indb id_uparams_bis id_nuparams id_indices s).

  End mkReturnType.

(* 3. Compute the type of the functorality *)
Definition func_type (pos_indb : nat) : term :=
  (* add inds to state *)
  let s := add_mdecl kname nb_uparams mdecl init_state in
  let annoted_uparams := combine (rev (get_uparams kname s)) strpos_uparams in
  let* s := replace_ind kname s in
  (* 2. add uparams + extra predicate *)
  let* id_uparams id_uparams_bis s := closure_uparams_func tProd annoted_uparams s in
  make_return_type id_uparams id_uparams_bis pos_indb s.


End FuncType.