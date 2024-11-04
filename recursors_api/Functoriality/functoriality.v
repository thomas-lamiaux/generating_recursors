From RecAPI Require Import api_debruijn.
From RecAPI Require Import functoriality_rec_call.

Section Functoriality.

  Context (kname : kername).
  Context (mdecl : mutual_inductive_body).
  Context (nb_uparams : nat).
  Context (strpos_uparams : list bool).
  Context (E : global_env).
  Context (Ep : param_env).



  (* ################################# *)
  (*    1. Make the different types    *)
  (* ################################# *)

  Section GenTypes.

  Context (binder : aname -> term -> term -> term).

  (* 1. Add uparams + uparams_bis + function A -> A_bis *)
  Definition closure_uparams_func : (list (context_decl * bool)) -> state ->
      (list ident -> list ident -> list ident -> list ident -> state -> term) -> term :=
    fold_right_state_opt4
      (fun _ ' (mkdecl an db ty, b) s t =>
        (* add old_param *)
        let* id_uparam s := kp_binder binder an ty (Some "uparams") s in
        (* add a function *)
        match b with
        | false => t [id_uparam] [] [id_uparam] [] s
        | true =>
            (* add new type *)
            let new_name := name_map (fun x => x ^ "_bis") an.(binder_name) in
            let* id_uparam_bis s := mk_binder binder (mkBindAnn new_name Relevant)
                                    (get_type id_uparam s) (Some "uparam'") s in
            (* add pred *)
            let nameP := name_map (fun x => ("f" ^ x)) an.(binder_name) in
            let ty_func := (let* _ s := mk_tProd (mkBindAnn nAnon Relevant)
                                      (get_term id_uparam s) None s in
                            (get_term id_uparam_bis s)) in
            let* id_func s := mk_binder binder (mkBindAnn nameP Relevant) ty_func (Some "func") s in
            t [id_uparam] [id_uparam] [id_uparam_bis] [id_func] s
        end
      ).


  (* 1.2 Make return types *)
  Section mkReturnType.

  Context (id_uparams : list ident).
  Context (id_uparams_bis : list ident).
  Context (pos_indb : nat).

  (* Ind A0' .. *)
  Definition make_ccl : list ident -> list ident -> ident -> state -> term :=
    fun id_nuparams id_indices id_VarMatch s =>
    make_ind kname pos_indb id_uparams_bis id_nuparams id_indices s.

  (* forall A0 A0' (A0 -> A0') ...,
     forall B0 ... i ..., Ind A0 .. -> Ind A0' .. *)
  Definition make_return_type : state -> term :=
    fun s =>
    let* id_nuparams s := closure_nuparams tProd kname s in
    let* id_indices  s := closure_indices  tProd kname pos_indb s in
    let* id_VarMatch  s := mk_tProd (mkBindAnn nAnon Relevant)
              (make_ind kname pos_indb id_uparams id_nuparams id_indices s) None s in
    make_ccl id_nuparams id_indices id_VarMatch s.

  End mkReturnType.

End GenTypes.



(* ################################################# *)
(*    2. Make the type of the functoriality lemma    *)
(* ################################################# *)

Definition gen_functoriality_type (pos_indb : nat) : term :=
  (* add inds to state *)
  let s := add_mdecl kname nb_uparams mdecl init_state in
  let annoted_uparams := combine (rev (get_uparams kname s)) strpos_uparams in
  let* s := replace_ind kname s in
  (* 1. add uparams + extra predicate *)
  let* id_uparams id_uparams_bis _ _ s := closure_uparams_func tProd annoted_uparams s in
  (* 2. conclusion *)
  make_return_type id_uparams id_uparams_bis pos_indb s.


(* ##################################### *)
(*    3. Make the functoriality lemma    *)
(* ##################################### *)

Section GetRecCall.

  Context (id_uparams     : list ident).
  Context (id_spuparams   : list ident).
  Context (id_uparams_bis : list ident).
  Context (id_funcs       : list ident).
  Context (id_fixs        : list ident).

  Definition compute_args_fix : list ident -> state -> list term :=
    fun id_args s =>
    fold_right (fun id_arg t =>
      let red_ty := reduce_except_lets E s (get_type id_arg s) in
      let ' (_, _, rc_tm) := make_func_call kname Ep id_uparams id_spuparams
                             id_uparams_bis id_funcs id_fixs id_arg red_ty s in
      rc_tm :: t
    ) [] id_args.

End GetRecCall.

(*  *)
Definition gen_functoriality_term (pos_indb : nat) : term :=
  (* add inds and its param to state *)
  let s := add_mdecl kname nb_uparams mdecl init_state in
  let annoted_uparams := combine (rev (get_uparams kname s)) strpos_uparams in
  let* s := replace_ind kname s in
  (* 1. add uparams + uparam_bis + functions A -> A_bis *)
  let* id_uparams id_spuparams id_uparams_bis id_funcs s :=
          closure_uparams_func tLambda annoted_uparams s in
  (* 2. fixpoint *)
  let tFix_type pos_indb := make_return_type id_uparams id_uparams_bis pos_indb s in
  let tFix_rarg := tFix_default_rarg kname s in
  let* id_fixs pos_indb s := mk_tFix kname tFix_type tFix_rarg pos_indb s in
  (* 3. closure nuparams + indices + var match *)
  let* id_nuparams s := closure_nuparams tLambda kname s in
  let* id_indices  s := closure_indices  tLambda kname pos_indb s in
  let* id_VarMatch s := mk_tLambda (mkBindAnn (nNamed "x") (get_relevance kname pos_indb s))
                        (make_ind kname pos_indb id_uparams id_nuparams id_indices s)
                        (Some "VarMatch") s in
  (* 4. match VarMatch *)
  let tCase_pred := make_ccl id_uparams_bis pos_indb id_nuparams in
  let* pos_ctor _ id_args _ s := mk_tCase kname pos_indb tCase_pred
                          id_uparams id_nuparams (get_term id_VarMatch s) s in
  (* 5. Conclude *)
  (mkApps (make_cst kname pos_indb pos_ctor id_uparams_bis id_nuparams s)
          (compute_args_fix id_uparams id_spuparams id_uparams_bis id_funcs
            id_fixs id_args s)).


End Functoriality.