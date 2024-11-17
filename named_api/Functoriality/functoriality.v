From NamedAPI Require Import api_debruijn.
From NamedAPI Require Import functoriality_rec_call.

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
  Definition closure_uparams_func : state -> (list (context_decl * bool)) ->
      (state -> keys -> keys -> keys -> keys -> term) -> term :=
    fun s x => fold_right_state_opt 4 s x
      (fun s _ ' (mkdecl an db ty, b) cc =>
        (* add old_param *)
        let* s key_uparam := kp_binder binder s (Some "uparams") an ty in
        (* add a function *)
        match b with
        | false => cc s [key_uparam] [] [key_uparam] []
        | true =>
            (* add new type *)
            let new_name := name_map (fun x => x ^ "_bis") an.(binder_name) in
            let* s key_uparam_bis := mk_binder binder s (Some "uparam_bis")
                  (mkBindAnn new_name Relevant) (get_type s key_uparam) in
            (* add pred *)
            let nameP := name_map (fun x => ("f" ^ x)) an.(binder_name) in
            let ty_func := (let* s _ := mk_tProd s None (mkBindAnn nAnon Relevant)
                                            (get_term s key_uparam) in
                                        (get_term s key_uparam_bis)) in
            let* s key_func := mk_binder binder s (Some "func") (mkBindAnn nameP Relevant) ty_func in
            cc s [key_uparam] [key_uparam] [key_uparam_bis] [key_func]
        end
      ).


  (* 1.2 Make return types *)
  Section mkReturnType.

  Context (s : state).
  Context (key_uparams     : keys).
  Context (key_uparams_bis : keys).
  Context (pos_indb : nat).

  (* Ind A0' .. *)
  Definition make_ccl : state -> keys -> keys -> key -> term :=
    fun s key_nuparams key_indices key_VarMatch =>
    make_ind s kname pos_indb key_uparams_bis key_nuparams key_indices.

  (* forall A0 A0' (A0 -> A0') ...,
     forall B0 ... i ..., Ind A0 .. -> Ind A0' .. *)
  Definition make_return_type : term :=
    let* s key_nuparams := closure_nuparams tProd s kname in
    let* s key_indices  := closure_indices  tProd s kname pos_indb in
    let* s key_VarMatch := mk_tProd s None (mkBindAnn nAnon Relevant)
                (make_ind s kname pos_indb key_uparams key_nuparams key_indices) in
    make_ccl s key_nuparams key_indices key_VarMatch.

  End mkReturnType.

End GenTypes.



(* ################################################# *)
(*    2. Make the type of the functoriality lemma    *)
(* ################################################# *)

Definition gen_functoriality_type (pos_indb : nat) : term :=
  (* add inds to state *)
  let s := add_mdecl kname nb_uparams mdecl init_state in
  let annoted_uparams := combine (rev (get_uparams s kname)) strpos_uparams in
  let* s := subst_ind s kname in
  (* 1. add uparams + extra predicate *)
  let* s key_uparams _ key_uparams_bis _ := closure_uparams_func tProd s annoted_uparams in
  (* 2. conclusion *)
  make_return_type s key_uparams key_uparams_bis pos_indb.


(* ##################################### *)
(*    3. Make the functoriality lemma    *)
(* ##################################### *)

Section GetRecCall.

  Context (s : state).
  Context (key_uparams     : keys).
  Context (key_spuparams   : keys).
  Context (key_uparams_bis : keys).
  Context (key_funcs       : keys).
  Context (key_fixs        : keys).

  Definition compute_args_fix : keys -> list term :=
    fold_right (fun key_arg c =>
      let red_ty := reduce_full E s (get_type s key_arg) in
      let rc_tm := make_func_call kname Ep s key_uparams key_spuparams
                      key_uparams_bis key_funcs key_fixs key_arg red_ty in
      rc_tm :: c
    ) [].

End GetRecCall.

(*  *)
Definition gen_functoriality_term (pos_indb : nat) : term :=
  (* add inds and its param to state *)
  let s := add_mdecl kname nb_uparams mdecl init_state in
  let annoted_uparams := combine (rev (get_uparams s kname)) strpos_uparams in
  let* s := subst_ind s kname in
  (* 1. add uparams + uparam_bis + functions A -> A_bis *)
  let* s key_uparams key_spuparams key_uparams_bis key_funcs :=
          closure_uparams_func tLambda s annoted_uparams in
  (* 2. fixpoint *)
  let tFix_type pos_indb := make_return_type s key_uparams key_uparams_bis pos_indb in
  let tFix_rarg := tFix_default_rarg s kname in
  let* s key_fixs pos_indb := mk_tFix kname tFix_type tFix_rarg s pos_indb in
  (* 3. closure nuparams + indices + var match *)
  let* s key_nuparams := closure_nuparams tLambda s kname in
  let* s key_indices  := closure_indices  tLambda s kname pos_indb in
  let* s key_VarMatch := mk_tLambda s (Some "VarMatch") (mkBindAnn (nNamed "x") (get_relevance s kname pos_indb))
                        (make_ind s kname pos_indb key_uparams key_nuparams key_indices) in
  (* 4. match VarMatch *)
  let tCase_pred s := make_ccl key_uparams_bis pos_indb s key_nuparams in
  let* s _ key_args _ pos_ctor := mk_tCase kname pos_indb tCase_pred
                            key_uparams key_nuparams s (get_term s key_VarMatch) in
  (* 5. Conclude *)
  (mkApps (make_cst s kname pos_indb pos_ctor key_uparams_bis key_nuparams)
          (compute_args_fix s key_uparams key_spuparams key_uparams_bis key_funcs
            key_fixs key_args)).


End Functoriality.