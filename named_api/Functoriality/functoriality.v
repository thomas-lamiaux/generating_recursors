From NamedAPI Require Import api_debruijn.

Unset Guard Checking.


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
  (* returns uparams, uparams_bis, functions *)
  Definition closure_uparams_func : state -> kername ->
      (state -> keys -> keys -> keys -> term) -> term :=
    fun s kname =>
    closure_by_uparam binder 3 s kname (
      fun s i key_uparam cc =>
      if (negb (nth i strpos_uparams false))
      then cc s [key_uparam] [key_uparam] [] else
      (* If it is strictlity positive *)
      (* 1. Add a new parameter A_bis *)
      let new_name := name_map (fun x => x ^ "_bis") (get_name s key_uparam) in
      let* s key_uparam_bis := mk_binder binder s (Some "uparam_bis")
            (mkBindAnn new_name Relevant) (get_type s key_uparam) in
      (* 2. Add a function fA : A -> A_bis *)
      let nameP := name_map (fun x => ("f" ^ x)) (get_name s key_uparam) in
      let ty_func := (let* s _ := mk_tProd s None (mkBindAnn nAnon Relevant)
                                    (get_term s key_uparam) in
                      (get_term s key_uparam_bis)) in
      let* s key_func := mk_binder binder s (Some "func") (mkBindAnn nameP Relevant) ty_func in
      cc s [key_uparam] [key_uparam_bis] [key_func]
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
  let* s := subst_ind s kname in
  let* s key_uparams key_uparams_bis _ := closure_uparams_func tProd s kname in
  make_return_type s key_uparams key_uparams_bis pos_indb.



  (* ############################## *)
  (*     3. Compute the Rec Call    *)
  (* ############################## *)


(* 1. Instiates Parametricity with rec call *)


Definition triv_subst : state -> list term :=
  fun s => mapi (fun i _ => tRel i) s.(state_context).

Fixpoint one_replace_list {A} (pos : nat) (a : A) (l : list A) : list A :=
  match pos, l with
  | 0, x::l => a::l
  | S n, x::l => x :: (one_replace_list n a l)
  | _, _ => l
  end.

Definition replace_list {A} (lpos : list nat) (la : list A) (l : list A) : list A :=
  fold_right (fun ' (pos, a) t => one_replace_list pos a t) l (combine lpos la).

Definition sub : state -> keys -> list term -> list term :=
  fun s ks rp => replace_list (map (fun x => get_pos s x) ks) rp (triv_subst s).


Section MkRecCall.

Context (s : state).
Context (key_uparams    : keys).
Context (key_strpos_uparams  : keys).
Context (key_uparam_bis : keys).
Context (key_funcs      : keys).
Context (key_fixs       : keys).

Definition sub_bis s := sub s key_uparams (get_terms s key_uparam_bis).

Fixpoint add_param (s : state) (strpos : list bool) (l : list term) (rc : list term) : list term :=
  match strpos, l, rc with
  | nil, nil, nil => nil
  | true :: strpos, A::l, tm :: rc => A :: (subst0 (sub_bis s) A) :: tm :: (add_param s strpos l rc)
  | false :: strpos, A::l, x :: rc => A :: (add_param s strpos l rc)
  | _, _, _ => nil
end.

Fixpoint make_func_call (s : state) (key_arg : key) (ty : term) {struct ty} : term :=
  match view_uparams_args s kname Ep [] key_uparams strpos_uparams ty with
  | SPArgIsSPUparam pos_uparams loc iargs =>
      let* s _ key_locals _ := closure_context_sep tLambda s (Some "locals") loc in
      mkApp (geti_term s key_funcs pos_uparams)
            (mkApps (get_term s key_arg) (get_terms s key_locals))
  | SPArgIsInd pos_indb loc local_nuparams local_indices =>
      let* s _ key_locals _ := closure_context_sep tLambda s (Some "locals") loc in
      mkApp (mkApps (geti_term s key_fixs pos_indb) (local_nuparams ++ local_indices))
            (mkApps (get_term  s key_arg) (get_terms s key_locals))
  | SPArgIsNested xp pos_indb loc local_uparams local_nuparams_indices =>
      let compute_nested_rc (x : term) (s s : state) : term :=
        let* s key_farg := mk_tLambda s (Some "rec_arg") (mkBindAnn nAnon Relevant) x in
        make_func_call s key_farg (lift0 1 x)
      in
      let* s _ key_locals _ := closure_context_sep tLambda s (Some "locals") loc in
      let rec_call := map (fun x => compute_nested_rc x s s) local_uparams in
      let ltm := add_param s xp.(ep_strpos_uparams) local_uparams rec_call in
          mkApp (mkApps (tConst xp.(ep_func_kname) []) (ltm ++ local_nuparams_indices))
                (mkApps (get_term  s key_arg) (get_terms s key_locals))
  | SPArgIsFree loc m iargs =>
      let* s _ key_locals _ := closure_context_sep tLambda s (Some "locals") loc in
      mkApps (get_term s key_arg) (get_terms s key_locals)
  end.

Definition compute_args_fix : keys -> list term :=
  map (fun key_arg => let red_ty := reduce_full E s (get_type s key_arg) in
                      make_func_call s key_arg red_ty ).

End MkRecCall.



(* ##################################### *)
(*    3. Make the functoriality lemma    *)
(* ##################################### *)


Definition gen_functoriality_term (pos_indb : nat) : term :=
  (* add inds and its param to state *)
  let s := add_mdecl kname nb_uparams mdecl init_state in
  let annoted_uparams := combine (rev (get_uparams s kname)) strpos_uparams in
  let* s := subst_ind s kname in
  (* 1. add uparams + uparam_bis + functions A -> A_bis *)
  let* s key_uparams key_uparams_bis key_funcs := closure_uparams_func tLambda s kname in
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
          (compute_args_fix s key_uparams key_uparams_bis key_funcs key_fixs key_args)).


End Functoriality.

