From NamedAPI Require Import api_debruijn.

(*
1. Instiates Parametricity with rec call
2. Generates rec call for inductive

*)

Definition make_ind' : state -> kername -> nat -> keys -> list term -> list term -> term :=
  fun s kname pos_indb key_uparams nuparams indices =>
  mkApps (tInd (mkInd kname pos_indb) [])
          (get_terms s key_uparams ++ nuparams ++ indices).


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


(* 2. Generates rec call for inductive *)
Unset Guard Checking.

Section MkRecCall.

(* Context (make_indp : nat -> keys -> list term -> list term -> state -> term). *)
Context (kname : kername).
Context (Ep : param_env).
Context (s : state).
Context (key_uparams    : keys).
Context (key_spuparams  : keys).
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

Fixpoint make_func_call_aux (s : state) (key_arg : key) (ty : term) {struct ty} : term :=
  match view_strpos_args s kname Ep key_uparams ty with
  | StrposArgIsUparam pos_strpos_uparams loc =>
      let* s _ key_locals _ := it_kp_binder tLambda s (Some "locals") loc in
      mkApp (geti_term s key_funcs pos_strpos_uparams)
            (mkApps (get_term s key_arg) (get_terms s key_locals))
  | StrposArgIsInd pos_indb loc local_nuparams local_indices =>
      let* s _ key_locals _ := it_kp_binder tLambda s (Some "locals") loc in
      mkApp (mkApps (geti_term s key_fixs pos_indb) (local_nuparams ++ local_indices))
            (mkApps (get_term  s key_arg) (get_terms s key_locals))
  | StrposArgIsNested xp pos_indb loc local_uparams local_nuparams_indices =>
      let compute_nested_rc (x : term) (s s : state) : term :=
        let* s key_farg := mk_tLambda s (Some "rec_arg") (mkBindAnn nAnon Relevant) x in
        make_func_call_aux s key_farg (lift0 1 x)
      in
      let* s _ key_locals _ := it_kp_binder tLambda s (Some "locals") loc in
      let rec_call := map (fun x => compute_nested_rc x s s) local_uparams in
      let ltm := add_param s xp.(ep_strpos_uparams) local_uparams rec_call in
          mkApp (mkApps (tConst xp.(ep_func_kname) []) (ltm ++ local_nuparams_indices))
                (mkApps (get_term  s key_arg) (get_terms s key_locals))
  | StrposArgIsFree loc m =>
      let* s _ key_locals _ := it_kp_binder tLambda s (Some "locals") loc in
      mkApps (get_term  s key_arg) (get_terms s key_locals)
  end.

#[using="All"]
Definition make_func_call : key -> term -> term :=
  fun key_arg ty => make_func_call_aux s key_arg ty.

End MkRecCall.