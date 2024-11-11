From NamedAPI Require Import api_debruijn.

(*
1. Instiates Parametricity with rec call
2. Generates rec call for inductive

*)

Definition find_bool {A} (p : A -> bool) (l : list A) : nat * bool :=
let fix aux n l :=
  match l with
  | [] => (n, false)
  | h::t => if p h then (n, true) else aux (S n) t
  end in
  aux 0 l.

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

Fixpoint make_func_call_aux (s : state) (key_arg : key) (rev_ids_local : keys) (ty : term) {struct ty} : term :=
  let (hd, iargs) := decompose_app ty in
  match hd with
  (* 1. If it is an iterated product or LetIn => accumulates arg  *)
  | tProd an A B =>
      let* s key_local := add_old_var s (Some "local_arg") an A in
      let tm := make_func_call_aux s key_arg (key_local :: rev_ids_local) B in
      tLambda an A tm
  | tLetIn an db A B =>
      let* s _ := add_old_letin s (Some "local_let") an db A in
      let tm := make_func_call_aux s key_arg rev_ids_local B in
      tLetIn an db A tm
  (* 2. If it an strictly postive uniform parameter *)
  | tRel n =>
      match find_bool (fun k => check_pos s k n) key_spuparams with
      | (pos_func, true) =>
            mkApp (geti_term s key_funcs pos_func)
                  (mkApps (get_term s key_arg)
                          (get_terms s (rev rev_ids_local)))
      | (pos_param, false) => mkApps (get_term s key_arg) (get_terms s (rev rev_ids_local))
      end
  (* 3. If it is an inductive *)
  | tInd (mkInd kname_indb pos_indb) _ =>
    if eqb kname kname_indb
    (* 3.1 It it is the inductive type *)
    then let nuparams_indices := skipn (get_nb_uparams s kname) iargs in
         let nuparams := firstn (get_nb_nuparams s kname) nuparams_indices in
         let indices  := skipn  (get_nb_nuparams s kname) nuparams_indices in
          mkApp (mkApps (geti_term s key_fixs pos_indb) (nuparams ++ indices))
                (mkApps (get_term  s key_arg)
                        (get_terms s (rev rev_ids_local)))
    (* 3.2 If it is nested *)
    else if length iargs =? 0
    then mkApps (get_term s key_arg) (get_terms s (rev rev_ids_local))
    else match find (fun x => eq_constant kname_indb x.(ep_kname)) Ep with
      | Some xp =>
        (* 3.2.1 get uparams and nuparams + indices *)
        let uparams_indb := firstn xp.(ep_nb_uparams) iargs in
        let nuparams_indices_indb := skipn xp.(ep_nb_uparams) iargs in
        (* 3.2.2 Check for further rec call recursively *)
        let compute_nested_rc (x : term) (s s : state) : term :=
          let anx := mkBindAnn nAnon Relevant in
          let* s key_farg := add_fresh_var s (Some "rec_arg") anx x in
          let tm := make_func_call_aux s key_farg [] (lift0 1 x) in
          tLambda anx x tm
        in
        let rec_call := map (fun x => compute_nested_rc x s s) uparams_indb in
        let ltm := add_param s xp.(ep_strpos_uparams) uparams_indb rec_call in
        (* mkApp (state_to_term s) (mkApps (tVar "Subst: ") (sub_bis s)) *)
        mkApp (mkApps (tConst xp.(ep_func_kname) [])
                      (ltm ++ nuparams_indices_indb))
              (mkApps (get_term  s key_arg)
                      (get_terms s (rev rev_ids_local)))
          (* Otherwise, kill the branch *)
      | None => mkApps (get_term s key_arg) (get_terms s (rev rev_ids_local))
      end
  (* 4. Otherwise *)
  | _ => mkApps (get_term s key_arg) (get_terms s (rev rev_ids_local))
  end.

#[using="All"]
Definition make_func_call : key -> term -> term :=
  fun key_arg ty => make_func_call_aux s key_arg [] ty.

End MkRecCall.