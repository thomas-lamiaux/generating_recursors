From RecAPI Require Import api_debruijn.

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

Definition make_ind' : kername -> nat -> list ident -> list term -> list term -> state -> term :=
  fun kname pos_indb id_uparams nuparams indices s =>
  mkApps (tInd (mkInd kname pos_indb) [])
          ( get_terms id_uparams s ++ nuparams ++ indices).


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

Definition sub : list ident -> list term -> state -> list term :=
  fun ids rp s => replace_list (map (fun x => get_pos x s) ids) rp (triv_subst s).


(* 2. Generates rec call for inductive *)
Unset Guard Checking.

Section MkRecCall.

(* Context (make_indp : nat -> list ident -> list term -> list term -> state -> term). *)
Context (kname : kername).
Context (Ep : param_env).
Context (id_uparams    : list ident).
Context (id_spuparams  : list ident).
Context (id_uparam_bis : list ident).
Context (id_funcs      : list ident).
Context (id_fixs       : list ident).

Definition sub_bis s := sub id_uparams (get_terms id_uparam_bis s) s.

Fixpoint add_param (strpos : list bool) (l : list term) (rc : list term) (s : state) : list term :=
  match strpos, l, rc with
  | nil, nil, nil => nil
  | true :: strpos, A::l, tm :: rc => A :: (subst0 (sub_bis s) A) :: tm :: (add_param strpos l rc s)
  | false :: strpos, A::l, x :: rc => A :: (add_param strpos l rc s)
  | _, _, _ => nil
end.

Fixpoint make_func_call_aux (id_arg : ident) (rev_ids_local : list ident) (ty : term) (s : state) {struct ty} : term :=
  let (hd, iargs) := decompose_app ty in
  match hd with
  (* 1. If it is an iterated product or LetIn => accumulates arg  *)
  | tProd an A B =>
      let* id_local s := add_old_var (Some "local_arg") (mkdecl an None A) s in
      let tm := make_func_call_aux id_arg (id_local :: rev_ids_local) B s in
      tLambda an A tm
  | tLetIn an db A B =>
      let* _ s := add_old_var (Some "local_let") (mkdecl an (Some db) A) s in
      let tm := make_func_call_aux id_arg rev_ids_local B s in
      tLetIn an db A tm
  (* 2. If it an strictly postive uniform parameter *)
  | tRel n =>
      match find_bool (fun id => check_pos id n s) id_spuparams with
      | (pos_func, true) =>
            mkApp (geti_term id_funcs pos_func s)
                  (mkApps (get_term id_arg s)
                          (get_terms (rev rev_ids_local) s))
      | (pos_param, false) => mkApps (get_term id_arg s) (get_terms (rev rev_ids_local) s)
      end
  (* 3. If it is an inductive *)
  | tInd (mkInd kname_indb pos_indb) _ =>
    if eqb kname kname_indb
    (* 3.1 It it is the inductive type *)
    then let nuparams_indices := skipn (get_nb_uparams kname s) iargs in
         let nuparams := firstn (get_nb_nuparams kname s) nuparams_indices in
         let indices  := skipn  (get_nb_nuparams kname s) nuparams_indices in
          mkApp (mkApps (geti_term id_fixs pos_indb s) (nuparams ++ indices))
                (mkApps (get_term id_arg s)
                        (get_terms (rev rev_ids_local) s))
    (* 3.2 If it is nested *)
    else if length iargs =? 0
    then mkApps (get_term id_arg s) (get_terms (rev rev_ids_local) s)
    else match find (fun x => eq_constant kname_indb x.(ep_kname)) Ep with
      | Some xp =>
        (* 3.2.1 get uparams and nuparams + indices *)
        let uparams_indb := firstn xp.(ep_nb_uparams) iargs in
        let nuparams_indices_indb := skipn xp.(ep_nb_uparams) iargs in
        (* 3.2.2 Check for further rec call recursively *)
        let compute_nested_rc (x : term) (s s : state) : term :=
          let anx := mkBindAnn nAnon Relevant in
          let* id_farg s := add_fresh_var (Some "rec_arg") (mkdecl anx None x) s in
          let tm := make_func_call_aux id_farg [] (lift0 1 x) s in
          tLambda anx x tm
        in
        let rec_call := map (fun x => compute_nested_rc x s s) uparams_indb in
        let ltm := add_param xp.(ep_strpos_uparams) uparams_indb rec_call s in
        (* mkApp (state_to_term s) (mkApps (tVar "Subst: ") (sub_bis s)) *)
        mkApp (mkApps (tConst xp.(ep_func_kname) [])
                      (ltm ++ nuparams_indices_indb))
              (mkApps (get_term id_arg s)
                      (get_terms (rev rev_ids_local) s))
          (* Otherwise, kill the branch *)
      | None => mkApps (get_term id_arg s) (get_terms (rev rev_ids_local) s)
      end
  (* 4. Otherwise *)
  | _ => mkApps (get_term id_arg s) (get_terms (rev rev_ids_local) s)
  end.

#[using="All"]
Definition make_func_call : ident -> term -> state -> term :=
  fun id_arg ty s => make_func_call_aux id_arg [] ty s.

End MkRecCall.