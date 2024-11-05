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

Fixpoint add_param (strpos : list bool) (l : list term) (rc : list (term * term)) : list term :=
  match strpos, l, rc with
  | nil, nil, nil => nil
  | true :: strpos, A::l, (ty_bis, tm) :: rc =>
      A :: ty_bis :: tm :: (add_param strpos l rc)
  | false :: strpos, A::l, x :: rc =>
      A :: (add_param strpos l rc)
  | _, _, _ => nil
end.


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


Fixpoint make_func_call_aux (id_arg : ident) (rev_ids_local : list ident) (ty : term) (sty stm : state) {struct ty} : term * term :=
  let (hd, iargs) := decompose_app ty in
  match hd with
  (* 1. If it is an iterated product or LetIn => accumulates arg  *)
  | tProd an A B =>
      let* id_local sty := add_old_var (Some "local_arg") (mkdecl an None A) sty in
      let* id_local stm := add_old_var (Some "local_arg") (mkdecl an None A) stm in
      let ' (ty_bis, tm) := make_func_call_aux id_arg (id_local :: rev_ids_local) B sty stm in
      (tProd an A ty_bis, tLambda an A tm)
  | tLetIn an db A B =>
      let* _ sty := add_old_var (Some "local_let") (mkdecl an (Some db) A) sty in
      let* _ stm := add_old_var (Some "local_let") (mkdecl an (Some db) A) stm in
      let ' (ty_bis, tm) := make_func_call_aux id_arg rev_ids_local B sty stm in
      (tLetIn an db A ty_bis, tLetIn an db A tm)
  (* 2. If it an strictly postive uniform parameter *)
  | tRel n =>
      match find_bool (fun id => check_pos id n sty) id_uparams with
      | (pos_param, true) =>
        match find_bool (fun id => check_pos id n stm) id_spuparams with
        | (pos_func, true) =>
            ( geti_term id_uparam_bis pos_param sty,
              mkApp (geti_term id_funcs pos_func stm)
                    (mkApps (get_term id_arg stm)
                            (get_terms (rev rev_ids_local) stm)))
        | (pos_param, false) => (ty, (mkApps (get_term id_arg stm) (get_terms (rev rev_ids_local) stm)))
        end
      | (n, false) => (ty, (mkApps (get_term id_arg stm) (get_terms (rev rev_ids_local) stm)))
      end
  (* 3. If it is an inductive *)
  | tInd (mkInd kname_indb pos_indb) _ =>
    if eqb kname kname_indb
    (* 3.1 It it is the inductive type *)
    then let nuparams_indices := skipn (get_nb_uparams kname sty) iargs in
         let nuparams := firstn (get_nb_nuparams kname sty) nuparams_indices in
         let indices  := skipn  (get_nb_nuparams kname sty) nuparams_indices in
         ( make_ind' kname pos_indb id_uparam_bis nuparams indices sty,
           mkApp (mkApps (geti_term id_fixs pos_indb stm) (nuparams ++ indices))
                 (mkApps (get_term id_arg stm)
                         (get_terms (rev rev_ids_local) stm)))
    (* 3.2 If it is nested *)
    else if length iargs =? 0
    then (ty, (mkApps (get_term id_arg stm) (get_terms (rev rev_ids_local) stm)))
    else match find (fun x => eq_constant kname_indb x.(ep_kname)) Ep with
      | Some xp =>
        (* 3.2.1 get uparams and nuparams + indices *)
        let uparams_indb := firstn xp.(ep_nb_uparams) iargs in
        let nuparams_indices_indb := skipn xp.(ep_nb_uparams) iargs in
        (* 3.2.2 Check for further rec call recursively *)
        let compute_nested_rc (x : term) (sty stm : state) : term * term :=
          let anx := mkBindAnn nAnon Relevant in
          let* id_farg stm := add_fresh_var (Some "rec_arg") (mkdecl anx None x) stm in
          let ' (ty_bis, tm) := make_func_call_aux id_farg [] (lift0 1 x) sty stm in
          (ty_bis, tLambda anx x tm)
        in
        let rec_call := map (fun x => compute_nested_rc x sty stm) uparams_indb in
        let ltm := add_param xp.(ep_strpos_uparams) uparams_indb rec_call in
        ( mkApps (tInd (mkInd kname_indb pos_indb) [])
                 (map fst rec_call ++ nuparams_indices_indb),
          mkApp (mkApps (tConst xp.(ep_func_kname) [])
                        (ltm ++ nuparams_indices_indb))
                (mkApps (get_term id_arg stm)
                        (get_terms (rev rev_ids_local) stm)))
          (* Otherwise, kill the branch *)
      | None => (ty, (mkApps (get_term id_arg stm) (get_terms (rev rev_ids_local) stm)))
      end
  (* 4. Otherwise *)
  | _ => (ty, (mkApps (get_term id_arg stm) (get_terms (rev rev_ids_local) stm)))
  end.

#[using="All"]
Definition make_func_call : ident -> term -> state -> term * term :=
  fun id_arg ty s => make_func_call_aux id_arg [] ty s s.

End MkRecCall.