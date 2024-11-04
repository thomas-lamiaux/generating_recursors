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


(* 1. Instiates Parametricity with rec call *)

Fixpoint add_param (strpos : list bool) (l : list term) (rc : list (option (term * term))) : list term * list term :=
  match strpos, l, rc with
  | nil, nil, nil => (nil , nil)
  | true :: strpos, A::l, x :: rc =>
      let (lty, ltm) := add_param strpos l rc in
      match x with
      | None => (A :: lty, A :: ltm)
      | Some (ty, tm) => (A::ty::lty, A::ty::tm::ltm)
      end
  | false :: strpos, A::l, x :: rc =>
    let (lty, ltm) := add_param strpos l rc in (A :: lty, A :: ltm)
  | _, _, _ => (nil, nil)
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


Fixpoint make_func_call_aux (id_arg : ident) (rev_ids_local : list ident) (ty : term) (s : state) {struct ty} : term * term * term :=
  let (hd, iargs) := decompose_app ty in
  match hd with
  (* 1. If it is an iterated product or LetIn => accumulates arg  *)
  | tProd an A B =>
      let* id_local s := add_old_var (Some "local_arg") (mkdecl an None A) s in
      let ' (ty, ty_bis, tm) := make_func_call_aux id_arg (id_local :: rev_ids_local) B s in
      (tProd an A ty, tProd an A ty, tLambda an A tm)
  | tLetIn an db A B =>
      let* _ s := add_old_var (Some "local_let") (mkdecl an (Some db) A) s in
      let ' (ty, ty_bis, tm) := make_func_call_aux id_arg rev_ids_local B s in
      (tLetIn an db A ty, tLetIn an db A ty_bis, tLetIn an db A tm)
  (* 2. If it an strictly postive uniform parameter *)
  | tRel n =>
      match find_bool (fun id => check_pos id n s) id_spuparams with
      | (n, true) =>
          (tVar "to implement rc", tVar "to implement rc",
                (* mkApp (geti_term id_funcs n s)
                      (mkApps (get_term id_arg s)
                              (get_terms (rev rev_ids_local) s)), *)
                mkApp (geti_term id_funcs n s)
                      (mkApps (get_term id_arg s)
                              (get_terms (rev rev_ids_local) s)))
      | (n, false) => (ty, ty, (mkApps (get_term id_arg s)
                                       (get_terms (rev rev_ids_local) s)))
      end
  (* 3. If it is an inductive *)
  | tInd (mkInd kname_indb pos_indb) _ =>
    if eqb kname kname_indb
    (* 3.1 It it is the inductive type *)
    then
      let nuparams_indices := skipn (get_nb_uparams kname s) iargs in
      let nuparams := firstn (get_nb_nuparams kname s) nuparams_indices in
      let indices  := skipn  (get_nb_nuparams kname s) nuparams_indices in
          (* Ind A0 PA0 ... B0 ... Bm i0 ... il (x a0 ... an) *)
      (* let make_indp pos_indb id_uparams_preds nuparams indices s :=
          mkApp (state_to_term s) (tVar ("value id_uparams_preds := " ^ concat_strings id_uparams_preds)) in *)
        (*
            mkApp (make_indp pos_indb id_uparams_preds nuparams indices s)
                   (mkApps (get_term id_arg s)
                           (get_terms (rev rev_ids_local) s)),*)
            (tVar "to implement rc", tVar "to implement rc",
            (* Fi  B0 ... Bm i0 ... il (x a0 ... an) *)
            mkApp (mkApps (geti_term id_fixs pos_indb s) (nuparams ++ indices))
                  (mkApps (get_term id_arg s)
                          (get_terms (rev rev_ids_local) s)))
    (* 3.2 If it is nested *)
    else (ty, ty, (mkApps (get_term id_arg s)
                          (get_terms (rev rev_ids_local) s)))
    (*
    if length iargs =? 0 then None
    else match find (fun x => eq_constant kname_indb x.(ep_kname)) Ep with
      | Some xp =>
        (* 3.2.1 get uparams and nuparams + indices *)
        let uparams_indb := firstn xp.(ep_nb_uparams) iargs in
        let nuparams_indices_indb := skipn xp.(ep_nb_uparams) iargs in
        (* 3.2.2 Check for further rec call recursively *)
        let compute_nested_rc (x : term) (e : state) : (option (term * term)) :=
          let anx := mkBindAnn nAnon Relevant in
          let* id_farg s := add_fresh_var (Some "rec_arg") (mkdecl anx None x) s in
          match make_func_call_aux id_farg [] (lift0 1 x) s with
          | Some (ty, tm) => Some (tLambda anx x ty, tLambda anx x tm)
          | None => None
          end
        in
        let rec_call := map (fun x => compute_nested_rc x s) uparams_indb in
        if existsb isSome rec_call
          (* If some instatiate the parametricty  *)
          then let (lty, ltm) := add_param xp.(ep_strpos_uparams) uparams_indb rec_call in
            Some (mkApp (mkApps (tInd (mkInd xp.(ep_cparam_kname) pos_indb) [])
                                (lty ++ nuparams_indices_indb))
                        (mkApps (get_term id_arg s)
                                (get_terms (rev rev_ids_local) s)),
                  mkApp (mkApps (tConst xp.(ep_fdt_kname) [])
                                (ltm ++ nuparams_indices_indb))
                        (mkApps (get_term id_arg s)
                                (get_terms (rev rev_ids_local) s)))
          (* Otherwise, kill the branch *)
        else None
      | None => None
      end
      *)
  (* 4. Otherwise *)
  | _ => (ty, ty, (mkApps (get_term id_arg s)
                          (get_terms (rev rev_ids_local) s)))
  end.

#[using="All"]
Definition make_func_call : ident -> term -> state -> term * term * term :=
  fun id_arg ty s => make_func_call_aux id_arg [] ty s.

End MkRecCall.