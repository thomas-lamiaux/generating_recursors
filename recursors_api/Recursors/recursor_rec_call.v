From RecAPI Require Import api_debruijn.
From RecAPI Require Import commons.

(*
1. Instiates Parametricity with rec call
2. Generates rec call for inductive

*)


(* 1. Instiates Parametricity with rec call *)

MetaCoq Quote Definition qTrue := True.

Definition funTrue : term -> term :=
  fun ty => tLambda (mkBindAnn nAnon Relevant) ty qTrue.

MetaCoq Quote Definition qI := I.

Definition funI : term -> term :=
  fun ty => tLambda (mkBindAnn nAnon Relevant) ty qI.

Fixpoint add_param (strpos : list bool) (l : list term) (rc : list (option (term * term))) : list term * list term :=
  match strpos, l, rc with
  | nil, nil, nil => (nil , nil)
  | true :: strpos, A::l, x :: rc =>
      let (lty, ltm) := add_param strpos l rc in
      match x with
      | None => (A :: (funTrue A) :: lty, A :: (funTrue A) :: (funI A) :: ltm)
      | Some (ty, tm) => (A::ty::lty, A::ty::tm::ltm)
      end
  | false :: strpos, A::l, x :: rc =>
    let (lty, ltm) := add_param strpos l rc in (A :: lty, A :: ltm)
  | _, _, _ => (nil, nil)
end.


(* 2. Generates rec call for inductive *)
Unset Guard Checking.

Section MkRecCall.

Context (kname : kername).
Context (Ep : env_param).
Context (id_preds : list ident).
Context (id_fixs  : list ident).


Fixpoint make_rec_call_aux (id_arg : ident) (rev_ids_local : list ident) (ty : term) (s : state) {struct ty} : option (term * term) :=
  let (hd, iargs) := decompose_app ty in
  match hd with
  (* 1. If it is an iterated product or LetIn => accumulates arg  *)
  | tProd an A B =>
      let* id_local s <- add_old_var (Some "local_arg") (mkdecl an None A) s in
      match make_rec_call_aux id_arg (id_local :: rev_ids_local) B s with
      | Some (ty, tm) => Some (tProd an A ty, tLambda an A tm)
      | None => None
      end
  | tLetIn an db A B =>
      let* _ s <- add_old_var (Some "local_let") (mkdecl an (Some db) A) s in
      match make_rec_call_aux id_arg rev_ids_local B s with
      | Some (ty, tm) => Some (tLetIn an db A ty, tLetIn an db A tm)
      | None => None
      end
  (* 2. If it is an inductive *)
  | tInd (mkInd kname_indb pos_indb) _ =>
    if eqb kname kname_indb
    (* 2.1 It it is the inductive type *)
    then
      let nuparams_indices := skipn (get_nb_uparams kname s) iargs in
      let nuparams := firstn (get_nb_nuparams kname s) nuparams_indices in
      let indices  := skipn  (get_nb_nuparams kname s) nuparams_indices in
            (* Pi B0 ... Bm i0 ... il (x a0 ... an) *)
      Some  (mkApp (make_pred id_preds pos_indb nuparams indices s)
                   (mkApps (get_term id_arg s)
                           (get_terms (rev rev_ids_local) s)),
            (* Fi  B0 ... Bm i0 ... il (x a0 ... an) *)
            mkApp (mkApps (geti_term id_fixs pos_indb s) (nuparams ++ indices))
                  (mkApps (get_term id_arg s)
                          (get_terms (rev rev_ids_local) s)))
    (* 2.2 If it is nested *)
    else if length iargs =? 0 then None
    else match find (fun x => eq_constant kname_indb x.(ep_kname)) Ep with
      | Some xp =>
        (* 2.2.1 get uparams and nuparams + indices *)
        let uparams_indb := firstn xp.(ep_nb_uparams) iargs in
        let nuparams_indices_indb := skipn xp.(ep_nb_uparams) iargs in
        (* 2.2.2 Check for further rec call recursively *)
        let compute_nested_rc (x : term) (e : state) : (option (term * term)) :=
          let anx := mkBindAnn nAnon Relevant in
          let* id_farg s <- add_fresh_var (Some "rec_arg") (mkdecl anx None x) s in
          match make_rec_call_aux id_farg [] (lift0 1 x) s with
          | Some (ty, tm) => Some (tLambda anx x ty, tLambda anx x tm)
          | None => None
          end
        in
        let rec_call := map (fun x => compute_nested_rc x s) uparams_indb in
        if existsb isSome rec_call
          (* If some instatiate the parametricty  *)
        then let (lty, ltm) := add_param xp.(ep_strpos_uparams) uparams_indb rec_call in
            Some (mkApp (mkApps (tInd (mkInd xp.(ep_pkname) pos_indb) [])
                                (lty ++ nuparams_indices_indb))
                        (mkApps (get_term id_arg s)
                                (get_terms (rev rev_ids_local) s)),
                  mkApp (mkApps (tConst xp.(ep_tkname) [])
                                (ltm ++ nuparams_indices_indb))
                        (mkApps (get_term id_arg s)
                                (get_terms (rev rev_ids_local) s)))
          (* Otherwise, kill the branch *)
        else None
      | None => None
      end
  (* 3. Otherwise *)
  | _ => None
  end.

#[using="All"]
Definition make_rec_call : ident -> term -> state -> option (term * term) :=
  fun id_arg ty s => make_rec_call_aux id_arg [] ty s.

End MkRecCall.