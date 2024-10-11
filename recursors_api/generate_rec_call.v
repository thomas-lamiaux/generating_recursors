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


Fixpoint make_rec_call_aux (id_arg : ident) (rev_ids_local : list ident) (ty : term) (e : info) {struct ty} : option (term * term) :=
  let (hd, iargs) := decompose_app ty in
  match hd with
  (* 1. If it is an iterated product or LetIn => accumulates arg  *)
  | tProd an A B =>
      let id_local := fresh_ident (Some "local") e in
      let e' := add_old_var id_local (mkdecl an None A) e in
      match make_rec_call_aux id_arg (id_local :: rev_ids_local) B e' with
      | Some (ty, tm) => Some (tProd an A ty, tLambda an A tm)
      | None => None
      end
  | tLetIn an db A B =>
      let e' := add_old_var "LET" (mkdecl an (Some db) A) e in
      match make_rec_call_aux id_arg rev_ids_local B e' with
      | Some (ty, tm) => Some (tLetIn an db A ty, tLetIn an db A tm)
      | None => None
      end
  (* 2. If it is an inductive *)
  | tInd (mkInd kname_indb pos_indb) _ =>
    if eqb kname kname_indb
    (* 2.1 It it is the inductive type *)
    then
      let nuparams_indices := skipn (get_nb_uparams kname e) iargs in
      let nuparams := firstn (get_nb_nuparams kname e) nuparams_indices in
      let indices  := skipn  (get_nb_nuparams kname e) nuparams_indices in
            (* Pi B0 ... Bm i0 ... il (x a0 ... an) *)
      Some  (mkApp (make_pred id_preds pos_indb nuparams indices e)
                   ((mkApps (get_one_term id_arg e)
                           (get_term (rev rev_ids_local) e))),
            (* Fi  B0 ... Bm i0 ... il (x a0 ... an) *)
            mkApp (mkApps (get_one_of_term id_fixs pos_indb e) (nuparams ++ indices))
                  (mkApps (get_one_term id_arg e)
                          (get_term (rev rev_ids_local) e)))
    (* 2.2 If it is nested *)
    else if length iargs =? 0 then None
    else match find (fun x => eq_constant kname_indb x.(ep_kname)) Ep with
      | Some xp =>
        (* 2.2.1 get uparams and nuparams + indices *)
        let uparams_indb := firstn xp.(ep_nb_uparams) iargs in
        let nuparams_indices_indb := skipn xp.(ep_nb_uparams) iargs in
        (* 2.2.2 Check for further rec call recursively *)
        let compute_nested_rc (x : term) (e : info) : (option (term * term)) :=
          let anx := mkBindAnn nAnon Relevant in
          let id_farg := fresh_ident (Some "rec_arg") e in
          let e := add_fresh_var id_farg (mkdecl anx None x) e in
          match make_rec_call_aux id_farg [] (lift0 1 x) e with
          | Some (ty, tm) => Some (tLambda anx x ty, tLambda anx x tm)
          | None => None
          end
        in
        let rec_call := map (fun x => compute_nested_rc x e) uparams_indb in
        (* match find isSome rec_call with
        | Some (Some (pty, ptm)) => Some (mkApp (tVar "REC PRED") pty, mkApp (tVar "REC PRED") ptm)
        | _ => None
        end *)
        if existsb isSome rec_call
          (* If some instatiate the parametricty  *)
        then let (lty, ltm) := add_param xp.(ep_strpos_uparams) uparams_indb rec_call in
            Some (mkApp (mkApps (tInd (mkInd xp.(ep_pkname) pos_indb) [])
                                (lty ++ nuparams_indices_indb))
                        (mkApps (get_one_term id_arg e)
                                (get_term (rev rev_ids_local) e)),
                  mkApp (mkApps (tConst xp.(ep_tkname) [])
                                (ltm ++ nuparams_indices_indb))
                        (mkApps (get_one_term id_arg e)
                                (get_term (rev rev_ids_local) e)))
          (* Otherwise, kill the branch *)
        else None
      | None => None
      end
  (* 4. Otherwise *)
  | _ => None
  end.

#[using="All"]
Definition make_rec_call : ident -> term -> info -> option (term * term) :=
  fun id_arg ty e => make_rec_call_aux id_arg [] ty e.

End MkRecCall.