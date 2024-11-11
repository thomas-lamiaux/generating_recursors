From NamedAPI Require Import api_debruijn.
From NamedAPI Require Import commons.

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
Context (Ep : param_env).
Context (s : state).
Context (key_preds : keys).
Context (key_fixs  : keys).


Fixpoint make_rec_call_aux (s : state) (key_arg : key) (rev_ids_local : keys) (ty : term) {struct ty} : option (term * term) :=
  let (hd, iargs) := decompose_app ty in
  match hd with
  (* 1. If it is an iterated product or LetIn => accumulates arg  *)
  | tProd an A B =>
      let* s key_local := add_old_var s (Some "local_arg") an A in
      match make_rec_call_aux s key_arg (key_local :: rev_ids_local) B with
      | Some (ty, tm) => Some (tProd an A ty, tLambda an A tm)
      | None => None
      end
  | tLetIn an db A B =>
      let* s _ := add_old_letin s (Some "local_let") an db A in
      match make_rec_call_aux s key_arg rev_ids_local B with
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
      Some  (mkApp (make_pred s key_preds pos_indb nuparams indices)
                   (mkApps (get_term s key_arg)
                           (get_terms s (rev rev_ids_local))),
            (* Fi  B0 ... Bm i0 ... il (x a0 ... an) *)
            mkApp (mkApps (geti_term s key_fixs pos_indb) (nuparams ++ indices))
                  (mkApps (get_term s key_arg)
                          (get_terms s (rev rev_ids_local))))
    (* 2.2 If it is nested *)
    else if length iargs =? 0 then None
    else match find (fun x => eq_constant kname_indb x.(ep_kname)) Ep with
      | Some xp =>
        (* 2.2.1 get uparams and nuparams + indices *)
        let uparams_indb := firstn xp.(ep_nb_uparams) iargs in
        let nuparams_indices_indb := skipn xp.(ep_nb_uparams) iargs in
        (* 2.2.2 Check for further rec call recursively *)
        let compute_nested_rc (s : state) (x : term) : (option (term * term)) :=
          let anx := mkBindAnn nAnon Relevant in
          let* s key_farg := add_fresh_var s (Some "rec_arg") anx x in
          match make_rec_call_aux s key_farg [] (lift0 1 x) with
          | Some (ty, tm) => Some (tLambda anx x ty, tLambda anx x tm)
          | None => None
          end
        in
        let rec_call := map (fun x => compute_nested_rc s x) uparams_indb in
        if existsb isSome rec_call
          (* If some instatiate the parametricty  *)
        then let (lty, ltm) := add_param xp.(ep_strpos_uparams) uparams_indb rec_call in
            Some (mkApp (mkApps (tInd (mkInd xp.(ep_cparam_kname) pos_indb) [])
                                (lty ++ nuparams_indices_indb))
                        (mkApps (get_term  s key_arg)
                                (get_terms s (rev rev_ids_local))),
                  mkApp (mkApps (tConst xp.(ep_fdt_kname) [])
                                (ltm ++ nuparams_indices_indb))
                        (mkApps (get_term  s key_arg)
                                (get_terms s (rev rev_ids_local))))
          (* Otherwise, kill the branch *)
        else None
      | None => None
      end
  (* 3. Otherwise *)
  | _ => None
  end.

#[using="All"]
Definition make_rec_call : key -> term -> option (term * term) :=
  fun key_arg ty => make_rec_call_aux s key_arg [] ty.

End MkRecCall.