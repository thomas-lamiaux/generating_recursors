From RecAPI Require Import api_debruijn.
From RecAPI Require Import commons.

(*
1. Instiates Parametricity with rec call
2. Generates rec call for inductive

*)

Unset Guard Checking.

Section GenRec.

Context (pdecl : preprocess_mutual_inductive_body).
Context (Ep : env_param).

MetaCoq Quote Definition qTrue := True.

Definition funTrue : term -> term :=
  fun ty => tLambda (mkBindAnn nAnon Relevant) ty qTrue.

MetaCoq Quote Definition qI := I.

Definition funI : term -> term :=
  fun ty => tLambda (mkBindAnn nAnon Relevant) ty qI.


(* 1. Instiates Parametricity with rec call *)
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
(* Fixpoint make_rec_pred_ind (ty : term) (e : info) {struct ty} : option (term * term) := *)
Definition local : nat -> string :=
  fun n => (String.append "local_" (string_of_nat n)).


Fixpoint make_rec_pred_aux (ty : term) (e : info) (d : nat) {struct ty} : option (term * term) :=
  let (hd, iargs) := decompose_app ty in
  match hd with
  (* 1. If it is an iterated product or LetIn => accumulates arg  *)
  | tProd an A B =>
      let e' := add_old_var (Some (local d)) (mkdecl an None A) e in
      match make_rec_pred_aux B e' d with
      | Some (ty, tm) => Some (tProd an A ty, tLambda an A tm)
      | None => None
      end
  | tLetIn an db A B =>
      let e' := add_old_var None (mkdecl an (Some db) A) e in
      match make_rec_pred_aux B e' d with
      | Some (ty, tm) => Some (tLetIn an db A ty, tLetIn an db A tm)
      | None => None
      end
  (* 2. If it is an inductive *)
  | tInd (mkInd kname_indb pos_indb) _ =>
    if eqb pdecl.(pmb_kname) kname_indb
    (* 2.1 It it is the inductive type *)
    then
      let nuparams_indices := skipn pdecl.(pmb_nb_uparams) iargs in
      let nuparams := firstn pdecl.(pmb_nb_nuparams) nuparams_indices in
      let indices  := skipn  pdecl.(pmb_nb_nuparams) nuparams_indices in
            (* Pi B0 ... Bm i0 ... il (x a0 ... an) *)
      Some  (mkApp (make_pred pos_indb nuparams indices e)
                   ((mkApps (geti_term_rev "args" 0 e)
                           (get_term (local d) e))),
            (* Fi  B0 ... Bm i0 ... il (x a0 ... an) *)
            mkApp (mkApps (geti_term "fix" pos_indb e) (nuparams ++ indices))
                  (mkApps (geti_term_rev "args" 0 e)
                          (get_term (local d) e)))
    (* 2.2 If it is nested *)
    else if length iargs =? 0 then None
    else match find (fun x => eq_constant kname_indb x.(ep_kname)) Ep with
      | Some xp =>
        (* 2.2.1 get uparams and nuparams + indices *)
        let uparams_indb := firstn xp.(ep_nb_uparams) iargs in
        let nuparams_indices_indb := skipn xp.(ep_nb_uparams) iargs in
        (* 2.2.2 Check for further rec call recursively *)
        let compute_nested_rc (x : term) (e : info) (d : nat) :=
          let anx := mkBindAnn nAnon Relevant in
          let e := add_fresh_var (Some "args") (mkdecl anx None x) e in
          match make_rec_pred_aux (lift0 1 x) e d with
          | Some (ty, tm) => Some (tLambda anx x ty, tLambda anx x tm)
          | None => None
          end
        in
        let rec_call := map (fun x => compute_nested_rc x e (S d)) uparams_indb in
        if existsb isSome rec_call
          (* If some instatiate the parametricty  *)
        then let (lty, ltm) := add_param xp.(ep_strpos_uparams) uparams_indb rec_call in
            Some (mkApp (mkApps (tInd (mkInd xp.(ep_pkname) pos_indb) [])
                                (lty ++ nuparams_indices_indb))
                        (mkApps (geti_term_rev "args" 0 e)
                                (get_term (local d) e)),
                  mkApp (mkApps (tConst xp.(ep_tkname) [])
                                (ltm ++ nuparams_indices_indb))
                        (mkApps (geti_term_rev "args" 0 e)
                                      (get_term (local d) e)))
          (* Otherwise, kill the branch *)
        else None
      | None => None
      end
  (* 4. Otherwise *)
  | _ => None
  end.

#[using="All"]
Definition make_rec_pred : term -> info -> option (term * term) :=
  fun ty e => make_rec_pred_aux ty e 0.

End GenRec.