From RecAPI Require Import api_debruijn.
From RecAPI Require Import commons.
From RecAPI Require Import preprocess_strpos_uparams.

(*
1. Instiates Parametricity with rec call
2. Generates rec call for inductive
3. Generates rec call for iterated product

Currently fails if it is nested by a function type like (nat -> RoseTree)
 *)

Unset Guard Checking.

Section GenRec.

Context (pdecl : preprocess_mutual_inductive_body).
Context (E : global_env).
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
      | None => let fT := (tLambda (mkBindAnn nAnon Relevant) A qTrue) in
                let fI := (tLambda (mkBindAnn nAnon Relevant) A qI) in
                (A :: (funTrue A) :: lty, A :: (funTrue A) :: (funI A) :: ltm)
      | Some (ty, tm) => (A::ty::lty, A::ty::tm::ltm)
      end
  | false :: strpos, A::l, x :: rc =>
    let (lty, ltm) := add_param strpos l rc in (A :: lty, A :: ltm)
  | _, _, _ => (nil, nil)
end.


(* 2. Generates rec call for inductive *)
Fixpoint make_rec_pred_ind (ty : term) (e : info) {struct ty} : option (term * term) :=
  let (hd, iargs) := decompose_app ty in
  match hd with
  | tInd (mkInd kname_indb pos_indb) _ =>
    if eqb pdecl.(pmb_kname) kname_indb
    (* 2. Itf it is the inductive type *)
    then let local := skipn pdecl.(pmb_nb_uparams) iargs in
      let nuparams := firstn pdecl.(pmb_nb_nuparams) local in
      let indices  := skipn  pdecl.(pmb_nb_nuparams) local in
      (* Pi B0 ... Bm i0 ... il / Fi  B0 ... Bm i0 ... il *)
      Some (make_pred pos_indb nuparams indices e,
          mkApps (geti_term "F" pos_indb e) (nuparams ++ indices))
    (* 3. If it is nested *)
    else if length iargs =? 0 then None
    else match find (fun x => eq_constant kname_indb x.(ep_kname)) Ep with
      | Some Ep_indb =>
        (* compute strpos uparams *)
        let strpos := preprocess_strpos kname_indb Ep_indb.(ep_body) E in
        let nb_uparams_indb := length strpos in
        (* get uparams and nuparams + indices *)
        let uparams_indb := firstn nb_uparams_indb iargs in
        let nuparams_indices_indb := skipn nb_uparams_indb iargs in
        (* Check if further rec call recursively *)
        let rec_call := map (fun x => make_rec_pred_ind x e) uparams_indb in
        if existsb isSome rec_call
          (* If some instatiate the parametricty  *)
        then let (lty, ltm) := add_param strpos uparams_indb rec_call in
            Some (mkApps (tInd (mkInd Ep_indb.(ep_pkname) pos_indb) []) (lty ++ nuparams_indices_indb),
                  mkApps (tConst Ep_indb.(ep_tkname) []) (ltm ++ nuparams_indices_indb))
          (* Otherwise, kill the branch *)
        else None
      | None => None
      end
  (* 4. Otherwise *)
  | _ => None
  end.

(* 3. Generates rec call for iterated product  *)
Fixpoint make_rec_pred (ty : term) (e : info) {struct ty} : option (term * term) :=
  let (hd, iargs) := decompose_app ty in
  match hd with
  (* If it is an iterated product *)
  | tProd an A B =>
      let e' := add_old_var (Some "local") (mkdecl an None A) e in
      match make_rec_pred B e' with
      | Some (ty, tm) => Some (tProd an A ty, tLambda an A tm)
      | None => None
      end
  | tLetIn an db A B =>
      let e' := add_old_var None (mkdecl an (Some db) A) e in
      match make_rec_pred B e' with
      | Some (ty, tm) => Some (tLetIn an db A ty, tLetIn an db A tm)
      | None => None
      end
  | _ => option_map
          (fun x => let ' (ty, tm) := x in
            (mkApp ty (mkApps (geti_term_rev "args" 0 e) (get_term "local" e)),
             mkApp ty (mkApps (geti_term_rev "args" 0 e) (get_term "local" e))))
          (make_rec_pred_ind (reduce_full E e ty) e)
  end.



End GenRec.