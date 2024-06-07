From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import All.

Require Import naming.
Require Import commons.


Unset Guard Checking.

Section GenRec.

  Context (kname : kername).
  Context (mdecl : mutual_inductive_body).
  Context (U : term).
  Context (E : env_param).

  Definition params := mdecl.(ind_params).
  Definition nb_params := #|params|.
  Definition relev_out_sort := relev_sort U.

  MetaCoq Quote Definition qTrue := True.
  MetaCoq Quote Definition qI := I.

  Fixpoint add_param (l : list term) (rc : list (option (term * term))) : list term * list term :=
    match l, rc with
    | nil, nil => (nil , nil)
    | A::l, x :: rc =>
      let (lty, ltm) := add_param l rc in
      match x with
      | None => let fT := (tLambda (mkBindAnn nAnon Relevant) A qTrue) in
                let fI := (tLambda (mkBindAnn nAnon Relevant) A qI) in
                (A :: fT :: lty, A :: fT :: fI :: lty)
      | Some (ty, tm) => (A::ty::lty, A::ty::tm::ltm)
      end
    | _, _ => (nil, nil)
  end.

  (* Issues with guard => need WF *)
  Fixpoint rec_pred (ty : term) {struct ty} : option (term * term) :=
    let (hd, iargs) := decompose_app ty in
    match hd with
    | tInd (mkInd s pos_s) _ =>
        if eq_constant kname s
        then let indices := skipn nb_params iargs in
             Some (make_pred pos_s indices,
                  mkApps (tVar (make_name "F" pos_s)) indices)
        else match find (fun x => eq_constant s x.(ep_kname)) E with
        | Some oep =>
             let s_nb_params := oep.(ep_body).(ind_npars) in
             let s_params := firstn s_nb_params iargs in
             let s_indices := skipn s_nb_params iargs in
             let rc := map rec_pred s_params in
             if existsb isSome rc
             then let (lty, ltm) := add_param s_params rc in
             Some (mkApps (tInd (mkInd oep.(ep_pkname) pos_s) []) (lty ++ s_indices),
                   mkApps (tConst oep.(ep_pkname) []) (ltm ++ s_indices))
             else None
        | None => None
        end
    | _ => None
    end.

End GenRec.