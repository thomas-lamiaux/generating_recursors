From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import All.

Require Import naming.
Require Import commons.


Unset Guard Checking.

Section GenRec.

  Context (kname : kername).
  Context (mdecl : mutual_inductive_body).
  Context (U : term).
  Context (E : list (kername * mutual_inductive_body * kername * kername)).

  Definition params := mdecl.(ind_params).
  Definition nb_params := #|params|.
  Definition relev_out_sort := relev_sort U.

  MetaCoq Quote Definition qTrue := True.
  MetaCoq Quote Definition qI := I.

  Definition isSome {A} (x : option A) : bool :=
    match x with
    | None => false
    | Some _ => true
    end.

  Fixpoint add_param (l : list term) (rc : list (option (term * term))) : list term * list term :=
    match l, rc with
    | nil, nil => (nil , nil)
    | A::l, x :: rc =>
      let (lty, ltm) := add_param l rc in
      match x with
      | None => (A :: (tLambda (mkBindAnn nAnon Relevant) A qTrue) :: lty,
                 A :: (tLambda (mkBindAnn nAnon Relevant) A qI)    :: lty)
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
                  tApp (tVar (make_name "F" pos_s)) indices)
        else match find (fun x => eq_constant s (fst (fst (fst x)))) E with
        | Some (_, s_medcl, kparam1, tparam1) =>
             let s_nb_params := s_medcl.(ind_npars) in
             let s_params := firstn s_nb_params iargs in
             let s_indices := skipn s_nb_params iargs in
             let rc := map rec_pred s_params in
             if existsb isSome rc
             then let (lty, ltm) := add_param s_params rc in
             Some (tApp (tInd (mkInd kparam1 pos_s) []) (lty ++ s_indices),
                   tApp (tConst tparam1 []) (ltm ++ s_indices))
             else None
        | None => None
        end
    | _ => None
    end.

  Definition gen_rec_call (pos_arg : nat) (arg_type : term) (next_closure : term) : term * term :=
    match rec_pred arg_type with
    | Some (P, tmP) =>
      ( tProd (mkBindAnn nAnon relev_out_sort)
              (tApp P [tVar (naming_arg pos_arg)])
              next_closure,
        tLambda (mkBindAnn nAnon relev_out_sort)
                (tApp P [tVar (naming_arg pos_arg)])
                next_closure
      )
    | None => (next_closure, next_closure)
    end.

End GenRec.