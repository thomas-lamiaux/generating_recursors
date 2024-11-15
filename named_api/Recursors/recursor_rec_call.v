From NamedAPI Require Import api_debruijn.
From NamedAPI Require Import commons.

(*
1. Instiates Parametricity with rec call
2. Generates rec call for inductive

*)


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
Unset Guard Checking.

Section MkRecCall.

Context (kname : kername).
Context (Ep : param_env).
Context (s : state).
Context (key_preds : keys).
Context (key_fixs  : keys).

Fixpoint make_rec_call_aux (s : state) (key_arg : key) (ty : term) {struct ty} : option (term * term) :=
  match view_args s kname Ep ty with
  | VargIsFree _ => None
  | VargIsInd pos_indb loc local_nuparams local_indices =>
            (* Pi B0 ... Bm i0 ... il (x a0 ... an) *)
      Some (let* s _ key_locals _ := it_kp_binder tProd s (Some "local") loc in
            mkApp (make_pred s key_preds pos_indb local_nuparams local_indices)
                  (mkApps (get_term s key_arg) (get_terms s key_locals)),
            (* Fi  B0 ... Bm i0 ... il (x a0 ... an) *)
            let* s _ key_locals _ := it_kp_binder tLambda s (Some "local") loc in
            mkApp (mkApps (geti_term s key_fixs pos_indb) (local_nuparams ++ local_indices))
                  (mkApps (get_term s key_arg) (get_terms s key_locals)))
  | VargIsNested xp pos_indb loc local_uparams local_nuparams_indices =>
      let compute_nested_rc (s : state) (x : term) : (option (term * term)) :=
        let anx := mkBindAnn nAnon Relevant in
        let* s key_farg := add_fresh_var s (Some "rec_arg") anx x in
        match make_rec_call_aux s key_farg (lift0 1 x) with
        | Some (ty, tm) => Some (tLambda anx x ty, tLambda anx x tm)
        | None => None
        end
      in
    let* s _ key_locals _ := add_old_context s (Some "local") loc in
    let rec_call := map (fun x => compute_nested_rc s x) local_uparams in
    if existsb isSome rec_call
      (* If some instatiate the parametricty  *)
    then let (lty, ltm) := add_param xp.(ep_strpos_uparams) local_uparams rec_call in
          Some ( fold_binder tProd loc (
                mkApp (mkApps (tInd (mkInd xp.(ep_cparam_kname) pos_indb) [])
                             (lty ++ local_nuparams_indices))
                      (mkApps (get_term s key_arg) (get_terms s key_locals))),
              fold_binder tLambda loc (
              mkApp (mkApps (tConst xp.(ep_fdt_kname) [])
                            (ltm ++ local_nuparams_indices))
                            (mkApps (get_term s key_arg) (get_terms s key_locals))))
    else None
  end.

#[using="All"]
Definition make_rec_call : key -> term -> option (term * term) :=
  fun key_arg ty => make_rec_call_aux s key_arg ty.

End MkRecCall.