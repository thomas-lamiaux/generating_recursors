From RecAPI Require Import api_debruijn.
From RecAPI Require Import commons.


(*
1. Dealing with nesting
2. Generating Rec call
 *)

Unset Guard Checking.

Section GenRec.

Context (pdecl : preprocess_mutual_inductive_body).
Context (E : global_env).
Context (Ep : env_param).

MetaCoq Quote Definition qTrue := True.
MetaCoq Quote Definition qI := I.




(* 2. Generates rec call  *)

(* Issues with guard => need WF *)
(* Issues let and reduction     *)
(* 2.1 If it is an Ind *)
Fixpoint make_rec_pred_ind (ty : term) (e : info) {struct ty} : option (term * term) :=
  let (hd, iargs) := decompose_app ty in
  match hd with
  | tInd (mkInd kname_ind pos_indb) _ =>
    if eqb pdecl.(pmb_kname) kname_ind
    (* 2. Itf it is the inductive type *)
    then let local := skipn pdecl.(pmb_nb_uparams) iargs in
          let nuparams := firstn pdecl.(pmb_nb_nuparams) local in
          let indices  := skipn  pdecl.(pmb_nb_nuparams) local in
          (* Pi B0 ... Bm i0 ... il / Fi  B0 ... Bm i0 ... il *)
          Some (make_pred pos_indb nuparams indices e,
              mkApps (geti_term "F" pos_indb e) (nuparams ++ indices))
    (* 3. If it is nested *)
    else None
  (* 4. Otherwise *)
  | _ => None
  end.

(* 2.2 Generates rec call *)
(* Won't pass the guard ! *)
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


(*

-> Compute which param are strict positive
-> Take parametricity for them
-> nest on them, fun _ => True when needed



param_is_strict_positive : (pos_param : nat) -> indb -> bool
strict_positive_params : indb -> list bool
*)

(* Dealing with nesting *)
(*
  Fixpoint add_param (l : list term) (rc : list (option (term * term))) : list term * list term :=
    match l, rc with
    | nil, nil => (nil , nil)
    | A::l, x :: rc =>
      let (lty, ltm) := add_param l rc in
      match x with
      | None => let fT := (tLambda (mkBindAnn nAnon Relevant) A qTrue) in
                let fI := (tLambda (mkBindAnn nAnon Relevant) A qI) in
                (A :: fT :: lty, A :: fT :: fI :: ltm)
      | Some (ty, tm) => (A::ty::lty, A::ty::tm::ltm)
      end
    | _, _ => (nil, nil)
  end.

    | tInd (mkInd s pos_s) _ =>
        (* Check if it is inductive under scrutiny *)
        if eq_constant pdecl.(pmb_kname) s
            (* 1. If so => create rec call => get_term uparams / nuparams / indices *)
        then let local := skipn pdecl.(pmb_nb_uparams) iargs in
             let nuparams := firstn pdecl.(pmb_nb_nuparams) local in
             let indices  := skipn  pdecl.(pmb_nb_nuparams) local in
            Some (make_pred #|pdecl.(pmb_ind_bodies)| pos_s e nuparams indices,
                  mkApps (tVar (make_name "F" pos_s)) (nuparams ++ indices))
            (* 2. If not: check for its parametricity *)
        else match find (fun x => eq_constant s x.(ep_kname)) E with
            (* 2.1 If so => Check recall on param => nest or not *)
            | Some s =>
                (* get_term nb_params params indices *)
                let s_nb_params := s.(ep_body).(ind_npars) in
                let s_params  := firstn s_nb_params iargs in
                let s_indices := skipn s_nb_params iargs in
                (* Compute and check recall in parameters *)
                let rc := map (fun x => make_rec_pred x e) s_params in
                if existsb isSome rc
                (* If there is one *)
                then let (lty, ltm) := add_param s_params rc in
                      Some (mkApps (tInd (mkInd s.(ep_pkname) pos_s) []) (lty ++ s_indices),
                            mkApps (tConst s.(ep_tkname) []) (ltm ++ s_indices))
                else None
            (* 2.2 If not => do nothing *)
            | None => None
            end
*)