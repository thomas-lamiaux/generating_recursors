From RecAPI Require Import api_debruijn.
From RecAPI Require Import commons.


Unset Guard Checking.

Section GenRec.

  Context (pdecl : preprocess_mutual_inductive_body).
  Context (E : env_param).

  MetaCoq Quote Definition qTrue := True.
  MetaCoq Quote Definition qI := I.

  (* Issues with guard => need WF *)
  (* Issues let and reduction     *)
  Fixpoint make_rec_pred (ty : term) (e : info) {struct ty} : option (term * term) :=
    let (hd, iargs) := decompose_app ty in
    match hd with
    (* 1. If it is the inductive type *)
    | tRel n =>
      match (Some 0) with
      | Some pos_s =>
          (* Get local nuparams and indices *)
          let local := skipn pdecl.(pmb_nb_uparams) iargs in
          let nuparams := firstn pdecl.(pmb_nb_nuparams) local in
          let indices  := skipn  pdecl.(pmb_nb_nuparams) local in
          (* Ppos_s B0 ... Bm i0 ... il / Fpos_s  B0 ... Bm i0 ... il *)
          Some (make_pred pos_s nuparams indices e,
                mkApps (geti "F" pos_s e) (nuparams ++ indices))
      | None => None
      end
    (* 2. If it is a product *)
    | tProd an A B => None
    (* 3. If it is nested *)
    | tInd (mkInd s pos_s) _ => None
    (* 4. Otherwise *)
    | _ => None
    end.

End GenRec.


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
            (* 1. If so => create rec call => get uparams / nuparams / indices *)
        then let local := skipn pdecl.(pmb_nb_uparams) iargs in
             let nuparams := firstn pdecl.(pmb_nb_nuparams) local in
             let indices  := skipn  pdecl.(pmb_nb_nuparams) local in
            Some (make_pred #|pdecl.(pmb_ind_bodies)| pos_s e nuparams indices,
                  mkApps (tVar (make_name "F" pos_s)) (nuparams ++ indices))
            (* 2. If not: check for its parametricity *)
        else match find (fun x => eq_constant s x.(ep_kname)) E with
            (* 2.1 If so => Check recall on param => nest or not *)
            | Some s =>
                (* Get nb_params params indices *)
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