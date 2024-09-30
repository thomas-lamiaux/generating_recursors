From RecAPI Require Import api_debruijn.
From RecAPI Require Import preprocess_uparams.

(* -> Check which uniform type param are strict pos => list bool
1. given the type of an arg check
2. Check over cstr
3. Check over ind

*)
Unset Guard Checking.

Section CustomParam.

  Context (kname : kername).
  Context (mdecl : mutual_inductive_body).
  Context (E : global_env).


(* 0. Aux functions *)
Fixpoint noccur_between (k n : nat) (t : term) {struct t} : bool :=
  match t with
  | tRel i => (i <? k) || (k + n <=? i)
  | tEvar _ args => forallb (noccur_between k n) args
  | tCast c _ t0 => noccur_between k n c && noccur_between k n t0
  | tProd _ T M | tLambda _ T M =>
	  noccur_between k n T && noccur_between (S k) n M
  | tLetIn _ b t0 b' =>
      noccur_between k n b && noccur_between k n t0 &&
      noccur_between (S k) n b'
  | tApp u v => noccur_between k n u && forallb (noccur_between k n) v
  | tCase _ p c brs =>
      let k' := #|pcontext p| + k in
      let p' :=
        test_predicate (fun _ : Instance.t => true)
          (noccur_between k n) (noccur_between k' n) p in
      let brs' := test_branches_k (fun k0 : nat => noccur_between k0 n) k brs
        in
      p' && noccur_between k n c && brs'
  | tProj _ c => noccur_between k n c
  | tFix mfix _ | tCoFix mfix _ =>
      let k' := #|mfix| + k in
      forallb (test_def (noccur_between k n) (noccur_between k' n)) mfix
  | tArray _ arr def ty =>
      forallb (noccur_between k n) arr && noccur_between k n def &&
      noccur_between k n ty
  | _ => true
  end.

Definition get_rel (ty : term) : nat :=
  match ty with
  | tRel i => i
  | _ => 2000
  end.




(* 1. Default value and bin op *)
Definition nb_uparams := preprocess_uparams kname mdecl E.

Definition default_value : list bool :=
  let uparams := firstn nb_uparams (rev mdecl.(ind_params)) in
  let isType decl := match reduce_full E init_info decl.(decl_type)
                     with tSort (sType _) => true | _ => false end in
  map isType uparams.

Definition all_false : list bool := repeat false nb_uparams.

Definition and_list : list bool -> list bool -> list bool :=
  map2 andb.

Notation "l1 &&l l2" := (and_list l1 l2) (at level 50).


(* 2. Compute strict pos for an arg *)
Definition check_not_free (ty : term) (e : info) : list bool :=
  map (fun pos => noccur_between pos 1 ty)
      (map get_rel (get_term (kname_to_ident "params" kname) e)).

Definition get_mdecl_from_env : kername -> global_env -> option mutual_inductive_body :=
  fun kname E =>
  let ' mk_global_env _ dec _ := E in
  let y := find (fun x => eqb kname (fst x)) dec in
  match y with
  | Some (_, (InductiveDecl mdecl0)) => Some mdecl0
  | _ => None
  end.




  Context (preprocess_strpos : kername -> mutual_inductive_body -> global_env -> list bool).


  (* main functions *)
  Fixpoint preprocess_strpos_arg (ty : term) (e : info) {struct ty} : list bool :=
    let (hd, iargs) := decompose_app ty in
    match hd with
    (* 1. If it an iterated product *)
    | tProd an A B => (check_not_free A e) &&l
                      (let e' := add_old_var (Some "local") (mkdecl an None A) e
                      in preprocess_strpos_arg B e')
    (* 2. ? *)
    | tRel i => fold_right and_list default_value (map (fun X => check_not_free X e) iargs)
    (* 3. If it an inductive type *)
    | tInd (mkInd kname_indb pos_indb) _ =>
        (* 3.1 If it is the current one *)
        if eqb kname kname_indb then default_value else
        if length iargs =? 0 then default_value else
        (* 3.2 If it is nested get the mdecl *)
        let opt_mdecl_indb := get_mdecl_from_env kname_indb E in
        match opt_mdecl_indb with
        | None => default_value
        | Some mdecl_indb =>
          (* 3.2.1 Check which uparams are nestable *)
          let nestable := preprocess_strpos kname_indb mdecl_indb E in
          let nb_uparams_indb := length nestable in
          let uparams_indb := firstn nb_uparams_indb iargs in
          let nuparams_indices_indb := skipn nb_uparams_indb iargs in
          (* 3.2.2 Check the uparams are strictly pos *)
          let strpos_uparams_val := map2 (fun (b : bool) X =>
            if b then preprocess_strpos_arg X e else check_not_free X e)
                  nestable uparams_indb in
          let strpos_uparams := fold_right and_list default_value strpos_uparams_val in
          (* 3.2.3 Check it does not appear in uparams and indices *)
          let strpos_nuparams_indices_val := map (fun X => check_not_free X e) nuparams_indices_indb in
          let strpos_nuparams_indices := fold_right and_list default_value strpos_nuparams_indices_val in
          (* Return *)
          strpos_uparams &&l strpos_nuparams_indices
        end
    | _ => check_not_free ty e
    end.

End CustomParam.

(* 3. Compute the number of uniform parameters of an inductive type *)
Fixpoint preprocess_strpos (kname : kername) (mdecl : mutual_inductive_body) (E : global_env) {struct kname} : list bool :=
  let nb_uparams := nb_params mdecl in
  let default_value := default_value kname mdecl E in
  let e := init_info in
  let e := replace_ind kname mdecl e in
  let e := add_old_context (kname_to_opt "params" kname) (rev (firstn nb_uparams (rev mdecl.(ind_params)))) e in
  let fct : term -> info -> list bool := preprocess_strpos_arg kname mdecl E preprocess_strpos in
  check_ctors_by_arg and_list default_value E fct (get_args mdecl) e.










(* 4. Debug functions *)
Inductive RoseTree (A : Type) : Type :=
| leaf : A -> RoseTree A
| leaf_left_tProd : A -> RoseTree A
| node_tProd : list (RoseTree A) -> RoseTree A
| node_nested : list (RoseTree A) -> RoseTree A.

Arguments leaf {_} _.
Arguments leaf_left_tProd {_} _.
Arguments node_tProd {_} _.
Arguments node_nested {_} _.

(*
Fixpoint debug_preprocess_strpos_arg (ty : term) (e : info) {struct ty} : RoseTree (info * list bool) :=
  let (hd, iargs) := decompose_app ty in
  match hd with
  | tProd an A B => node_tProd [
                    leaf_left_tProd (e , check_not_free A e) ;
                    let e' := add_old_var (Some "local") (mkdecl an None A) e
                    in debug_preprocess_strpos_arg B e']
  | tRel i => leaf ([], default_value)
  | tInd (mkInd kname_indb pos_indb) _ =>
      if eqb kname kname_indb
      then leaf ([], default_value)
      else (* get mdecl associated to indb *)
        let opt_mdecl_indb := get_mdecl_from_env kname_indb E in
        match opt_mdecl_indb with
        | None => leaf ([], default_value)
        | Some mdecl_indb =>
          (* get uparams and the rest *)
          let nb_block_indb := length mdecl_indb.(ind_bodies) in
          let nb_uparams_indb := preprocess_uparams kname_indb mdecl_indb E in
          let uparams := map (lift0 1) (firstn nb_uparams_indb iargs) in
          let indices := map (lift0 nb_block_indb) (skipn nb_uparams_indb iargs) in
          (* update env with ind  *)
          let e := replace_ind kname_indb mdecl_indb e in
          (* update env with uparams and subst *)
          let (uparams_cxt, nuparams_cxt) := split_params nb_uparams_indb mdecl_indb in
          let e := add_replace_context (kname_to_opt "UPARAMS" kname_indb) uparams_cxt uparams e in
          let e := add_old_context (kname_to_opt "NUPARAMS" kname_indb) [] e in
          (* get the args and subst *)
          (* let args := map (weaken_context e) (get_args mdecl_indb) in *)
          let args := (get_args mdecl_indb) in
          (* Check it does not appear in the body of cst *)
          if nb_uparams_indb =? 0 then leaf ([], default_value) else (* for perf *)
          node_nested (@check_ctors_by_arg (list (RoseTree (info * (list bool)))) (fun x y => app x y) [] E kname_indb (fun kname tm e => [debug_preprocess_strpos_arg kname tm e]) args e)
          (* Check if does not appear in nuparams and indices *)
          (* leaf (repeat false nb_uparams) *)
          (* default_value *)
        end
  | _ => leaf ([], check_not_free hd e)
  end.
  *)

Fixpoint debug_preprocess_strpos (kname : kername) (mdecl : mutual_inductive_body) (E : global_env) {struct kname} : _ :=
  let nb_uparams := nb_params mdecl in
  let default_value := default_value kname mdecl E in
  let e := init_info in
  let e := replace_ind kname mdecl e in
  let e := add_old_context (kname_to_opt "params" kname) (rev (firstn nb_uparams (rev mdecl.(ind_params)))) e in
  let fct : term -> info -> list bool := preprocess_strpos_arg kname mdecl E preprocess_strpos in
  debug_check_ctors_by_arg E fct (get_args mdecl) e.