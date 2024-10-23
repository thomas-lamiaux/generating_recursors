From RecAPI Require Import api_debruijn.
From RecAPI Require Import uniform_parameters.


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

  (* 1. Default value and bin op *)
  Definition nb_uparams := preprocess_uparams kname mdecl E.

  Definition default_value : list bool :=
  let uparams := firstn nb_uparams (rev mdecl.(ind_params)) in
  let isType decl := match reduce_full E init_state decl.(decl_type)
                      with tSort (sType _) => true | _ => false end in
  map isType uparams.

  Definition all_false : list bool := repeat false nb_uparams.

  Definition and_list : list bool -> list bool -> list bool :=
    map2 andb.

  Notation "l1 &&l l2" := (and_list l1 l2) (at level 50).


  (* 2. Compute strict pos for an arg *)
  Context (id_params : list ident).

  Definition get_rel (ty : term) : nat :=
    match ty with
    | tRel i => i
    | _ => failwith "this is not a tRel"
    end.


  Definition check_not_free (ty : term) (s : state) : list bool :=
    map (fun pos => noccur_between pos 1 ty)
        (map get_rel (get_term id_params s)).


  Context (preprocess_strpos : kername -> mutual_inductive_body -> global_env -> list bool).


  (* main functions *)
  Fixpoint preprocess_strpos_arg (ty : term) (s : state) {struct ty} : list bool :=
    let (hd, iargs) := decompose_app ty in
    match hd with
    (* 1. If it an iterated product *)
    | tProd an A B => (check_not_free A s) &&l
                      (let id_local := fresh_ident (Some "local") s in
                      let s' := add_old_var id_local (mkdecl an None A) s
                      in preprocess_strpos_arg B s')
    (* 2. ? *)
    | tRel i => fold_right and_list default_value (map (fun X => check_not_free X s) iargs)
    (* 3. If it an inductive type *)
    | tInd (mkInd kname_indb pos_indb) _ =>
        (* 3.1 If it is the current one *)
        if eqb kname kname_indb then default_value else
        if length iargs =? 0 then default_value else
        (* 3.2 If it is nested get the mdecl *)
        match TemplateLookup.lookup_minductive E kname_indb with
        | None => default_value
        | Some mdecl_indb =>
          (* 3.2.1 Check which uparams are nestable *)
          let nestable := preprocess_strpos kname_indb mdecl_indb E in
          let nb_uparams_indb := length nestable in
          let uparams_indb := firstn nb_uparams_indb iargs in
          let nuparams_indices_indb := skipn nb_uparams_indb iargs in
          (* 3.2.2 Check the uparams are strictly pos *)
          let strpos_uparams_val := map2 (fun (b : bool) X =>
            if b then preprocess_strpos_arg X s else check_not_free X s)
                  nestable uparams_indb in
          let strpos_uparams := fold_right and_list default_value strpos_uparams_val in
          (* 3.2.3 Check it does not appear in uparams and indices *)
          let strpos_nuparams_indices_val := map (fun X => check_not_free X s) nuparams_indices_indb in
          let strpos_nuparams_indices := fold_right and_list default_value strpos_nuparams_indices_val in
          (* Return *)
          strpos_uparams &&l strpos_nuparams_indices
        end
    | _ => check_not_free ty s
    end.

End CustomParam.


(* 3. Compute the number of uniform parameters of an inductive type *)
Fixpoint preprocess_strpos (kname : kername) (mdecl : mutual_inductive_body) (E : global_env) {struct kname} : list bool :=
  let nb_uparams := nb_params mdecl in
  let default_value := default_value kname mdecl E in
  (* add inds *)
  let s := add_mdecl kname nb_uparams mdecl init_state in
  let ' (id_inds, s) := replace_ind kname s in
  (* add params *)
  let ' (id_params, id_cxt_params) := fresh_id_context (Some "params") s (get_params kname s) in
  let s := add_old_context id_cxt_params s in
  (* compute fct rec  *)
  let fct := preprocess_strpos_arg kname mdecl E id_params preprocess_strpos in
  check_ctors_by_arg and_list default_value E fct (get_args mdecl) s.










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
Fixpoint debug_preprocess_strpos_arg (ty : term) (s : state) {struct ty} : RoseTree (state * list bool) :=
  let (hd, iargs) := decompose_app ty in
  match hd with
  | tProd an A B => node_tProd [
                    leaf_left_tProd (s , check_not_free A s) ;
                    let s' := add_old_var (Some "local") (mkdecl an None A) s
                    in debug_preprocess_strpos_arg B s']
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
          let s := replace_ind kname_indb mdecl_indb s in
          (* update env with uparams and subst *)
          let (uparams_cxt, nuparams_cxt) := split_params nb_uparams_indb mdecl_indb in
          let s := add_replace_context (kname_to_opt "UPARAMS" kname_indb) uparams_cxt uparams s in
          let s := add_old_context (kname_to_opt "NUPARAMS" kname_indb) [] s in
          (* get the args and subst *)
          (* let args := map (weaken_context s) (get_args mdecl_indb) in *)
          let args := (get_args mdecl_indb) in
          (* Check it does not appear in the body of cst *)
          if nb_uparams_indb =? 0 then leaf ([], default_value) else (* for perf *)
          node_nested (@check_ctors_by_arg (list (RoseTree (state * (list bool)))) (fun x y => app x y) [] E kname_indb (fun kname tm s => [debug_preprocess_strpos_arg kname tm s]) args s)
          (* Check if does not appear in nuparams and indices *)
          (* leaf (repeat false nb_uparams) *)
          (* default_value *)
        end
  | _ => leaf ([], check_not_free hd s)
  end.
  *)

Fixpoint debug_preprocess_strpos (kname : kername) (mdecl : mutual_inductive_body) (E : global_env) {struct kname} : _ :=
  let nb_uparams := nb_params mdecl in
  let default_value := default_value kname mdecl E in
  (* add inds *)
  let s := add_mdecl kname nb_uparams mdecl init_state in
  let ' (id_inds, s) := replace_ind kname s in
  (* add params *)
  let ' (id_params, id_cxt_params) := fresh_id_context (Some "params") s (get_params kname s) in
  let s := add_old_context id_cxt_params s in
  (* compute fct rec  *)
  let fct := preprocess_strpos_arg kname mdecl E id_params preprocess_strpos in
  debug_check_ctors_by_arg E fct (get_args mdecl) s.