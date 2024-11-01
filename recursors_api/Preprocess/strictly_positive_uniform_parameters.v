From RecAPI Require Import api_debruijn.


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
  Context (nb_uparams : nat).
  Context (E : global_env).
  Context (Ep : param_env).

  (* 1. Default value and bin op *)
  Definition default_value : list bool :=
  let uparams := firstn nb_uparams (rev mdecl.(ind_params)) in
  let isType decl := match reduce_full E init_state decl.(decl_type)
                      with tSort (sType _) => true | _ => false end in
  map isType uparams.

  Definition all_false : list bool := repeat false nb_uparams.

  Definition and_list : list bool -> list bool -> list bool :=
    map2 andb.

  Notation "l1 &&l l2" := (and_list l1 l2) (at level 50).


  Definition get_rel (ty : term) : nat :=
    match ty with
    | tRel i => i
    | _ => 404
    end.

  (* 2. Compute strict pos for an arg *)
Section CheckArg.
  Context (id_inds   : list ident).
  Context (id_uparams : list ident).
  Context (id_nuparams : list ident).

  Definition check_not_free (ty : term) (s : state) : list bool :=
    map (fun pos => noccur_between pos 1 ty)
        (map get_rel (get_terms id_uparams s)).

  Fixpoint preprocess_strpos_arg (ty : term) (s : state) {struct ty} : list bool :=
    let (hd, iargs) := decompose_app ty in
    match hd with
    (* 1. If it is an product check that id does not appear left of the arrow, and check the right side *)
    | tProd an A B => (check_not_free A s) &&l
                      (let* _ s := add_old_var (Some "local") (mkdecl an None A) s in
                       preprocess_strpos_arg B s)
    (* 2. If it is a let in, store and check the remaining of the term *)
    | tLetIn an A db B => let* _ s := add_old_var (Some "local") (mkdecl an None A) s in
                          preprocess_strpos_arg (reduce_lets s B) s
    (* 3. If it is variable:  *)
    | tRel n => if check_ids n id_inds s
                (* 3.1 If it is the inductive type being defined, then nothing to check *)
                then default_value
                (* 3.2 Otherwise, check the arguments  *)
                else fold_right and_list default_value (map (fun X => check_not_free X s) iargs)
    (* 3. If it is nested *)
    | tInd (mkInd kname_indb pos_indb) _ =>
        (* Check if there is at least one argument to save computation *)
        if length iargs =? 0 then default_value else
        match find (fun x => eq_constant kname_indb x.(ep_kname)) Ep with
        | Some (mk_one_param_env _ nb_uparams_indb nestable _ _) =>
            (* Retrieve the instantiation *)
            let uparams_inst := firstn nb_uparams_indb iargs in
            let nuparams_indices_inst := skipn nb_uparams_indb iargs in
            (* 3.1 For each uparams_inst:
                - if you can nest on it => check for strict positivity in the instantiation
                - if you can not => check if they appear in it *)
            let strpos_uparams := fold_right (fun ' (b, X) t =>
                if (b : bool) then preprocess_strpos_arg X s &&l t else check_not_free X s)
              default_value (combine nestable uparams_inst) in
            (* 3.2 Check they do not appear in the instantiation of nuparams or indices *)
              let free_nuparams_indices := fold_right (fun X t => check_not_free X s &&l t)
                                              default_value nuparams_indices_inst in
            (* 3.3 Check they do not appear in the type of a varibale in the nuparams or indices *)
            strpos_uparams &&l free_nuparams_indices
        | None => all_false
        end
    | _ => default_value
    end.


  (* Check the uparams does not appear in the types *)
  Definition check_free_cxt : list term -> state -> list bool :=
    fun lty s =>
    fold_right (fun X t => check_not_free X s &&l t)
      default_value lty.

End CheckArg.


(* 3. Compute the number of uniform parameters of an inductive type *)
Definition preprocess_strpos : list bool :=
  (* add inds *)
  let s := add_mdecl kname nb_uparams mdecl init_state in
  let* id_inds s := add_inds (get_mdecl kname s) s in
  let* _ id_uparams _ s  := add_old_context (Some "uparams") (get_uparams kname s) s in
  let* _ id_nuparams _ s := add_old_context (Some "nparams") (get_nuparams kname s) s in
  (* 1. Check strict positivity in the arguments *)
  (check_ctors_by_arg and_list default_value E (preprocess_strpos_arg id_inds id_uparams)
    (get_all_args kname s) s)
  (* Check the uparams does not appear in the types of the non uniform parameters *)
  &&l (check_free_cxt id_uparams (map decl_type (get_nuparams kname s)) s)
  (* Check the uparams does not appear in the types of the indices *)
  &&l (check_free_cxt id_uparams (fold_right (fun indb t => (map decl_type indb.(ind_indices)) ++ t)
                                    [] mdecl.(ind_bodies)) s).


(* 4. Debug function *)
Definition debug_preprocess_strpos : list (list (list bool)) :=
  (* add inds *)
  let s := add_mdecl kname nb_uparams mdecl init_state in
  let* id_inds s := add_inds (get_mdecl kname s) s in
  let* _ id_uparams _ s  := add_old_context (Some "uparams") (get_uparams kname s) s in
  let* _ id_nuparams _ s := add_old_context (Some "nparams") (get_nuparams kname s) s in
  debug_check_ctors_by_arg E (preprocess_strpos_arg id_inds id_uparams) (get_all_args kname s) s
  ++ [[(check_free_cxt id_uparams (map decl_type (get_nuparams kname s)) s)]]
  ++ [[(check_free_cxt id_uparams (fold_right (fun indb t => (map decl_type indb.(ind_indices)) ++ t)
                                  [] mdecl.(ind_bodies)) s)]].


End CustomParam.
