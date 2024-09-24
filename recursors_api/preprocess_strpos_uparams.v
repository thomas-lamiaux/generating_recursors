From RecAPI Require Import api_debruijn.


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
  Context (nb_uparams : nat).


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
Definition default_value : list bool :=
  let uparams := firstn nb_uparams (rev mdecl.(ind_params)) in
  let isType decl := match reduce_full E init_info decl.(decl_type)
                     with tSort _ => true | _ => false end in
  map isType uparams.

Definition and_list : list bool -> list bool -> list bool :=
  map2 andb.

Notation "l1 &&l l2" := (and_list l1 l2) (at level 50).


(* 2. Compute strict pos for an arg *)
Definition check_not_free (ty : term) (e : info) : list bool :=
  map (fun pos => noccur_between pos 1 ty)
      (map get_rel (get_term "params" e)).

Fixpoint preprocess_strpos_arg (ty : term) (e : info) {struct ty} : list bool :=
  let (hd, iargs) := decompose_app ty in
  match hd with
  | tProd an A B =>
                    check_not_free A e &&l
                    let e' := add_old_var (Some "local") (mkdecl an None A) e
                    in preprocess_strpos_arg B e'
  | tRel i => default_value
  | tInd (mkInd kname_indb pos_indb) _ => default_value
     (* if eqb kname kname_indb then default_value else default_value *)
  | _ => check_not_free hd e
  end.




(* Print global_env.
Print global_declarations.
Print global_decl. *)

Definition get_ind_from_env : kername -> global_env -> option mutual_inductive_body :=
  fun kname0 E =>
  let ' mk_global_env _ dec _ := E in
  let y := find (fun x => eqb kname (fst x)) dec in
  match y with
  | Some (_, (InductiveDecl mdecl0)) => Some mdecl0
  | _ => None
  end.


(* 3. Compute the number of uniform parameters of an inductive type *)
Definition preprocess_strpos : list bool :=
  let e := init_info in
  let e := replace_ind kname mdecl e in
  let e := add_context (Some "params") (rev (firstn nb_uparams (rev mdecl.(ind_params)))) e in
  check_ctors_by_arg and_list default_value E preprocess_strpos_arg (get_args mdecl) e.


(* 4. Debug functions *)
Definition debug_preprocess_strpos : _ :=
  let e := init_info in
  let e := replace_ind kname mdecl e in
  let e := add_context (Some "params") (rev (firstn nb_uparams (rev mdecl.(ind_params)))) e in
  debug_check_ctors_by_arg E preprocess_strpos_arg (get_args mdecl) e.



End CustomParam.