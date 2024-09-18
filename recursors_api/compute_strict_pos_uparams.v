From RecAPI Require Import api_debruijn.
From RecAPI Require Import commons.
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
Definition nb_uparams := preprocess_ctors kname mdecl E.

Definition default_value : list bool :=
  repeat true nb_uparams.

Definition and_list : list bool -> list bool -> list bool :=
  map2 andb.

Notation "l1 &&l l2" := (and_list l1 l2) (at level 50).

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

(* 2. Compute the number of uniform parameters of an argument *)

(* 2.1 Check which parameters appear in a term *)
Definition check_not_free (ty : term) (e : info) : list bool :=
  map (fun pos => noccur_between pos 1 ty)
      (map get_rel (get_term "params" e)).

Fixpoint strpos_preprocess_arg (ty : term) (e : info) {struct ty} : list bool :=
  let (hd, iargs) := decompose_app ty in
  match hd with
  | tProd an A B =>
                    check_not_free A e &&l
                    (* default_value &&l *)
                    let e' := add_old_var (Some "local") (mkdecl an None A) e
                    in strpos_preprocess_arg B e'
  | tRel i => default_value
  | tInd (mkInd kname_indb pos_indb) _ => default_value
     (* if eqb kname kname_indb
     then check_uniform (firstn nb_params iargs) e
     else fold_right min nb_params (map (fun x => check_strict_pos_arg x e) iargs) *)
  | _ => check_not_free hd e
  end.


(* 3. Compute the number of uniform parameters of a constructor *)
Definition strpos_preprocess_args : context -> info -> list bool :=
  fun args e =>
  fold_left_ie
    ( fun i arg e t =>
        let e' := add_old_var (Some "args") arg e in
        match arg.(decl_body) with
        | None => let rty := reduce_full E e (e ↑ arg.(decl_type)) in
                  (strpos_preprocess_arg rty e) &&l t e'
        | Some _ => t e'
        end
  )
  args e (fun _ => default_value).


(* 4. Compute the number of uniform parameters of an inductive type *)
Definition strpos_preprocess_ctors : list bool :=
  let e := init_info in
  let e := replace_ind kname mdecl e in
  let e := add_context (Some "params") (rev (firstn nb_uparams (rev mdecl.(ind_params)))) e in
  fold_right and_list default_value
      (map (fun cstr => strpos_preprocess_args cstr.(cstr_args) e)
            (concat (map ind_ctors mdecl.(ind_bodies)))).






Definition debug_check (ty : term) (e : info) : term * (list nat) * (list bool) :=
  (ty, (map get_rel (get_term "params" e)), check_not_free ty e).

Fixpoint debug_strpos_preprocess_arg (ty : term) (e : info) {struct ty} : list (term * (list nat) * (list bool)) :=
  let (hd, iargs) := decompose_app ty in
  match hd with
  | tProd an A B =>
                    debug_check A e ::
                    (* default_value &&l *)
                    let e' := add_old_var (Some "local") (mkdecl an None A) e
                    in debug_strpos_preprocess_arg B e'
  | tRel i => [(tVar "REL", [], [])]
  | tInd (mkInd kname_indb pos_indb) _ => [(tVar "IND", [], [])]
      (* if eqb kname kname_indb
      then check_uniform (firstn nb_params iargs) e
      else fold_right min nb_params (map (fun x => check_strict_pos_arg x e) iargs) *)
  | _ => [(tVar "ELSE", [], [])]
  end.


(* 3. Compute the number of uniform parameters of a constructor *)
Definition debug_strpos_preprocess_args : context -> info -> list (list (_)) :=
  fun args e =>
  fold_left_ie
    ( fun i arg e t =>
        let e' := add_old_var (Some "args") arg e in
        match arg.(decl_body) with
        | None => let rty := reduce_full E e (e ↑ arg.(decl_type)) in
                  (debug_strpos_preprocess_arg rty e) :: t e'
        | Some _ => t e'
        end
  )
  args e (fun _ => []).


(* 4. Compute the number of uniform parameters of an inductive type *)
Definition debug_strpos_preprocess_ctors : _ :=
  let e := init_info in
  let e := replace_ind kname mdecl e in
  let e := add_context (Some "params") (rev (firstn nb_uparams (rev mdecl.(ind_params)))) e in
  fold_right cons []
      (map (fun cstr => debug_strpos_preprocess_args cstr.(cstr_args) e)
            (concat (map ind_ctors mdecl.(ind_bodies)))).



End CustomParam.