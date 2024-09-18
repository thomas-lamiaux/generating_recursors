From RecAPI Require Import api_debruijn.
From RecAPI Require Import commons.


Unset Guard Checking.

Section PreprocessParameters.

  Context (kname : kername).
  Context (pos_indb : nat).
  Context (mdecl : mutual_inductive_body).
  Context (E : global_env).

  Definition nb_params := mdecl.(ind_npars).

(* 1. Compute the number of uniform params *)
Definition check_uniform : list term -> info -> nat :=
  let fix aux n args e :=
  match args with
  | [] => nb_params
  | tRel pos_var :: args =>
      if check_var_pos "params" n pos_var e then aux (S n) args e else pos_var
  | _ => n
  end in aux 0.


(* 2. Compute the number of uniform parameters of an argument *)
Fixpoint preprocess_types (ty : term) (e : info) {struct ty} :  nat :=
  let (hd, iargs) := decompose_app ty in
  match hd with
  | tProd an A B => let e' := add_old_var (Some "local") (mkdecl an None A) e
                    in preprocess_types B e'
  | tInd (mkInd kname_indb pos_indb) _ =>
     if eqb kname kname_indb
     then check_uniform (firstn nb_params iargs) e
     else fold_right min nb_params (map (fun x => preprocess_types x e) iargs)
  | _ => nb_params
  end.


(* 3. Compute the number of uniform parameters of a constructor *)
Definition preprocess_args : context -> info -> nat :=
  fun args e =>
  fold_left_ie
    ( fun i arg e t =>
        let e' := add_old_var (Some "args") arg e in
        match arg.(decl_body) with
        | None => let rty := reduce_full E e (e ↑ arg.(decl_type)) in
                  min (preprocess_types rty e) (t e')
        | Some _ => t e'
        end
  )
  args e (fun _ => nb_params).


(* 4. Compute the number of uniform parameters of an inductive type *)
Definition preprocess_ctors : nat :=
  let e := init_info in
  let e := replace_ind kname mdecl e in
  let e := add_context (Some "params") mdecl.(ind_params) e in
  fold_right min nb_params
      (map (fun cstr => preprocess_args cstr.(cstr_args) e)
            (concat (map ind_ctors mdecl.(ind_bodies)))).


(* 5. Preprocess an inductive type *)
Definition preprocess_parameters : preprocess_mutual_inductive_body :=
  let n := preprocess_ctors in
  let revparams := rev mdecl.(ind_params) in
  {| pmb_kname := kname ;
     pmb_pos_indb := pos_indb ;
     (* uniform parameters *)
     pmb_uparams    := rev (firstn n revparams) ;
     pmb_nb_uparams := n ;
     (* non uniform parameters *)
     pmb_nuparams    := rev (skipn n revparams)  ;
     pmb_nb_nuparams := nb_params - n ;
     (* rest inductive *)
     pmb_ind_bodies := mdecl.(ind_bodies);
  |}.








(* 6. DEBUG FUNCTIONS *)
  Fixpoint debug_types (ty : term) (e : info) {struct ty} : _ :=
    let (hd, iargs) := decompose_app ty in
    match hd with
    | tProd an A B => let e' := add_old_var (Some "local") (mkdecl an None A) e
                      in debug_types B e'
    | tInd (mkInd kname_indb pos_indb) _ =>
       if eqb kname kname_indb
       then [2000]
       (* (mapi (fun i tm => check_uniform tm i e) (firstn nb_params iargs)) *)
       (* will bug for nesting *)
       else []
    | _ => []
    end.


(* 3. Compute the number of uniform parameters of a constructor *)
Definition debug_args : context -> info -> _ :=
  fun args e =>
  fold_left_ie
    ( fun i arg e t =>
        let e' := add_old_var (Some "args") arg e in
        match arg.(decl_body) with
        | None => let ty := e ↑ arg.(decl_type) in
                  let nty := debug_types ty e in
                  (e , ty, nty) :: (t e')
        | Some _ => t e'
        end
  )
  args e (fun _ => []).



(* 4. Compute the number of uniform parameters of an inductive type *)
Definition debug_nuparams : _ :=
  let e := init_info in
  let e := replace_ind kname mdecl e in
  let e := add_context (Some "params") mdecl.(ind_params) e in
  (map (fun x => debug_args x e)
       (map (cstr_args) (concat (map ind_ctors mdecl.(ind_bodies))))).


End PreprocessParameters.
