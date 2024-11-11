From NamedAPI Require Import core.
From NamedAPI Require Import fold_functions.
From NamedAPI Require Import inductive_access.
From NamedAPI Require Import context_access.
From NamedAPI Require Import context_store.

(* Interface to create terms

  1. Functions for building inductive types
-----------------------------------------------------------------
- replace_ind {X} : kername -> state -> (state -> X) -> X
- make_ind : kername -> nat -> list ident -> list ident -> list ident -> state -> term
- make_cst : kername -> nat -> nat -> list ident -> list ident -> state -> term

  2. Keep and Make Let in
-----------------------------------------------------------------
- kp_tLetIn : aname -> term -> term -> state -> (ident -> state -> term) -> term
- mk_tLetIn : aname -> term -> term -> state -> (ident -> state -> term) -> term

  3. Keep and Make Binary binder(s)
--------------------------------------------------------------------------------
Context (binder : aname -> term -> term -> term)

- kp_binder : aname -> term -> option ident -> state -> (ident -> state -> term) -> term
- it_kp_binder : context -> option ident -> state -> (list ident -> state -> term) -> term
- closure_uparams : kername -> state -> (list ident -> state -> term) -> term
- closure_nuparams : kername -> state -> (list ident -> state -> term) -> term
- closure_params : kername -> state -> (list ident -> state -> term) -> term

- mk_binder : aname -> term -> option ident -> state -> (ident -> state -> term) -> term
- it_mk_binder : context -> option ident -> state -> (list ident -> state -> term) -> term
- closure_indices : kername -> nat -> state -> (list ident -> state -> term) -> term
- closure_binder {A} : option ident -> list A -> (naming : nat -> A -> aname) ->
    (typing : nat -> A -> state -> term) -> state -> (list ident -> state -> term) -> term

- kp_tProd / kp_tLambda / mk_tProd / mk_tLambda

  4. Make Fixpoint
--------------------------------------------------------------------------------
Context (kname : kername)
        (fty   : nat -> term)
        (frarg : nat -> nat)

- mk_tFix : nat -> state -> (list ident -> nat -> state -> term) -> term

End

- tFix_default_rarg : kername -> state -> nat -> nat

  5. Make Match
-----------------------------------------------------------------
Context (kname : kername) (pos_indb : nat) (indb : one_inductive_body)
        (key_uparams key_nuparams : list ident)
        (mk_case_pred : list ident -> ident -> state -> term)

- mk_tCase : term -> state -> (nat -> list ident -> list ident -> list ident -> state -> term) -> term

*)




(* 1. Functions for building inductive types *)
Definition replace_ind {X} : state -> kername -> (state -> X) -> X :=
  fun s kname t =>
  let ind_terms := mapi (fun i _ => (tInd (mkInd kname i) [])) (get_ind_bodies kname s) in
  let* s := subst_old_context s ind_terms in
  t s.

(* Builds: Ind A1 ... An B0 ... Bm i1 ... il *)
Definition make_ind : state -> kername -> nat -> keys -> keys -> keys -> term :=
  fun s kname pos_indb key_uparams key_nuparams key_indices =>
  mkApps (tInd (mkInd kname pos_indb) [])
          (  get_terms s key_uparams
          ++ get_terms s key_nuparams
          ++ get_terms s key_indices  ).

Arguments make_ind _ _ pos_indb key_uparams key_nuparams key_indices.

(* Builds: Cst A1 ... An B0 ... Bm *)
Definition make_cst : state -> kername -> nat -> nat -> keys -> keys -> term :=
  fun s kname pos_indb pos_ctor key_uparams key_nuparams =>
  mkApps (tConstruct (mkInd kname pos_indb) pos_ctor [])
          (get_terms s key_uparams ++ get_terms s key_nuparams).

Arguments make_cst _ pos_indb pos_ctor _ key_uparams key_nuparams.



(* 2. Keep and Make Let in *)
Definition kp_tLetIn : state -> aname -> term -> term -> (state -> key -> term) -> term :=
  fun s an db ty cc =>
  let db' := weaken s db in
  let ty' := weaken s ty in
  let* s' key_let := add_old_letin s (Some "let") an db ty in
  tLetIn an db' ty' (cc s' key_let).

Definition mk_tLetIn : state -> aname -> term -> term -> (state -> key -> term) -> term :=
  fun s an db ty cc =>
  let* s key_let := add_fresh_letin s (Some "let") an db ty in
  tLetIn an db ty (cc s key_let).



(* 3. Keep and Make Binary binder(s) *)
Section Binder.

  Context (binder : aname -> term -> term -> term).

  Definition kp_binder : state -> option ident -> aname -> term -> (state -> key -> term) -> term :=
    fun s x an ty cc =>
    let ty' := weaken s ty in
    let* s' key_bind := add_old_var s x an ty in
    binder an ty' (cc s' key_bind).

  Definition it_kp_binder : state -> option ident -> context -> (state -> keys -> term) -> term :=
    fun s x cxt => fold_left_state
    (fun _ cdecl s c =>
      let '(mkdecl an z ty) := cdecl in
      match z with
      | None => kp_binder s x an ty c
      | Some db => kp_tLetIn s an db ty c
      end) cxt s.

  Definition closure_uparams : state -> kername -> (state -> keys -> term) -> term :=
    fun s kname => it_kp_binder s (Some "uparams") (get_uparams kname s).

  Definition closure_nuparams : state -> kername -> (state -> keys -> term) -> term :=
    fun s kname => it_kp_binder s (Some "nuparams") (get_nuparams kname s).

  Definition closure_params : state -> kername -> (state -> keys -> term) -> term :=
  fun s kname => it_kp_binder s (Some "params") (get_params kname s).

  Definition mk_binder : state -> option ident -> aname -> term -> (state -> key -> term) -> term :=
    fun s x an ty cc =>
      let* s key_mk := add_fresh_var s x an ty in
      binder an ty (cc s key_mk).

  Definition it_mk_binder : state -> option ident -> context -> (state -> keys -> term) -> term :=
    fun s x cxt => fold_left_state
    (fun _ cdecl s cc =>
      let '(mkdecl an z ty) := cdecl in
      match z with
      | None => mk_binder s x an ty cc
      | Some db => mk_tLetIn s an db ty cc
      end) cxt s.

  Definition closure_indices : state -> kername -> nat -> (state -> keys -> term) -> term :=
    fun s kname pos_indb => it_mk_binder s (Some "indices") (get_indices kname pos_indb s).

  Definition closure_binder {A} (s : state) (x : option ident) (l : list A)
    (naming : nat -> A -> aname) (typing : nat -> A -> state -> term) :
    (state -> keys -> term) -> term :=
    fold_right_state
      (fun n a s cc => mk_binder s x (naming n a) (typing n a s) cc)
      l s.

End Binder.

Definition kp_tProd := kp_binder tProd.
Definition kp_tLambda := kp_binder tLambda.

Definition mk_tProd := mk_binder tProd.
Definition mk_tLambda := mk_binder tLambda.



(* 4. Make Fixpoint *)
Section mk_tFix.
  Context (kname : kername).
  Context (tFix_type : nat -> term).
  Context (tFix_rarg : nat -> nat).

  #[local] Definition tFix_name : nat -> ident :=
    fun pos_indb => "F" ^ string_of_nat pos_indb ^  "_" ^ (snd kname).

  #[local] Definition tFix_aname : nat -> aname :=
    fun pos_indb => mkBindAnn (nNamed (tFix_name pos_indb)) Relevant.

  #[local] Definition tFix_context : state -> context :=
    fun s => rev ( mapi
    (fun pos_indb _ => mkdecl (tFix_aname pos_indb) None (tFix_type pos_indb))
    (get_ind_bodies kname s)).

  Definition mk_tFix : state -> nat -> (state -> keys -> nat -> term) -> term :=
    fun s focus tmc =>
    let* s_Fix _ key_fixs _ := add_fresh_context s (Some "tFix") (tFix_context s) in
    tFix
      (mapi (fun pos_indb _ =>
        mkdef _ (tFix_aname pos_indb)
                (tFix_type  pos_indb)
                (tmc s_Fix key_fixs pos_indb )
                (tFix_rarg  pos_indb))
            (get_ind_bodies kname s))
      focus.

End mk_tFix.

Definition tFix_default_rarg : state -> kername -> nat -> nat :=
  fun s kname pos_indb => get_nb_nuparams kname s + length (get_indices kname pos_indb s).



(* 5. Make Match *)
Section MktCase.
  Context (kname : kername).
  Context (pos_indb : nat).
  Context (mk_case_pred : state -> keys -> key -> term).
  Context (key_uparams key_nuparams : keys).

  #[local] Definition mk_case_info : state -> case_info :=
    fun s => mk_case_info (mkInd kname pos_indb) (get_nb_params kname s) Relevant.

  #[local] Definition mk_pred : state -> predicate term :=
    fun s =>
    let* sPred _ key_findices _ := add_fresh_context s None (get_indices kname pos_indb s) in
    let* sPred key_fVarMatch := add_fresh_var sPred (Some "fresh var match") (mkBindAnn nAnon Relevant)
                                (make_ind sPred kname pos_indb key_uparams key_nuparams key_findices) in
    mk_predicate []
      (get_terms s key_uparams ++ get_terms s key_nuparams)
      (get_aname sPred key_fVarMatch :: get_anames sPred key_findices)
      (mk_case_pred sPred key_findices key_fVarMatch).

  Definition mk_tCase : state -> term -> (state -> keys -> keys -> keys -> nat -> term) -> term :=
    fun s tm_match branch =>
    tCase (mk_case_info s) (mk_pred s) tm_match
    (mapi
      (fun pos_ctor ctor =>
      let* s key_lets key_args key_lets_args := add_old_context s (Some ("args_" ^ snd kname)) ctor.(cstr_args) in
          mk_branch (rev (get_anames s key_lets_args)) (branch s key_lets key_args key_lets_args pos_ctor))
      (get_indb kname pos_indb s).(ind_ctors)).

End MktCase.