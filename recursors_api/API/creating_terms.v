From RecAPI Require Import core.
From RecAPI Require Import fold_functions.
From RecAPI Require Import inductive_access.
From RecAPI Require Import context_access.
From RecAPI Require Import context_store.

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
        (id_uparams id_nuparams : list ident)
        (mk_case_pred : list ident -> ident -> state -> term)

- mk_tCase : term -> state -> (nat -> list ident -> list ident -> list ident -> state -> term) -> term

*)




(* 1. Functions for building inductive types *)
Definition replace_ind {X} : kername -> state -> (state -> X) -> X :=
  fun kname s t =>
  let ind_terms := mapi (fun i _ => (tInd (mkInd kname i) [])) (get_ind_bodies kname s) in
  let* s := subst_old_vars ind_terms s in
  t s.

(* Builds: Ind A1 ... An B0 ... Bm i1 ... il *)
Definition make_ind : kername -> nat -> list ident -> list ident -> list ident -> state -> term :=
  fun kname pos_indb id_uparams id_nuparams id_indices s =>
  mkApps (tInd (mkInd kname pos_indb) [])
          (  get_terms id_uparams  s
          ++ get_terms id_nuparams s
          ++ get_terms id_indices s).

Arguments make_ind _ pos_indb id_uparams id_nuparams id_indices _.

(* Builds: Cst A1 ... An B0 ... Bm *)
Definition make_cst : kername -> nat -> nat -> list ident -> list ident -> state -> term :=
  fun kname pos_indb pos_ctor id_uparams id_nuparams s =>
  mkApps (tConstruct (mkInd kname pos_indb) pos_ctor [])
          (get_terms id_uparams s ++ get_terms id_nuparams s).

Arguments make_cst _ pos_indb pos_ctor id_uparams id_nuparams _.



(* 2. Keep and Make Let in *)
Definition kp_tLetIn : aname -> term -> term -> state -> (ident -> state -> term) -> term :=
  fun an db t1 s t2 =>
  let db' := weaken s db in
  let t1' := weaken s t1 in
  let* id_let s' := add_old_var (Some "let") (mkdecl an (Some db) t1) s in
  tLetIn an db' t1' (t2 id_let s').

Definition mk_tLetIn : aname -> term -> term -> state -> (ident -> state -> term) -> term :=
  fun an db t1 s t2 =>
  let* id_let s := add_fresh_var (Some "let") (mkdecl an (Some db) t1) s in
  tLetIn an db t1 (t2 id_let s).



(* 3. Keep and Make Binary binder(s) *)
Section Binder.

  Context (binder : aname -> term -> term -> term).

  Definition kp_binder : aname -> term -> option ident -> state -> (ident -> state -> term) -> term :=
    fun an t1 x s t2 =>
    let t1' := weaken s t1 in
    let* id_kp s' := add_old_var x (mkdecl an None t1) s in
    binder an t1' (t2 id_kp s').

  Definition it_kp_binder : context -> option ident -> state -> (list ident -> state -> term) -> term :=
    fun cxt x => fold_left_state
    (fun _ cdecl s t =>
      let '(mkdecl an db ty) := cdecl in
      match db with
      | None => kp_binder an ty x s t
      | Some db => kp_tLetIn an db ty s t
      end) cxt.

  Definition closure_uparams : kername -> state -> (list ident -> state -> term) -> term :=
    fun kname s => it_kp_binder (get_uparams kname s) (Some "uparams") s.

  Definition closure_nuparams : kername -> state -> (list ident -> state -> term) -> term :=
    fun kname s => it_kp_binder (get_nuparams kname s) (Some "nuparams") s.

  Definition closure_params : kername -> state -> (list ident -> state -> term) -> term :=
  fun kname s => it_kp_binder (get_params kname s) (Some "params") s.

  Definition mk_binder : aname -> term -> option ident -> state -> (ident -> state -> term) -> term :=
    fun an t1 x s t2 =>
      let* id_mk s := add_fresh_var x (mkdecl an None t1) s in
      binder an t1 (t2 id_mk s).

  Definition it_mk_binder : context -> option ident -> state -> (list ident -> state -> term) -> term :=
    fun cxt x => fold_left_state
    (fun _ cdecl s t =>
      let '(mkdecl an db ty) := cdecl in
      match db with
      | None => mk_binder an ty x s t
      | Some db => mk_tLetIn an db ty s t
      end) cxt.

  Definition closure_indices : kername -> nat -> state -> (list ident -> state -> term) -> term :=
    fun kname pos_indb s => it_mk_binder (get_indices kname pos_indb s) (Some "indices") s.

  Definition closure_binder {A} (x : option ident) (l : list A)
    (naming : nat -> A -> aname) (typing : nat -> A -> state -> term) :
    state -> (list ident -> state -> term) -> term :=
    fold_right_state
      (fun n a s t => mk_binder (naming n a) (typing n a s) x s t)
      l .

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
    fun pos_indb => "F" ^ (snd kname) ^ string_of_nat pos_indb.

  #[local] Definition tFix_aname : nat -> aname :=
    fun pos_indb => mkBindAnn (nNamed (tFix_name pos_indb)) Relevant.

  #[local] Definition tFix_context : state -> context :=
    fun s => rev ( mapi
    (fun pos_indb _ => mkdecl (tFix_aname pos_indb) None (tFix_type pos_indb))
    (get_ind_bodies kname s)).

  Definition mk_tFix : nat -> state -> (list ident -> nat -> state -> term) -> term :=
    fun focus s tmc =>
    let* id_fix s_Fix := add_fresh_context (Some "tFix") (tFix_context s) s in
    tFix
      (mapi (fun pos_indb _ =>
        mkdef _ (tFix_aname pos_indb)
                (tFix_type  pos_indb)
                (tmc id_fix pos_indb s_Fix)
                (tFix_rarg  pos_indb))
            (get_ind_bodies kname s))
      focus.

End mk_tFix.

Definition tFix_default_rarg : kername -> state -> nat -> nat :=
  fun kname s pos_indb => get_nb_nuparams kname s + length (get_indices kname pos_indb s).



(* 5. Make Match *)
Section MktCase.
  Context (kname : kername).
  Context (pos_indb : nat).
  Context (mk_case_pred : list ident -> ident -> state -> term).
  Context (id_uparams id_nuparams : list ident).

  #[local] Definition mk_case_info : state -> case_info :=
    fun s => mk_case_info (mkInd kname pos_indb) (get_nb_params kname s) Relevant.

  #[local] Definition mk_pred : state -> predicate term :=
    fun s =>
    let* id_findices sPred := add_fresh_context None (get_indices kname pos_indb s) s in
    let fVarMatch := (mkdecl (mkBindAnn nAnon Relevant) None
          (make_ind kname pos_indb id_uparams id_nuparams id_findices sPred)) in
    let* id_fVarMatch sPred := add_fresh_var (Some "fresh var match") fVarMatch sPred in
    mk_predicate []
      (get_terms id_uparams s ++ get_terms id_nuparams s)
      (get_aname id_fVarMatch sPred :: get_anames id_findices sPred)
      (mk_case_pred id_findices id_fVarMatch sPred).

  Definition mk_tCase : term -> state -> (nat -> list ident
    -> list ident -> list ident -> state -> term) -> term :=
    fun tm_match s branch =>
    tCase (mk_case_info s) (mk_pred s) tm_match
      (mapi (fun pos_ctor ctor =>
        let* id_lets id_args id_lets_args s :=
            add_old_context (Some ("args_" ^ snd kname)) ctor.(cstr_args) s in
        mk_branch (rev (get_anames id_lets_args s))
                  (branch pos_ctor id_lets id_args id_lets_args s))
      (get_indb kname pos_indb s).(ind_ctors)).

End MktCase.