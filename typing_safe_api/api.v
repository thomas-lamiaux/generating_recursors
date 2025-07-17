From Stdlib Require Export List.
Export ListNotations.

From MetaRocq.Utils Require Export utils.

From Stdlib Require Export ssreflect ssrbool ssrfun Morphisms Setoid.
(* From MetaRocq.Common Require Import BasicAst Primitive Universes Environment. *)
(* From Equations.Prop Require Import Classes EqDecInstances. *)
(* From Coq Require Import List. *)

From MetaRocq.Utils Require Export utils.
From MetaRocq.PCUIC Require Export
  PCUICAst PCUICTyping PCUICSubstitution PCUICAstUtils PCUICOnFreeVars PCUICOnFreeVarsConv
  PCUICInstDef PCUICOnFreeVars PCUICSigmaCalculus PCUICInstConv PCUICConfluence
  PCUICNamelessDef.
Import PCUICEnvironment.

From MetaRocq.PCUIC Require Import PCUICTactics.


Record imp_mdecl : Type := mk_pdecl
{
  state_uparams     : context ;
  state_nb_uparams  : nat ;
  state_nuparams    : context ;
  state_nb_nuparams : nat ;
  state_mdecl       : mutual_inductive_body ;
}.

Section GetInds.

  Context (pdecl : imp_mdecl).

  Definition get_uparams : context :=
    pdecl.(state_uparams).

  Definition get_nb_uparams : nat :=
    pdecl.(state_nb_uparams).

  Definition get_nuparams : context :=
    pdecl.(state_nuparams).

  Definition get_nb_nuparams : nat :=
    pdecl.(state_nb_nuparams).

  Definition get_params : context :=
    pdecl.(state_mdecl).(ind_params).

  Definition get_nb_params : nat :=
    pdecl.(state_mdecl).(ind_npars).

  Definition get_mdecl : mutual_inductive_body :=
    pdecl.(state_mdecl).

  Definition get_ind_bodies : list one_inductive_body :=
    pdecl.(state_mdecl).(ind_bodies).

  Definition get_all_args : list context :=
    map cstr_args (concat (map ind_ctors get_mdecl.(ind_bodies))).

  #[local] Definition ERROR_GET_INDB : one_inductive_body :=
    Build_one_inductive_body "ERROR GET_INDB" [] sProp (tVar "ERROR GET_INDB") IntoAny [] [] Relevant.

  Context (pos_indb : nat).

  Definition get_indb : one_inductive_body :=
    nth pos_indb get_ind_bodies ERROR_GET_INDB.

  Definition get_relevance : relevance :=
    get_indb.(ind_relevance).

  #[local] Definition ERROR_GET_CTOR : constructor_body :=
    Build_constructor_body "ERROR GET CTOR" [] [] (tVar "ERROR GET CTOR") 0.

  Definition get_ctors : list constructor_body :=
    get_indb.(ind_ctors).

  Context (pos_ctor : nat).

  Definition get_ctor : constructor_body :=
    nth pos_ctor get_indb.(ind_ctors) ERROR_GET_CTOR.

  Definition get_args : context :=
    get_ctor.(cstr_args).

  Definition get_indices : context :=
    get_indb.(ind_indices).

  Definition get_ctor_indices : list term :=
    get_ctor.(cstr_indices).

End GetInds.

(* Aux Functions *)

Definition mkApp u v := mkApps u [v].

Notation "let* x .. z ':=' c1 'in' c2" := (c1 (fun x => .. (fun z => c2) ..))
(at level 100, x binder, z binder, c1 at next level, right associativity).

(*

#############################
###   Backend interface   ###
#############################

*)


Axiom (Σ : global_env_ext).
Axiom todo: forall {A}, A.

Existing Instance config.strictest_checker_flags.
(* Print subslet.
Check cons_let_ass.
Search "subslet". *)
(* Check subslet_well_subst. *)

Definition wf_subst Γ Δ σ : Type :=
  forall t T, Σ ;;; Γ |- t : T -> Σ ;;; Δ |- (subst0 σ t) : (subst0 σ T).

Record state : Type := mk_state
{ state_old_context : context;
  state_new_context : context;
  state_subst : list term;
  (* wf cxt and sub *)
  state_wf_oc : wf_local Σ state_old_context;
  state_wf_nc : wf_local Σ state_new_context;
  state_wf_subst : wf_subst state_old_context state_new_context state_subst
}.


Program Definition init_state : state := mk_state [] [] [] _ _ _.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.



(* ### STORE INTERFACE ### *)

(* 1. Add existing var / letin / context *)
Program Definition add_old_cdecl (s : state) (cdecl : context_decl) : state :=
  mk_state (state_old_context s ,, cdecl)
           (state_new_context s ,, map_decl_anon (subst0 s.(state_subst)) cdecl)
           (map (lift0 1) s.(state_subst),, tRel 0)
           (* Proofs *)
           _ _ _.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.

Program Definition add_old_context (s : state) (Δ : context) : state :=
  mk_state (state_old_context s ,,, Δ)
           (state_new_context s ,,, subst_context s.(state_subst) 0 Δ)
           (map (lift0 #|Δ|) s.(state_subst) ,,, mapi (fun i _ => tRel (#|Δ| -i - 1)) Δ)
           (* Proofs *)
           _ _ _.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.

(* 2. Add fresh var / letin / context *)
Program Definition add_fresh_cdecl (s : state) (cdecl : context_decl) : state :=
  mk_state (state_old_context s)
           (state_new_context s ,, cdecl)
           (map (lift0 1) s.(state_subst))
           (* Proofs *)
           _ _ _.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.

Program Definition add_fresh_context (s : state) (Δ : context) : state :=
  mk_state (state_old_context s)
           (state_new_context s ,,, Δ)
           (map (lift0 #|Δ|) s.(state_subst))
           (* Proofs *)
           _ _ _.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.




(*
##############################
###   FrontEnd interface   ###
##############################
 *)

(* ACCESS STATE *)
Definition key := nat.
Definition keys := list nat.
Definition fresh_key : state -> key :=
  fun s => #|s.(state_new_context)|.
Definition fresh_keys : state -> nat -> keys :=
  fun s length => List.rev (seq #|s.(state_new_context)| length).

(* 1.0 Local functions geting term and type with shifted *)
Definition lift_cdecl : nat -> context_decl -> context_decl :=
  fun n ' (mkdecl an x ty) => mkdecl an (option_map (lift0 n) x) (lift0 n ty).

#[local] Definition ERROR_CDECL : context_decl :=
  mkdecl (mkBindAnn nAnon Relevant) None (tVar "error_get_sdecl").

#[local] Definition get_cdecl : state -> key -> context_decl :=
  fun s k =>
  let n' := length (state_new_context s) - k -1 in
  lift_cdecl n' (nth n' (state_new_context s) ERROR_CDECL).

(* Genereric get functions *)
Section Get.

  Context {X : Type}.
  Context (f : nat -> context_decl -> X).

  #[local] Definition get_X : state -> key -> X :=
    fun s k => f (#|state_new_context s| - k -1) (get_cdecl s k).

  #[local] Definition get_Xs : state -> keys -> list X :=
  fun s ks => map (fun k => get_X s k) ks.

End Get.


(* 1.1 Get terms *)
#[local] Definition get_sdecl_term : nat -> context_decl -> term :=
  fun n ' (mkdecl _ bd _) =>
  match bd with
  | Some tm => lift0 1 tm
  | None => tRel n
  end.

Definition get_term := get_X get_sdecl_term.
Definition get_terms := get_Xs get_sdecl_term.

(* 1.2 Get types *)
#[local] Definition get_sdecl_type : nat -> context_decl -> term :=
  fun _ ' (mkdecl _ _ ty) => lift0 1 ty.

Definition get_type   := get_X   get_sdecl_type.
Definition get_types  := get_Xs  get_sdecl_type.








(* MAKE TERMS *)
Definition kp_binder binder : state -> aname -> term -> (state -> key -> term) -> term :=
  fun s an A cc =>
  let A' := subst0 s.(state_subst) A in
  let s' := add_old_cdecl s (vass an A) in
  let key_bind := fresh_key s in
  binder an A' (cc s' key_bind).

Definition kp_tProd := kp_binder tProd.
Definition kp_tLambda := kp_binder tLambda.

Definition mk_binder binder : state -> aname -> term -> (state -> key -> term) -> term :=
  fun s an A cc =>
  let s' := add_fresh_cdecl s (vass an A) in
  let key_bind := fresh_key s in
    binder an A (cc s key_bind).

Definition mk_tProd := mk_binder tProd.
Definition mk_tLambda := mk_binder tLambda.

Definition it_kp_mkProd_or_LetIn : state -> context -> (state -> list key -> term) -> term :=
  fun s Δ cc =>
    let s' := add_old_context s Δ in
    let key_context := fresh_keys s #|Δ| in
    it_mkProd_or_LetIn (subst_context s.(state_subst) 0 Δ) (cc s' key_context).


(* closure functions *)
Definition closure_params : state -> imp_mdecl -> (state -> list key -> term) -> term :=
  fun s pdecl => it_kp_mkProd_or_LetIn s (get_params pdecl).

Definition closure_uparams : state -> imp_mdecl -> (state -> list key -> term) -> term :=
  fun s pdecl => it_kp_mkProd_or_LetIn s (get_uparams pdecl).

Definition closure_nuparams : state -> imp_mdecl -> (state -> list key -> term) -> term :=
  fun s pdecl => it_kp_mkProd_or_LetIn s (get_nuparams pdecl).

Definition closure_indices : state -> imp_mdecl -> nat -> (state -> list key -> term) -> term :=
  fun s pdecl pos_indb => it_kp_mkProd_or_LetIn s (get_indices pdecl pos_indb).


Unset Guard Checking.

Section GenRecursors.

Context (kname : kername).
Context (pdecl : imp_mdecl).
Context (nb_uparams : nat).
Context (E : global_env).

Definition gen_rec_type (pos_indb : nat) : term :=
  (* to deal with  *)
  let s := init_state in
  (* let* s := subst_ind s kname in *)
  let* s key_uparams  := closure_uparams s pdecl in
  let* s key_nuparams := closure_nuparams s pdecl in
  let* s key_indices  := closure_indices  s pdecl pos_indb in
  tProd (mkBindAnn nAnon Relevant)
        (mkApps (tInd (mkInd kname pos_indb) [])
          (get_terms s key_uparams ++ get_terms s key_nuparams ++ get_terms s key_indices))
        (tSort sProp).

Definition closure_uparams_ty s cc :
  let s' := add_old_context s (get_uparams pdecl) in
  let fcxt := subst_context s.(state_subst) 0 (get_uparams pdecl) in
  Σ ;;; s.(state_new_context) ,,, fcxt |- cc s' (fresh_keys s #|get_uparams pdecl|) : tSort sProp ->
  Σ ;;; s.(state_new_context) |- (let* s key_uparams := closure_uparams s pdecl in
                                cc s key_uparams) : tSort sProp.
Proof.
  unfold closure_uparams.
  intros H.
Admitted.

Definition gen_rec_wt (pos_indb : nat) :
  Σ ;;; [] |- gen_rec_type pos_indb : (tSort sProp).
Proof.
  unfold gen_rec_type.
  change (@nil context_decl) with (init_state.(state_new_context)).
  apply closure_uparams_ty. cbn.
Admitted.