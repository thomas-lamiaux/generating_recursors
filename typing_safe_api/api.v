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

Definition lift_cdecl : nat -> context_decl -> context_decl :=
  fun n ' (mkdecl an x ty) => mkdecl an (option_map (lift0 n) x) (lift0 n ty).



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
Existing Instance config.strictest_checker_flags.

Axiom (Σ : global_env_ext).
Axiom (wfΣ : wf Σ).
Existing Instance wfΣ.
Axiom todo: forall {A}, A.

Print subslet.
Check cons_let_ass.
(* Search "subslet".  *)
Check subslet_well_subst.
Print well_subst.
Print substitutionT.

From MetaRocq.PCUIC Require Import PCUICInstTyp.
Check typing_inst.


(*
Definition wf_subst Γ Δ σ : Type :=
  forall n T, Σ ;;; Γ |- Var n : T -> Σ ;;; Δ |- σ n : (subst0 σ T).

Definition wf_subst Γ Δ σ : Type :=
  forall t T, Σ ;;; Γ |- t : T -> Σ ;;; Δ |- (subst0 σ t) : (subst0 σ T). *)

Record state : Type := mk_state
{ state_old_context : context;
  state_new_context : context;
  state_subst : substitutionT;
  (* wf cxt and sub *)
  (* state_wf_oc : wf_local Σ state_old_context; *)
  state_wf_nc : wf_local Σ state_new_context;
  state_wf_subst : Σ;;; state_new_context ⊢ state_subst : state_old_context
}.


Program Definition init_state : state := mk_state [] [] _ _ _.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.



(* ### STORE INTERFACE ### *)

Print Up.

#[local] Obligation Tactic := idtac.

Lemma lift_typing_inst Γ Δ σ j {wfΣ : wf Σ.1} :
  wf_local Σ Δ ->
  Σ ;;; Δ ⊢ σ : Γ ->
  lift_typing typing Σ Γ j ->
  lift_typing typing Σ Δ (judgment_map (inst σ) j).
Proof.
  intros wfΓ Hs HT.
  apply lift_typing_f_impl with (1 := HT) => // ?? Ht.
  eapply typing_inst in Ht; tea.
Qed.

Definition on_prop :=
  fun (P : global_env_ext -> context -> judgment -> Type) (Σ : global_env_ext)
      (Γ : context) (T : term) => P Σ Γ (TypUniv T sProp).

Definition isProp := fun {H : config.checker_flags} (Σ : global_env_ext) (Γ : context) =>
  fun t => on_prop (lift_typing typing) Σ Γ t.

(* 1. Add existing var / letin / context *)
Program Definition add_old_vass (s : state) (na : aname) (A : term)
    (typA : isProp Σ s.(state_old_context) A) : state :=
  let x := _ in
  mk_state (state_old_context s ,, vass na A)
           (state_new_context s ,, vass na A.[s.(state_subst)])
           (⇑ s.(state_subst))
           (* Proofs *)
          x _.
Next Obligation.
  intros s na A typA.
  constructor. apply state_wf_nc.
  change (lift_typing0 (typing Σ (state_new_context s))
  (Typ A.[state_subst s])) with (isType Σ (state_new_context s) (A.[state_subst s])).
  (* eapply lift_typing_inst with (j := Typ _); tea.
  all: try apply s. exact _. *)
Admitted.
Next Obligation.
  intros s na A typA x.
  apply well_subst_Up; tea.
  apply state_wf_subst.
Qed.

(* 2. Add fresh var / letin / context *)
Program Definition add_fresh_vass (s : state) (na : aname) (A : term)
  (typA : isProp Σ s.(state_new_context) A) : state :=
  let x := _ in
  mk_state (state_old_context s)
           (state_new_context s ,, vass na A)
           ( (s.(state_subst)) ∘s ↑)
           (* Proofs *)
           x _.
Next Obligation.
  intros s na A typA.
  constructor. apply s.
Admitted.
Next Obligation.
  (* intros s na A typeA x.
  (* apply usubst_well_subst. *)
  (* Set Printing All. *)
  constructor.
  - intros n [? bd ty] ins; cbn.
    unfold subst_compose, "↑". cbn.
    admit.
  -
    eassert (X : _).
      eapply snd. eapply s.(state_wf_subst).
    unfold usubst in *.
    intros n cdecl n_in_old ty bd_ty.
    specialize (X n cdecl n_in_old ty bd_ty).
    destruct X as [X | X].
    +
    clear cdecl n_in_old bd_ty.

    destruct X as [n' [cdecl' [n'_in_new [bd eq_bd]]]].
    left.
    exists (S n').
    exists (cdecl').
    split; try split.
    * unfold subst_compose, "↑". rewrite n'_in_new; cbn. done.
    * rewrite nth_error_cons bd. done.
    * destruct cdecl'. destruct decl_body; cbn in *. 2: discriminate.
      f_equal. injection eq_bd; clear eq_bd; intros eq_bd.
      Search subst_compose.
      rewrite -subst_compose_assoc -inst_assoc.
      rewrite -eq_bd.
      Search inst shift.
      Unset Printing Notations.  *)
Admitted.





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

Axiom (in_s : state -> state -> Type).


(* MAKE TERMS *)
Definition kp_tProd (s : state) (na : aname) (A : term) (typA : isProp Σ s.(state_old_context) A)
  (cc : forall (s' : state) (k : key), ∑ (t : term), Σ ;;; state_new_context s' |- t : tSort sProp) :
  let A' := inst s.(state_subst) A in
  let s' := add_old_vass s na A typA in
  let key_bind := fresh_key s in
  ∑ t, Σ ;;; state_new_context s |- t : tSort sProp.
Proof.
  intros A' s' key_bind.
  exists (tProd na A' (projT1 (cc s' key_bind))).
  destruct ((cc s' key_bind)) as [T typT]; cbn in *.
  rewrite -(sort_of_product_idem sProp).
  eapply type_Prod.
  - unfold A'.
    eapply lift_typing_inst with (j := TypUniv _ _); tea.
    all: try apply s. exact _.
  - assumption.
Defined.

Definition mk_tProd (s : state) (na : aname) (A : term) (typA : isProp Σ s.(state_new_context) A)
  (cc : forall (s' : state) (k : key), ∑ (t : term), Σ ;;; state_new_context s' |- t : tSort sProp) :
  let s' := add_fresh_vass s na A typA in
  let key_bind := fresh_key s in
  ∑ t, Σ ;;; state_new_context s |- t : tSort sProp.
Proof.
  intros s' key_bind.
  exists (tProd na A (projT1 (cc s' key_bind))).
  destruct ((cc s' key_bind)) as [T typT]; cbn in *.
  rewrite -(sort_of_product_idem sProp).
  eapply type_Prod.
  - done.
  - assumption.
Defined.

Definition mk_App (s : state) (u v : term) (na : aname) (A : term) U
  (typProd : Σ;;; s.(state_new_context) |- tProd na A (tSort sProp) : tSort U)
  (typu : Σ;;; s.(state_new_context) |- u : tProd na A (tSort sProp))
  (typv : Σ;;; s.(state_new_context) |- v : A) :
  ∑ t, Σ ;;; state_new_context s |- t : tSort sProp.
Proof.
  exists (tApp u v).
  change (tSort sProp) with ((tSort sProp) {0 := v}).
  eapply type_App with (na := na) (A := A) (s := U).
  all: tea.
Qed.

Definition Anon := (mkBindAnn nAnon Relevant).


(* P : forall A, Prop *)
(* forall B,
forall a A, P a *)

Axiom (na nb nP : aname).
Axiom (A B : term).
Axiom (typA : Σ;;; [] |- A : tSort sProp).
Axiom (typB : Σ;;; [vass nP (tProd na A (tSort sProp))] |- B : tSort sProp).
Axiom (U : sort).
Axiom (typSProp : Σ;;; [] |- tSort sProp : tSort U).

(*
A : Prop
B : forall (p : A -> Prop), Prop
---
forall (p : A -> Prop) (b : B P) (a : A), P a
*)

Axiom (wf_state : forall (s : state) (k : key), Σ ;;; state_new_context s |- get_term s k : get_type s k).

Program Definition foo : ∑ t, Σ ;;; [] |- t : tSort sProp :=
  let* s key_p := kp_tProd init_state nP (tProd na A (tSort sProp)) _ in
  let* s key_b := kp_tProd s nb B _ in
  let* s key_a := mk_tProd s na A _ in
  mk_App s (get_term s key_p) (get_term s key_a) Anon A ((Sort.super sProp)) _ _ _.
Next Obligation. (* type deriv: P *)
  admit.
Admitted.
Next Obligation. (* type deriv: B *)
  admit.
Admitted.
Next Obligation. (* type deriv: A *)
  admit.
Admitted.
Next Obligation. (* type deriv: tProd *)
  intros s0 key_P s1 key_B s2 key_A.
  change (Sort.super _) with (Sort.sort_of_product sProp (Sort.super sProp)).
  eapply type_Prod.
  + admit.
  + eapply type_Sort.
    - constructor. apply s2. admit.
Admitted.
Next Obligation. (* type deriv: get_term s P *)
  intros s0 key_P s1 key_B s2 key_A.
  eenough (H : tProd Anon A (tSort sProp) = get_type s2 key_P). erewrite H. apply wf_state.
  admit.
Admitted.
Next Obligation. (* type deriv: get_term s A *)
  intros s0 key_P s1 key_B s2 key_A.
  eenough (H : A = get_type s2 key_A). erewrite H. apply wf_state.
  admit.
Admitted.



(* Definition kp_binder binder (s : state):  -> aname -> term -> (state -> key -> term) -> term :=
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
    it_mkProd_or_LetIn (subst_context s.(state_subst) 0 Δ) (cc s' key_context). *)


(* closure functions *)
(* Definition closure_params : state -> imp_mdecl -> (state -> list key -> term) -> term :=
  fun s pdecl => it_kp_mkProd_or_LetIn s (get_params pdecl).

Definition closure_uparams : state -> imp_mdecl -> (state -> list key -> term) -> term :=
  fun s pdecl => it_kp_mkProd_or_LetIn s (get_uparams pdecl).

Definition closure_nuparams : state -> imp_mdecl -> (state -> list key -> term) -> term :=
  fun s pdecl => it_kp_mkProd_or_LetIn s (get_nuparams pdecl).

Definition closure_indices : state -> imp_mdecl -> nat -> (state -> list key -> term) -> term :=
  fun s pdecl pos_indb => it_kp_mkProd_or_LetIn s (get_indices pdecl pos_indb). *)


(* Unset Guard Checking.

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
        (tSort sProp). *)

