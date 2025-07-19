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
  PCUICNamelessDef PCUICLiftSubst PCUICInstTyp.
Import PCUICEnvironment.

From MetaRocq.PCUIC Require Import PCUICTactics.


(* PRELIMINARIES *)
#[local] Obligation Tactic := idtac.

Definition lift_cdecl : nat -> context_decl -> context_decl :=
  fun n ' (mkdecl an x ty) => mkdecl an (option_map (lift0 n) x) (lift0 n ty).

Definition lift0_add n m t : lift0 n (lift0 m t) = lift0 (n + m) t.
Proof.
  apply simpl_lift; lia.
Qed.

Axiom todo: forall {A}, A.


(* On Typing *)
Definition isSort {cf : config.checker_flags} Σ Γ T s :=
  (lift_typing typing) Σ Γ (TypUniv T s).

Definition isProp {cf : config.checker_flags} Σ Γ T :=
  @isSort cf Σ Γ T sProp.

Definition has_sort_TypUniv {cf : config.checker_flags} Σ Γ T s :
  Σ;;; Γ |- T : tSort s -> isSort Σ Γ T s :=
  fun H => (tt, (s ; (H, eq_refl))).

Definition isSort_to_isType {cf : config.checker_flags} {Σ Γ T so} :
  isSort Σ Γ T so -> isType Σ Γ T.
Proof.
  unfold isProp, isSort, isType, lift_typing0, on_type, lift_sorting. cbn.
  intros [_ [so' [H p]]].
  exact (tt, (so' ; (H, tt))).
Qed.

Lemma lift_typing_inst {cf : config.checker_flags} Σ Γ Δ σ j {wfΣ : wf Σ.1} :
  wf_local Σ Δ ->
  Σ ;;; Δ ⊢ σ : Γ ->
  lift_typing typing Σ Γ j ->
  lift_typing typing Σ Δ (judgment_map (inst σ) j).
Proof.
  intros wfΓ Hs HT.
  apply lift_typing_f_impl with (1 := HT) => // ?? Ht.
  eapply typing_inst in Ht; tea.
Qed.



(*

#############################
###   Backend interface   ###
#############################

*)
Existing Instance config.strictest_checker_flags.

Axiom (Σ : global_env_ext).
Axiom (wfΣ : wf Σ).
Existing Instance wfΣ.

Record state : Type := mk_state
{ state_old_context : context;
  state_new_context : context;
  state_subst : substitutionT;
  (* wf cxt and sub *)
  (* state_wf_oc : wf_local Σ state_old_context; *)
  state_wf_nc : wf_local Σ state_new_context;
  state_wf_subst : Σ;;; state_new_context ⊢ state_subst : state_old_context
}.

Program Definition init_state : state := mk_state [] [] (fun n => tRel n) _ _.
Next Obligation.
  constructor.
Qed.
Next Obligation.
  constructor.
  + intros n decl H. rewrite nth_error_nil in H. done.
  + intros n decl H. rewrite nth_error_nil in H. done.
Qed.





(* ### STORE INTERFACE ### *)

(* Add existing var / letin / context *)
Program Definition add_old_vass (s : state) (na : aname) (A : term)
    (typA : isType Σ s.(state_old_context) A) : state :=
  let x := _ in
  mk_state (state_old_context s ,, vass na A)
           (state_new_context s ,, vass na A.[s.(state_subst)])
           (⇑ s.(state_subst))
           (* Proofs *)
          x _.
Next Obligation.
  intros s na A typA.
  constructor. apply state_wf_nc.
  change (lift_typing0 (typing Σ (state_new_context s)) (Typ A.[state_subst s]))
  with (isType Σ (state_new_context s) (A.[state_subst s])).
  eapply lift_typing_inst with (j := Typ _); tea.
  all: try apply s. exact _.
Qed.
Next Obligation.
  intros s na A typA x.
  apply well_subst_Up; tea.
  apply state_wf_subst.
Qed.

(* Add fresh var / letin / context *)
Program Definition add_fresh_vass (s : state) (na : aname) (A : term)
  (typA : isType Σ s.(state_new_context) A) : state :=
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


(* ### STATE INCLUSION + TYPECLASS ### *)
Definition state_in (s1 s2 : state) :=
  ∑ Δ, s1.(state_new_context) ,,, Δ = s2.(state_new_context).

Class IsIncluded (s s' : state) : Type := is_included : state_in s s'.
Infix "⊑" := IsIncluded (at level 25).
Set Typeclasses Depth 5.

(*
(* refl *)
Instance IsIncluded_refl (s : state) : s ⊑ s.
Proof.
  exists ([]). done.
Qed.

#[global] Hint Mode IsIncluded_refl + : typeclass_instances.
*)

(* transitivity *)
Instance IsIncluded_trans {s1 s2 s3} : s1 ⊑ s2 -> s2 ⊑ s3 -> s1 ⊑ s3.
Proof.
  intros [Δ1 H1] [Δ2 H2].
  exists (Δ1 ,,, Δ2). rewrite app_context_assoc.
  rewrite H1 H2. done.
Defined.

#[global] Hint Mode IsIncluded_trans + - + - - : typeclass_instances.

Definition state_in_trans_length (s1 s2 s3 : state) (ins1 : s1 ⊑ s2) (ins2 : s2 ⊑ s3):
  #|(IsIncluded_trans ins1 ins2).π1| = #|ins1.π1| + #|ins2.π1|.
Proof.
  destruct ins1, ins2. cbn. len.
Qed.

(* Compatibility with backend *)
Definition add_fresh_vass_in s na A typA : s ⊑ (add_fresh_vass s na A typA).
Proof.
  exists ([vass na A]). done.
Defined.

Definition add_old_vass_in s na A typA : s ⊑ (add_old_vass s na A typA).
Proof.
  exists ([vass na A.[s.(state_subst)]]). done.
Defined.



(* ### ACCESS STATE ### *)
Definition key s := ∑ (n : nat), n < #|state_new_context s| .

Definition mk_key {s} k infk : key s := existT _ k infk.

Program Definition wk_key {s1 s2} (ins : s1 ⊑ s2) : key s1 -> key s2 :=
  fun ' (existT k infk) => mk_key k _.
Next Obligation.
  cbn. intros s1 s2 [Δ <-] **.
  rewrite app_context_length. lia.
Qed.

(* 1.0 Local functions geting term and type with shifted *)
(* #[local] Definition ERROR_CDECL : context_decl :=
  mkdecl (mkBindAnn nAnon Relevant) None (tVar "error_get_sdecl"). *)

#[local] Program Definition get_cdecl s : key s -> context_decl :=
  fun '(existT k infk) =>
  let k' := #|state_new_context s| - k -1 in
  lift_cdecl k' (safe_nth (state_new_context s) (exist k' _)).
Next Obligation.
  cbn. lia.
Qed.

(* Genereric get functions *)
Section Get.

  Context {X : Type}.
  Context (f : nat -> context_decl -> X).

  #[local] Definition get_X : forall s, key s -> X :=
    fun s '(existT k infk) => f (#|state_new_context s| - k -1) (get_cdecl s (mk_key k infk)).

End Get.

(* 1.1 Get terms *)
#[local] Definition get_sdecl_term : nat -> context_decl -> term :=
  fun n ' (mkdecl _ bd _) =>
  match bd with
  | Some tm => lift0 1 tm
  | None => tRel n
  end.

Definition get_term {s1} s2 {ins: s1 ⊑ s2} (k : key s1) : term :=
  get_X get_sdecl_term s2 (wk_key ins k).

(* 1.2 Get types *)
#[local] Definition get_sdecl_type : nat -> context_decl -> term :=
  fun _ cdecl => lift0 1 (decl_type cdecl).

Definition get_type  {s1} s2 {ins: s1 ⊑ s2} (k : key s1) : term :=
  get_X get_sdecl_type s2 (wk_key ins k).

Instance IsIncluded_refl (s : state) : s ⊑ s.
Proof.
  exists ([]). done.
Qed.

#[global] Hint Mode IsIncluded_refl + : typeclass_instances.


(* Properties get_term and get_type *)
Definition well_type_get {s1} s2 {ins : s1 ⊑ s2} (k : key s1) :
    Σ ;;; state_new_context s2 |- get_term s2 k : get_type s2 k.
Proof.
Admitted.

Definition get_term_in {s1} (k : key s1) s2 {ins : s1 ⊑ s2}   :
    get_term s2 k = lift0 #|ins.π1| (get_term s1 k).
Proof.
Admitted.

Definition get_type_in {s1} (k : key s1) s2 {ins : s1 ⊑ s2} :
    get_type s2 k = lift0 #|ins.π1| (get_type s1 k).
Proof.
Admitted.

Program Definition add_old_vass_fresh_key {s na A typA} : key (add_old_vass s na A typA) :=
  mk_key #|state_new_context s| _.
Next Obligation.
  cbn. intros. apply Nat.lt_succ_diag_r.
Qed.

Definition add_old_vass_get_type {s na A typA} :
    get_type (add_old_vass s na A typA) add_old_vass_fresh_key
  = lift0 #|(add_old_vass_in s na A typA).π1| A.[state_subst s].
Proof.
Admitted.

Program Definition add_fresh_vass_fresh_key {s na A typA} : key (add_fresh_vass s na A typA) :=
  mk_key #|state_new_context s| _.
Next Obligation.
  cbn. intros. apply Nat.lt_succ_diag_r.
Qed.

Definition add_fresh_vass_get_type {s na A typA} :
    get_type (add_fresh_vass s na A typA) add_fresh_vass_fresh_key
  = lift0 #|(add_fresh_vass_in s na A typA).π1| A.
Proof.
Admitted.




(* ### MAKE TERMS ### *)
Notation "let* x .. z ':=' c1 'in' c2" := (c1 (fun x => .. (fun z => c2) ..))
(at level 100, x binder, z binder, c1 at next level, right associativity).

Definition sort_of_product_idem_sProp s : Sort.sort_of_product s sProp = sProp := eq_refl.

  (* for the contination ? *)
  (* assert (H : forall s (ins : s1 ⊑ s), get_type s P = lift0 #|(IsIncluded_trans ins1 ins).π1| (tProd Anon (get_term s0 A) (tSort sProp))). *)

Definition kp_tProd (s : state) (na : aname) (A : term) (typA : isType Σ s.(state_old_context) A)
  (cc : forall s' (ins : s ⊑ s') (k : key s'), get_type s' k = lift0 #|ins.π1| A.[state_subst s] ->
    ∑ (t : term), Σ ;;; state_new_context s' |- t : tSort sProp) :
  ∑ t, Σ ;;; state_new_context s |- t : tSort sProp.
Proof.
  pose x := cc (add_old_vass s na A typA) (add_old_vass_in s na A _)
                add_old_vass_fresh_key add_old_vass_get_type.
  destruct x as [T typT].
  exists (tProd na A.[state_subst s] T).
  (* Proof Derivation *)
  cbn in *. destruct typA as [_ [so [typA _]]].
  rewrite -(sort_of_product_idem_sProp so). eapply type_Prod => //=.
  eapply lift_typing_inst with (j := TypUniv _ _). all: try apply s. exact _.
  apply has_sort_TypUniv. tea.
Defined.

Definition mk_tProd (s : state) (na : aname) (A : term) (typA : isType Σ s.(state_new_context) A)
  (cc : forall s' (ins : s ⊑ s') k, get_type s' (k : key s') = lift0 #|ins.π1| A ->
    ∑ (t : term), Σ ;;; state_new_context s' |- t : tSort sProp) :
  ∑ (t : term), Σ ;;; state_new_context s |- t : tSort sProp.
Proof.
 pose x := cc (add_fresh_vass s na A typA) (add_fresh_vass_in s na A typA)
                add_fresh_vass_fresh_key add_fresh_vass_get_type.
  destruct x as [T typT].
  exists (tProd na A T).
  (* Proof Derivation *)
  cbn in *.
  unfold isType, lift_typing0, lift_sorting, on_type in typA. cbn in typA.
  destruct typA as [_ [so [typA _]]].
  change (sProp) with (Sort.sort_of_product so sProp).
  eapply type_Prod; tea.
  eapply has_sort_TypUniv. done.
Defined.

Definition mk_App (s : state) (u v : term) (na : aname) (A : term)
  (typProd : Σ;;; state_new_context s |- A : tSort sProp)
  (typu : Σ;;; s.(state_new_context) |- u : tProd na A (tSort sProp))
  (typv : Σ;;; s.(state_new_context) |- v : A) :
  ∑ t, Σ ;;; state_new_context s |- t : tSort sProp.
Proof.
  exists (tApp u v).
  change (tSort sProp) with ((tSort sProp) {0 := v}).
  eapply type_App with (na := na) (A := A) (s := Sort.super sProp).
  all: tea.
  (* WRITE A BETTER LEMMA? *)
  change (Sort.super sProp) with (Sort.sort_of_product sProp (Sort.super sProp)).
  eassert (H : _). 2:apply type_Prod; only 1: exact H.
  + apply has_sort_TypUniv. done.
  + apply type_Sort.
    pose s3 := (add_fresh_vass s na A (isSort_to_isType H)).
    change (state_new_context s,, vass na A) with (state_new_context s3).
    - apply s3.
    - constructor.
Qed.

Definition Anon := (mkBindAnn nAnon Relevant).




(*
##############################
###      Applications      ###
##############################
*)

(* To replace a goal Σ ;;; Δ |- get_term s k : T  with get_type s k = T *)
Ltac replace_type :=
  match goal with
  | [ |- typing Σ ?Δ (get_term ?s ?k) ?T ] =>
        let H := fresh "H" in
        eenough (H : _ = T);
        [ erewrite <- H; apply well_type_get | idtac]
  end.

(* PP for the lift *)
Notation "'lift_in' ins t" := (lift0 #|ins.π1| t) (at level 10).
Notation "ins '↑' t" := (lift0 #|ins.π1| t) (at level 10).
Notation "ins1 & ins2" := (IsIncluded_trans ins1 ins2) (at level 10).

(* collapse lift to eq on nat  *)
Ltac collapse_lift := repeat (rewrite state_in_trans_length !lift0_add -app_context_length).

(* to simplify lift directly *)
Definition lift_in_comp_l s1 s2 s3 (ins1 : s1 ⊑ s2) (ins2 : s2 ⊑ s3) t :
  ins2 ↑ (ins1 ↑ t) = (ins1 & ins2) ↑ t.
Proof.
  collapse_lift. f_equal. rewrite app_context_length. lia.
Qed.

Definition lift_in_comp_r s1 s2 s3 (ins1 : s1 ⊑ s2) (ins2 : s2 ⊑ s3) t :
  ins1 ↑ (ins2 ↑ t) = (ins1 & ins2) ↑ t.
Proof.
  collapse_lift. f_equal.
Qed.

Definition IsIncluded_assoc s1 s2 s3 s4 (ins1 : s1 ⊑ s2) (ins2 : s2 ⊑ s3) (ins3 : s3 ⊑ s4) :
  ins1 & (ins2 & ins3) = (ins1 & ins2) & ins3.
Proof.
Admitted.

(* collapse the lift to eq of s ⊑ s', better for PP *)
Ltac collapse_comp := repeat (rewrite ?lift_in_comp_l ?lift_in_comp_r ?IsIncluded_assoc).



(* A : Prop *)
(* forall P : A -> Prop *)
(* forall a : A, P a*)
Program Definition foo : ∑ t, Σ ;;; [] |- t : tSort sProp :=
  let s := init_state in
  let* s ins A gty_A := mk_tProd s Anon (tSort sProp) _ in
  let* s ins P gty_P := mk_tProd s Anon (tProd Anon (get_term s A) (tSort sProp)) _ in
  let* s ins a gty_a := mk_tProd s Anon (get_term s A) _ in
  mk_App s (get_term s P) (get_term s a) Anon (get_term s A) _ _ _.
(* Proof Derivation *)
Next Obligation. (* type deriv: Prop *)
  intros s. apply has_sort_isType with (Sort.super sProp).
  apply type_Sort. apply s. constructor.
Qed.
Next Obligation. (* type deriv: P *)
  intros s s0 ins0 A gty_A.
  apply has_sort_isType with (Sort.super sProp).
  change (Sort.super sProp) with (Sort.sort_of_product sProp (Sort.super sProp)).
  eassert (H : _). 2:apply type_Prod; only 1: exact H.
  + apply has_sort_TypUniv. replace_type. rewrite gty_A. cbn. done.
  + apply type_Sort.
    pose s3 := (add_fresh_vass s0 Anon _ (isSort_to_isType H)).
    change (state_new_context s,, vass _ _) with (state_new_context s3).
    - apply s3.
    - constructor.
Qed.
Next Obligation. (* type deriv: A *)
  intros s s0 ins0 A gty_A s1 ins1 P gty_P.
  apply has_sort_isType with sProp.
  replace_type. rewrite get_type_in gty_A /=. done.
Qed.
Next Obligation. (* type deriv: A *)
  intros s s0 ins0 A gty_A s1 ins1 P gty_P s2 ins2 a gty_a.
  replace_type. rewrite get_type_in gty_A /=. done.
Qed.
Next Obligation. (* type deriv: get_term s P *)
  intros s s0 ins0 A gty_A s1 ins1 P gty_P s2 ins2 a gty_a.
  replace_type.
  rewrite (get_type_in P) gty_P /=. f_equal.
  rewrite (get_term_in A s2) /=.
  collapse_comp. done.
Qed.
Next Obligation. (* type deriv: get_term s A *)
  intros s s0 ins0 A gty_A s1 ins1 P gty_P s2 ins2 a gty_a.
  replace_type.
  rewrite gty_a (get_term_in A) (get_term_in A s2).
  collapse_comp. done.
Qed.

































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

