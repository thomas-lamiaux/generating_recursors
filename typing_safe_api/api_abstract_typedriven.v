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
  PCUICNamelessDef PCUICLiftSubst PCUICInstTyp PCUICInversion PCUICValidity.
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

Definition lift_tSort n k so : tSort so = lift n k (tSort so) := eq_refl.


(* On Typing *)
Definition isSort {cf : config.checker_flags} Σ Γ T s :=
  (lift_typing typing) Σ Γ (TypUniv T s).

Definition isProp {cf : config.checker_flags} Σ Γ T :=
  @isSort cf Σ Γ T sProp.

Definition has_sort_TypUniv {cf : config.checker_flags} Σ Γ T s :
  Σ ;;; Γ |- T : tSort s -> isSort Σ Γ T s :=
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

Definition well_subst_vass {cf : config.checker_flags} {Σ : global_env_ext}
  (wfΣ :wf Σ) {Γ : context} {Δ : list context_decl} {σ : nat -> term} {na : aname} {A : term}:
  wf_local Σ (Δ,, vass na A) ->
  Σ ;;; Δ ⊢ σ : Γ ->
  Σ ;;; Δ,, vass na A ⊢ σ ∘s ↑^1 : Γ.
Proof.
  intros wf_loc [typ_σ usubst_σ]. constructor.
  + intros n cdecl in_cdecl.
    unfold "∘s". rewrite -inst_assoc. rewrite -!lift0_inst.
    eapply PCUICWeakeningTyp.weakening with (Γ' := [vass na A]) => //=.
    eapply typ_σ => //.
  + unfold usubst in *. cbn in *.
    intros n cdecl inΓ bd incdecl.
    specialize (usubst_σ n cdecl inΓ bd incdecl).
    all: unfold "∘s"; rewrite -!inst_assoc.
    destruct usubst_σ as [[n' [cdecl' [-> [incdecl' rn]]]] | Y].
    - left. exists (S n'), cdecl'. repeat split => //=.
      destruct cdecl' as [? [bd' |]]; cbn in * => //.
      f_equal. rewrite -(PCUICRenameConv.rename_compose (fun n => 1 + n)).
      injection rn; clear rn; intros ->.
      rewrite rename_inst. rewrite -inst_assoc. done.
    - right. rewrite Y. rewrite -!inst_assoc. done.
Qed.




(*

#############################
###   Backend interface   ###
#############################

*)
Existing Instance config.strictest_checker_flags.
Identity Coercion id : context >-> list.

Axiom (Σ : global_env_ext).
Axiom (wfΣ : wf Σ).
Existing Instance wfΣ.

Record state : Type := mk_state
{ state_old_context : context;
  state_new_context :> context;
  state_subst : substitutionT;
  (* wf cxt and sub *)
  (* state_wf_oc : wf_local Σ state_old_context; *)
  state_wf_nc : wf_local Σ state_new_context;
  state_wf_subst : Σ ;;; state_new_context ⊢ state_subst : state_old_context
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

Notation "∅" := init_state.

(* ### TERMS INTERFACE ### *)
Definition oldType : state -> Type :=
  fun s => ∑ (T : term) (so : sort), Σ ;;; state_old_context s |- T : tSort so.

(* Well-defined terms *)
Definition dSort : state -> Type :=
  fun s => ∑ (si so : sort), Σ ;;; s |- tSort si : tSort so.

Definition dType : state -> Type :=
  fun s => ∑ (T : term) (so : sort), Σ ;;; s |- T : tSort so.

Definition eType : state -> sort -> Type :=
  fun s so => ∑ (T : term), Σ ;;; s |- T : tSort so.

Definition dTerm : state -> Type :=
  fun s => ∑ (t T : term), Σ ;;; s |- t : T.

Definition eTerm : state -> term -> Type :=
  fun s T => ∑ (t : term), Σ ;;; s |- t : T.



(* Coercions  *)
Definition dSort_to_dType {s} : dSort s -> dType s :=
  fun ' x => (tSort x.π1; x.π2.π1; x.π2.π2).

Coercion dSort_to_dType : dSort >-> dType.

Definition dType_to_dTerm {s} : dType s -> dTerm s :=
  fun x => (x.π1; tSort x.π2.π1; x.π2.π2).

Coercion dType_to_dTerm : dType >-> dTerm.

Definition eType_to_dType {s T} : eType s T -> dType s :=
  fun x => (x.π1; T; x.π2).

Coercion eType_to_dType : eType >-> dType.

Definition eTerm_to_dTerm {s T} : eTerm s T -> dTerm s :=
  fun x => (x.π1; T; x.π2).

Coercion eTerm_to_dTerm : eTerm >-> dTerm.

Definition eType_to_eTerm {s T} : eType s T -> eTerm s (tSort T) :=
  fun ' x => (x.π1; x.π2).

Coercion eType_to_eTerm : eType >-> eTerm.


(* ### STORE INTERFACE ### *)
(* Program Definition add_old_vass (s : state) (na : aname) (A : oldType s) : state :=
  let x := _ in
  mk_state (state_old_context s ,, vass na A.π1)
           (state_new_context s ,, vass na A.π1.[s.(state_subst)])
           (⇑ s.(state_subst))
           (* Proofs *)
          x _.
Next Obligation.
  intros s na [A [sA typA]].
  constructor. apply state_wf_nc.
  eapply lift_typing_inst with (j := Typ _); tea.
  all: try apply s. exact _.
  eapply has_sort_isType. tea.
Qed.
Next Obligation.
  intros s na [A [sA typA]] x.
  apply well_subst_Up; tea.
  apply state_wf_subst.
Qed. *)


Definition dVass : state -> Type :=
  fun s => ∑ (na : aname), dType s.

Program Definition add_fresh_vass (s : state) (decl : dVass s) : state :=
  let x := _ in
  mk_state (state_old_context s)
           (state_new_context s ,, vass decl.π1 decl.π2.π1)
           ( (s.(state_subst)) ∘s ↑^1)
           (* Proofs *)
           x _.
Next Obligation.
  intros s [na [A [sA typA]]].
  constructor. apply s. eapply has_sort_isType, typA.
Qed.
Next Obligation.
  intros s [na [A [sA typA]]] wf_locΣ'.
  apply well_subst_vass => //=. apply wfΣ. apply s.
Qed.

Infix "▸" := add_fresh_vass (left associativity, at level 24).


(* ************************************************************************** *)
(* ************************************************************************** *)
(* ************************************************************************** *)
(* ************************************************************************** *)
(* ************************************************************************** *)




(*
##############################
###  Access Terms & Types  ###
##############################
*)


(* ### STATE INCLUSION + TYPECLASS ### *)

Definition state_in (s1 s2 : state) :=
  ∑ Δ, s1.(state_new_context) ,,, Δ = s2.(state_new_context).


(* Class Structure *)
Class IsIncluded (s s' : state) : Type := is_included : state_in s s'.
Infix "⊑" := IsIncluded (at level 25).
Set Typeclasses Depth 5.

Definition IsIncluded_trans {s1 s2 s3} : s1 ⊑ s2 -> s2 ⊑ s3 -> s1 ⊑ s3.
Proof.
  intros [Δ1 H1] [Δ2 H2].
  exists (Δ1 ,,, Δ2). rewrite app_context_assoc.
  rewrite H1 H2. done.
Defined.

(* #[global] Hint Mode IsIncluded_trans + - + - - : typeclass_instances. *)

Definition state_in_trans_length (s1 s2 s3 : state) (ins1 : s1 ⊑ s2) (ins2 : s2 ⊑ s3):
  #|(IsIncluded_trans ins1 ins2).π1| = #|ins1.π1| + #|ins2.π1|.
Proof.
  destruct ins1, ins2. cbn. len.
Qed.

Definition IsIncluded_refl (s : state) : s ⊑ s := ([]; eq_refl).

#[global] Hint Mode IsIncluded_refl + : typeclass_instances.

(* UIP *)
Definition state_in_uip {s1 s2 : state} (ins1 ins2 : s1 ⊑ s2): ins1 = ins2.
  destruct ins1 as [Δ1 eqΔ1], ins2 as [Δ2 eqΔ2].
  unshelve eapply eq_existT_curried.
  + rewrite -eqΔ1 in eqΔ2. apply app_inv_tail in eqΔ2. done.
  + apply EqDec.eqdec_uip. exact _.
Qed.


(* Compatibility with backend *)
(* Definition add_old_vass_in {s na A} : s ⊑ (add_old_vass s na A).
Proof.
  exists ([vass na A.π1.[s.(state_subst)]]). done.
Defined. *)

Definition add_fresh_vass_in {s decl} : s ⊑ s ▸ decl.
Proof.
  exists ([vass decl.π1 decl.π2.π1]). done.
Defined.


(* functoriality / weakening *)
Program Definition weaken_dSort {s1} s2 {ins: s1 ⊑ s2} : dSort s1 -> dSort s2 :=
  fun x => (x.π1; x.π2.π1; _).
Next Obligation.
  intros s1 s2 [Δ eqΔ] (si & so & typ). cbn.
  change (tSort si) with (lift0 #|Δ| (tSort si)).
  change (tSort so) with (lift0 #|Δ| (tSort so)).
  rewrite -eqΔ.
  apply PCUICWeakeningTyp.weakening; tea.
  + exact _.
  + rewrite eqΔ. apply s2.
Defined.

Program Definition weaken_dType {s1} s2 {ins: s1 ⊑ s2} : dType s1 -> dType s2 :=
  fun x => (lift0 #|ins.π1| x.π1; x.π2.π1; _).
Next Obligation.
  intros s1 s2 [Δ eqΔ] (T & sT & typT). cbn.
  change (tSort sT) with (lift0 #|Δ| (tSort sT)).
  rewrite -eqΔ.
  apply PCUICWeakeningTyp.weakening; tea.
  + exact _.
  + rewrite eqΔ. apply s2.
Defined.

Program Definition weaken_eType {s1} s2 {ins: s1 ⊑ s2} {T} : eType s1 T -> eType s2 T :=
  fun x => (lift0 #|ins.π1| x.π1; _).
Next Obligation.
  intros s1 s2 [Δ eqΔ] T [t typt]. cbn.
  change (tSort T) with (lift0 #|Δ| (tSort T)).
  rewrite -eqΔ.
  apply PCUICWeakeningTyp.weakening; tea.
  + exact _.
  + rewrite eqΔ. apply s2.
Defined.

Program Definition weaken_dTerm {s1} s2 {ins: s1 ⊑ s2} : dTerm s1 -> dTerm s2 :=
  fun x => (lift0 #|ins.π1| x.π1; lift0 #|ins.π1| x.π2.π1; _).
Next Obligation.
  intros s1 s2 [Δ eqΔ] (t & T & typt). cbn.
  rewrite -eqΔ.
  apply PCUICWeakeningTyp.weakening; tea.
  + exact _.
  + rewrite eqΔ. apply s2.
Defined.

Program Definition weaken_eTerm {s1} s2 {ins: s1 ⊑ s2} {T} : eTerm s1 T -> eTerm s2 (lift0 #|ins.π1| T):=
  fun x => (lift0 #|ins.π1| x.π1; _).
Next Obligation.
  intros s1 s2 [Δ eqΔ] T [t typt]. cbn.
  rewrite -eqΔ.
  apply PCUICWeakeningTyp.weakening; tea.
  + exact _.
  + rewrite eqΔ. apply s2.
Defined.






(*
##############################
###   Make Types & Terms   ###
##############################
*)

(* ### Notations  ### *)
Notation "let* x .. z ':=' c1 'in' c2" := (c1 (fun _ => (fun x => .. (fun z => c2) ..)))
(at level 100, x binder, z binder, c1 at next level, right associativity).

(* Notation "let# x .. z ':=' c1 'in' c2" := (c1 (fun x => .. (fun z => c2) ..))
(at level 100, x binder, z binder, c1 at next level, right associativity). *)

Notation "sProp+" := (Sort.super sProp).
Definition Anon := (mkBindAnn nAnon Relevant).

(* ### Make Sort  ### *)
Program Definition mk_Prop {s} : dSort s :=
  (sProp; sProp+; _).
Next Obligation.
  intros s. apply type_Sort.
  + apply s.
  + constructor.
Qed.

Definition tyVar {s1 s2 x} := @weaken_dType s1 s2 x.
Definition tmVar {s1 s2 x} := @weaken_dTerm s1 s2 x.


(* ### Make Types  ### *)

(* Definition kp_Prod (s : state) (na : aname) (A : oldType s)
  (cc : forall s' (ins : s ⊑ s') (k : skey s'), dType s') :
  dType s.
Proof.
  destruct (cc (add_old_vass s na A) add_old_vass_in add_old_vass_skey) as [B [sB typB]].
  destruct A as [A [sA typA]].
  exists (tProd na A.[state_subst s] B). exists (Sort.sort_of_product sA sB).
  (* Proof Derivation: *)
  eapply type_Prod => //=.
  eapply lift_typing_inst with (j := TypUniv _ _). all: try apply s. 1:exact _.
  apply has_sort_TypUniv. tea.
Defined. *)

Program Definition mk_Prod_Sort {s} (A : dSort s) (decl := (Anon; A) : dVass s)
  (cc : forall decl (k : eType (s ▸ decl) A.π1), dType (s ▸ decl)) :
  dType s :=
  let B := (cc decl _) in
  (tProd Anon (tSort A.π1) B.π1; Sort.sort_of_product A.π2.π1 B.π2.π1 ; _).
Next Obligation.
  intros. all: destruct A as [si [sA typA]]; cbn in *.
  exists (tRel 0).
  change (tSort si) with (lift0 1 (tSort si)).
  eapply meta_conv. eapply type_Rel; cbn. 2-3: reflexivity.
  apply (s ▸ decl).
Defined.
Next Obligation.
  intros. cbn beta.
  destruct B as [B [sB typB]]; cbn beta in *.
  destruct A as [si [so typA]]; cbn beta in *.
  eapply type_Prod => //.
  eapply has_sort_TypUniv => //.
Defined.

Program Definition mk_Prod {s} (A : dType s) (decl := (Anon; A) : dVass s)
  (cc : forall decl, eTerm (s ▸ decl) (lift0 1 A.π1) -> dType (s ▸ decl)) :
  dType s :=
  let B := (cc decl _) in
  (tProd Anon A.π1 B.π1; Sort.sort_of_product A.π2.π1 B.π2.π1 ; _).
Next Obligation.
  intros. exists (tRel 0).
  eapply meta_conv. unshelve eapply type_Rel; cbn.
  - exact (vass Anon A.π1).
  - apply (s ▸ decl).
  - reflexivity.
  - reflexivity.
Defined.
Next Obligation.
  intros. cbn beta.
  destruct B as [B [sB typB]]; cbn beta in *.
  destruct A as [A [sA typA]]; cbn beta in *.
  eapply type_Prod => //.
  eapply has_sort_TypUniv => //.
Defined.

(* Record Pack_dTerm s : Type := pack_dTerm {
  packed_state : state;
  packed_inc   : packed_state ⊑ s;
  packed_term  :> dTerm packed_state;
}.

Arguments pack_dTerm {_ _ _} _. *)

(* Coercion pack_dTerm : dTerm >-> Pack_dTerm. *)

Inductive state_spine (s : state) : term -> list (dTerm s) -> Type :=
| state_spine_nil : state_spine s (tSort sProp) []
| state_spine_cons :
    forall (A : term) (B : term),
    forall (hd : dTerm s) (eq : hd.π2.π1 = A) (tl : list (dTerm s)),
    state_spine s (B {0 := hd.π1}) tl ->
    state_spine s (tProd Anon A B) (hd :: tl).

Definition mk_Apps_sort
  {s} (f : dTerm s)
  (args : list (dTerm s))
  (typ_args : state_spine s (f.π2.π1) args) :
  dType s.
Proof.
  destruct f as (f & Tf & typf); cbn in *.
  induction typ_args as [| A B hd eq tl typ_B] in f, typf |- *.
  + exists f, sProp. tea.
  + destruct (validity typf) as [_ [so [typ_Prod _]]]. cbn in *.
    eapply inversion_Prod in typ_Prod => //=. 2: apply wfΣ.
    destruct typ_Prod as [sA [sB [typA [typB l]]]].
      (* rec *)
    eapply IHtyp_B with (tApp f hd.π1).
    eapply type_App with (na := Anon) (A := A) (s := Sort.sort_of_product sA sB).
    all:tea.
    eapply type_Prod => //=.
    rewrite -eq. eapply hd.π2.π2.
Qed.

(* ### Make Terms  ### *)
(* Definition kp_Lambda (s : state) (na : aname) (A : oldType s)
  (cc : forall s' (ins : s ⊑ s') (k : tkey s'), dTerm s') :
  dTerm s.
Proof.
  destruct(cc (add_old_vass s na A) add_old_vass_in add_old_vass_tkey) as [t [B typB]].
  destruct A as [A [sA typA]].
  exists (tLambda na A.[state_subst s] t). exists (tProd na A.[state_subst s] B).
  (* Proof Derivation: *)
  eapply type_Lambda => //.
  eapply lift_typing_inst with (j := Typ _). all: try apply s. 1:exact _.
  eapply has_sort_isType. tea.
Defined. *)

(* Program Definition mk_Lambda_Sort {s1 s2} {ins : s1 ⊑ s2}
  (old_A : dSort s1) (A := @weaken_dSort s1 s2 ins old_A) (s3 := add_fresh_vass s2 Anon A)
  (cc : forall s3 (ins : s2 ⊑ s3) (k : eType s3 old_A.π1), dTerm s3) :
  dTerm s2 :=
  let B := (cc s3 add_fresh_vass_in _) in
  (tLambda Anon (tSort A.π1) B.π1; tProd Anon (tSort A.π1) B.π2.π1 ; _).
Next Obligation.
  intros. all: destruct old_A as [si [sA typA]]; cbn in *.
  exists (tRel 0).
  change (tSort si) with (lift0 1 (tSort si)).
  eapply meta_conv. eapply type_Rel; cbn. 2-3: reflexivity.
  apply s3.
Defined.
Next Obligation.
  intros. cbn beta.
  destruct B as [t [B typB]]; cbn beta in *.
  destruct A as [si [so typA]]; cbn beta in *. cbn.
  eapply type_Lambda => //.
  eapply has_sort_isType => //. tea.
Defined. *)

(* Program Definition mk_Lambda {s1 s2} {ins1 : s1 ⊑ s2}
  (old_A : dType s1) (A := @weaken_dType s1 s2 ins1 old_A) (s3 := add_fresh_vass s2 Anon A)
  (cc : forall s3 (ins2 : s2 ⊑ s3), eTerm s3 (lift_ins ins2 A.π1) -> dTerm s3) :
  dTerm s2 :=
  let B := (cc s3 add_fresh_vass_in _) in
  (tLambda Anon A.π1 B.π1; tProd Anon A.π1 B.π2.π1 ; _).
Next Obligation.
  intros. exists (tRel 0).
  eapply meta_conv. eapply type_Rel; cbn. 2-3: reflexivity. apply s3.
Defined.
Next Obligation.
  intros. cbn beta.
  destruct B as [B [sB typB]]; cbn beta in *.
  destruct A as [A [sA typA]]; cbn beta in *.
  eapply type_Lambda => //.
  eapply has_sort_isType => //. tea.
Defined. *)

(*
(* forall (A : Prop) (P : A -> Prop) (a : A), P a : Prop *)
Definition mk_App (s : state) (f a : term) (na : aname) (A : term) (B : term)
  (typu : Σ ;;; s |- f : tProd na A B)
  (typv : Σ ;;; s |- a : A) :
  dTerm s.
Proof.
  exists (tApp f a). exists (B {0 := a}).
  destruct (validity typu) as [_ [so [typ_Prod _]]]. cbn in *.
  eapply type_App; tea.
Defined.
 *)



(* ************************************************************************** *)
(* ************************************************************************** *)
(* ************************************************************************** *)
(* ************************************************************************** *)
(* ************************************************************************** *)

Ltac ssrdone3 :=
  repeat (
      match goal with
      | |- context[lift0 ?n (lift0 ?k ?M)] => rewrite (lift0_add n k M)
      end
  )
  ; try lia; try done.

Ltac econstructor2 :=
  tryif solve [econstructor]
  then idtac "done"
  else (econstructor; only 2: econstructor2).

#[local] Obligation Tactic :=
  try solve [intros; cbn; try econstructor2; move => /= /3/].


(*
#############################
###     Applications 1    ###
#############################
*)

(* type class solve *)
Ltac solve_in :=
  match goal with
  | [ |- ?s ⊑ ?s] => eapply IsIncluded_refl
  | [ |- ?s ⊑ ?s1 ▸ ?d] => eapply IsIncluded_trans; only 2: eapply add_fresh_vass_in; solve_in
  end.

Hint Extern 3 => solve_in : typeclass_instances.

Set Typeclasses Debug Verbosity 2.



(* forall (A : Prop) (P : A -> Prop) (a : A), P a : Prop *)
Time Program Definition type_inhabited : dTerm ∅ :=
  let* A := mk_Prod_Sort mk_Prop in
  let* P := mk_Prod (let* a := mk_Prod (tyVar A) in mk_Prop) in
  let* a := mk_Prod (tyVar A) in
  mk_Apps_sort (tmVar P) [tmVar a] _.


Definition simpl_subst_inf (N : list term) (M : term) (k p : nat):
  #|N| <= p -> subst N k (lift p k M) = (lift (p - #|N|) k M).
Proof.
Admitted.

(* ∀ (eq : forall A : Prop, A -> A -> Prop)
   ∀ (A : Prop) (P : A → Prop) (x y : A),
   x = y → P x → P y
*)
Time Program Definition type_transport : dType ∅ :=
  let* eq := mk_Prod (
    (* forall A : Prop, A -> A -> Prop : Prop+ *)
    let* A := mk_Prod_Sort mk_Prop in
    let* x := mk_Prod (tyVar A) in
    let* y := mk_Prod (tyVar A) in
    mk_Prop
    ) in
  let* A := mk_Prod_Sort mk_Prop in
  let* P := mk_Prod (let* a := mk_Prod (tyVar A) in mk_Prop) in
  let* x := mk_Prod (tyVar A) in
  let* y := mk_Prod (tyVar A) in
  let* eqxy := mk_Prod (mk_Apps_sort (tmVar eq) [tmVar A; tmVar x; tmVar y] _) in
  let* Px := mk_Prod (mk_Apps_sort (tmVar P) [tmVar x] _) in
  mk_Apps_sort (tmVar P) [tmVar y] _.
    (* ### Proof Derivation ### *)
Next Obligation.
  intros deq eq dA A declP P dx x dy y. cbn in *.
  econstructor2; fold lift subst; unfold Nat.sub ; move => /= /3/.
  rewrite simpl_subst_inf /3/=.
Time Qed.


(*
#############################
###     Applications 3    ###
#############################
*)


Definition relation : Type -> Type :=
  fun A => A -> A -> Type.

Program Definition body_relation : dTerm ∅ :=
  let* A := mk_Lambda_Sort mk_Prop in
  dType_to_dTerm (
    let* x := mk_Prod A in
    let* x := mk_Prod A in
    mk_Prop
  ).

Definition reflexive : forall A (R : A -> A -> Type), Type :=
  fun A R => forall x y, R x y -> R y x.

Program Definition body_reflexive : dTerm ∅ :=
  let* A := mk_Lambda_Sort mk_Prop in
  let* R := mk_Lambda (
    let* _ := mk_Prod A in
    let* _ := mk_Prod A in
    mk_Prop
    ) in
  dType_to_dTerm (
    let* x := mk_Prod A in
    let* y := mk_Prod A in
    let* Rxy := mk_Prod (mk_Apps_sort R [x; y] _) in
    mk_Apps_sort R [y; x] _
  ).
Next Obligation.
  intros s0 ins0 A s1 ins1 R s2 ins2 x s3 ins3 y. cbn in *.
  econstructor2. all : fold lift subst; repeat rewrite ?lift0_id => /3/.
  + rewrite (simpl_lift _ 1 0); try lia. rewrite Nat.add_comm simpl_lift0.
    rewrite (simpl_lift _ 1 0); try lia. rewrite Nat.add_comm simpl_lift0.
    rewrite simpl_subst_k => /3/.
Qed.
Next Obligation.
  intros s0 ins0 A s1 ins1 R s2 ins2 x s3 ins3 y s4 ins4 _. cbn in *.
  econstructor2. all : fold lift subst; repeat rewrite ?lift0_id => /3/.
  + rewrite (simpl_lift _ 1 0); try lia. rewrite Nat.add_comm simpl_lift0.
    rewrite (simpl_lift _ 1 0); try lia. rewrite Nat.add_comm simpl_lift0.
    rewrite simpl_subst_k => /3/.
Qed.



(*
#############################
###     Applications 4    ###
#############################
*)

(*
  basic K combinator, you need a weakening
  in all previous examples this was done by app
*)

(* fun (A : Prop) (x y : A) => x *)
Definition k_combinator : dTerm ∅ :=
  let* A := mk_Lambda_Sort mk_Prop in
  let* x := mk_Lambda A in
  let* y := mk_Lambda A in
  weaken_dTerm _ x.













(* Definition kp_binder binder (s : state):  -> aname -> term -> (state -> tkey -> term) -> term :=
  fun s an A cc =>
  let A' := subst0 s.(state_subst) A in
  let s' := add_old_cdecl s (vass an A) in
  let key_bind := fresh_key s in
  binder an A' (cc s' key_bind).

Definition kp_Prod := kp_binder tProd.
Definition kp_tLambda := kp_binder tLambda.

Definition mk_binder binder : state -> aname -> term -> (state -> tkey -> term) -> term :=
  fun s an A cc =>
  let s' := add_fresh_cdecl s (vass an A) in
  let key_bind := fresh_key s in
    binder an A (cc s key_bind).

Definition mk_Prod := mk_binder tProd.
Definition mk_tLambda := mk_binder tLambda.

Definition it_kp_mk_Prod_or_LetIn : state -> context -> (state -> list tkey -> term) -> term :=
  fun s Δ cc =>
    let s' := add_old_context s Δ in
    let key_context := fresh_keys s #|Δ| in
    it_mk_Prod_or_LetIn (subst_context s.(state_subst) 0 Δ) (cc s' key_context). *)


(* closure functions *)
(* Definition closure_params : state -> imp_mdecl -> (state -> list tkey -> term) -> term :=
  fun s pdecl => it_kp_mk_Prod_or_LetIn s (get_params pdecl).

Definition closure_uparams : state -> imp_mdecl -> (state -> list tkey -> term) -> term :=
  fun s pdecl => it_kp_mk_Prod_or_LetIn s (get_uparams pdecl).

Definition closure_nuparams : state -> imp_mdecl -> (state -> list tkey -> term) -> term :=
  fun s pdecl => it_kp_mk_Prod_or_LetIn s (get_nuparams pdecl).

Definition closure_indices : state -> imp_mdecl -> nat -> (state -> list tkey -> term) -> term :=
  fun s pdecl pos_indb => it_kp_mk_Prod_or_LetIn s (get_indices pdecl pos_indb). *)


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

