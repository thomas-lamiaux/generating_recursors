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


(* ### TERMS INTERFACE ### *)
Definition oldType : state -> Type :=
  fun s => ∑ (T : term) (so : sort), Σ ;;; state_old_context s |- T : tSort so.

(* Well-defined terms *)
Definition dSort : state -> Type :=
  fun s => ∑ (si so : sort), Σ ;;; s |- tSort si : tSort so.

Definition dType : state -> Type :=
  fun s => ∑ (T : term) (so : sort), Σ ;;; s |- T : tSort so.

Definition dTerm : state -> Type :=
  fun s => ∑ (t T : term), Σ ;;; s |- t : T.

(* Coercions  *)
Definition dSort_to_DType {s} : dSort s -> dType s :=
  fun ' (si; so; typ) => (tSort si; so; typ).

Coercion dSort_to_DType : dSort >-> dType.

Definition dType_to_dTerm {s} : dType s -> dTerm s :=
  fun ' (t; so; typ) => (t; tSort so; typ).

Coercion dType_to_dTerm : dType >-> dTerm.



(* ### STORE INTERFACE ### *)
Program Definition add_old_vass (s : state) (na : aname) (A : oldType s) : state :=
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
Qed.

Program Definition add_fresh_vass (s : state) (na : aname) (A : dType s) : state :=
  let x := _ in
  mk_state (state_old_context s)
           (state_new_context s ,, vass na A.π1)
           ( (s.(state_subst)) ∘s ↑^1)
           (* Proofs *)
           x _.
Next Obligation.
  intros s na [A [sA typA]].
  constructor. apply s. eapply has_sort_isType, typA.
Qed.
Next Obligation.
  intros s na [A [sA typA]] wf_locΣ'.
  apply well_subst_vass => //=. apply wfΣ. apply s.
Qed.





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

Class IsIncluded (s s' : state) : Type := is_included : state_in s s'.
Infix "⊑" := IsIncluded (at level 25).
Set Typeclasses Depth 5.

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

Instance IsIncluded_refl (s : state) : s ⊑ s.
Proof.
  exists ([]). done.
Qed.

#[global] Hint Mode IsIncluded_refl + : typeclass_instances.

(* Compatibility with backend *)
Definition add_old_vass_in {s na A} : s ⊑ (add_old_vass s na A).
Proof.
  exists ([vass na A.π1.[s.(state_subst)]]). done.
Defined.

Definition add_fresh_vass_in {s na A} : s ⊑ (add_fresh_vass s na A).
Proof.
  exists ([vass na A.π1]). done.
Defined.





(*
#############################
###      Access key       ###
#############################
*)


(* ### to recover types ### *)
Definition val_tel {A} {l : list A} : {n : nat | n < #|l| } -> {n : nat | n < #|l| }.
Proof.
  intros [k infk]. exists (#|l| -k -1). lia.
Defined.

Record skey (s : state) : Type := mk_skey {
  skey_val : nat ;
  skey_inf : skey_val < #|s|;
  skey_isSort : ∑ so, decl_type (safe_nth (state_new_context s) (val_tel (exist skey_val skey_inf))) = tSort so
}.

Arguments mk_skey {s} _ _ _.
Arguments skey_val {s} _.
Arguments skey_inf {s} _.
Arguments skey_isSort {s} _.

Program Definition weaken_skey {s1 s2} (ins : s1 ⊑ s2) : skey s1 -> skey s2 :=
  fun ' (mk_skey k infk (so; k_isSort)) => mk_skey k _ _.
Next Obligation.
  intros. destruct ins as [? e]. rewrite -e. len.
Qed.
Next Obligation.
  intros. exists so.
Admitted.

Definition get_type_aux s (k : skey s) : dType s.
Proof.
  destruct k as [k infk [so k_isSort]].
  exists (tRel (#|s| -k -1)).
  exists so.
  eapply meta_conv; only 1: eapply type_Rel.
  + apply s.
  + apply nth_error_safe_nth.
  + change (tSort so) with (lift0 (S (#|s| - k - 1)) (tSort so)).
    rewrite -k_isSort. repeat f_equal. unfold val_tel. f_equal.
Defined.

Definition get_type {s1} s2 {ins: s1 ⊑ s2} (k : skey s1) : dType s2.
Proof.
  eapply get_type_aux. eapply weaken_skey; tea.
Defined.

Program Definition add_old_vass_skey {s na A} : skey (add_old_vass s na A) :=
  (mk_skey #|s| _ _).
Next Obligation.
  cbn. intros. apply Nat.lt_succ_diag_r.
Qed.
Next Obligation.
  intros s na [A [sA typA]].
  exists sA.
Admitted.

Program Definition add_fresh_vass_skey {s na} {A : dSort s} :
  skey (add_fresh_vass s na A) :=
  (mk_skey #|s| _ _).
Next Obligation.
  cbn. intros. apply Nat.lt_succ_diag_r.
Qed.
Next Obligation.
  intros s na [si [so typA]].
  set mm := (val_tel _).
  pose H := @exist _ (fun n => n < #|add_fresh_vass s na (tSort si; so; typA) |) 0 todo.
  replace mm with H by admit.
  unfold H. cbn. exists si. done.
Admitted.


(* ### To recover terms #### *)
Definition tkey s := ∑ (n : nat), n < #|state_new_context s|.

Program Definition weaken_tkey {s1 s2} (ins : s1 ⊑ s2) : tkey s1 -> tkey s2 :=
  fun ' (existT k infk) => (k; _).
Next Obligation.
  intros s1 s2 [Δ <-] **. len.
Qed.

Definition get_term_aux s (k : tkey s) : dTerm s.
Proof.
  destruct k as [k infk].
  exists (tRel (#|s| -k -1)). eexists.
  unshelve eapply type_Rel.
  + exact (safe_nth s (val_tel (exist k infk))).
  + apply s.
  + apply nth_error_safe_nth.
Defined.

Definition get_term {s1} s2 {ins: s1 ⊑ s2} (k : tkey s1) : dTerm s2.
Proof.
  eapply get_term_aux. eapply weaken_tkey; tea.
Defined.

Program Definition add_old_vass_tkey {s na A} : tkey (add_old_vass s na A) :=
  (#|s|; _).
Next Obligation.
  cbn. intros. apply Nat.lt_succ_diag_r.
Qed.

Program Definition add_fresh_vass_tkey {s na A} : tkey (add_fresh_vass s na A) :=
  (#|s|; _).
Next Obligation.
  cbn. intros. apply Nat.lt_succ_diag_r.
Qed.


(* ### Else ### *)
Definition skey_in_tkey {s} : skey s -> tkey s :=
  fun ' (mk_skey k infk l) => (k; infk).




(*
#############################
###      Lift and PP      ###
#############################
*)

Definition lift_ins {s1 s2} (ins : s1 ⊑ s2) t := lift0 #|ins.π1| t.
Notation "{ s1 ⊏ s2 } ↑ t" := ( @lift_ins s1 s2 _ t) (at level 10).

Definition lift_ins_unfold {s1 s2} (ins : s1 ⊑ s2) t :
  lift_ins ins t = lift0 #|ins.π1| t :=
  eq_refl.

Notation "ins1 & ins2" := (IsIncluded_trans ins1 ins2) (at level 10).

(* Solver for lifts to eq on nat  *)
Ltac solve_lift :=
  rewrite ?lift_ins_unfold;
  repeat (rewrite state_in_trans_length ?lift0_add -?app_context_length);
  len.

(* to simplify lift directly *)
Definition lift_in_comp_l s1 s2 s3 (ins1 : s1 ⊑ s2) (ins2 : s2 ⊑ s3) t :
  lift_ins ins2 (lift_ins ins1 t) = lift_ins (ins1 & ins2) t.
Proof.
  solve_lift.
Qed.

Definition lift_in_comp_r s1 s2 s3 (ins1 : s1 ⊑ s2) (ins2 : s2 ⊑ s3) t :
  lift_ins ins1 (lift_ins ins2 t) = lift_ins (ins1 & ins2) t.
Proof.
  solve_lift.
Qed.

Definition IsIncluded_assoc s1 s2 s3 s4 (ins1 : s1 ⊑ s2) (ins2 : s2 ⊑ s3) (ins3 : s3 ⊑ s4) :
  ins1 & (ins2 & ins3) = (ins1 & ins2) & ins3.
Proof.
Admitted.

Definition IsIncluded_refl_l s1 s2 (ins1 : s1 ⊑ s2) :
  ins1 & (IsIncluded_refl s2) = ins1.
Proof.
Admitted.

Definition IsIncluded_refl_r s1 s2 (ins1 : s1 ⊑ s2) :
  (IsIncluded_refl s1) & ins1 = ins1.
Proof.
Admitted.

(* collapse composition of lift + simplify comp and refl of IsIncluded *)
Ltac collapse_comp :=
  repeat (rewrite ?lift_in_comp_l ?lift_in_comp_r
            ?IsIncluded_assoc ?IsIncluded_refl_l ?IsIncluded_refl_r).

(* simplify to normal form *)
Ltac simpl_lift :=
  (* to make it compute *)
  rewrite ?lift_ins_unfold /= -?lift_ins_unfold;
  (* to simplify *)
  collapse_comp;
  (* why not *)
  try solve [done].



(*
##############################
###   Make Types & Terms   ###
##############################
*)

Notation "let* x .. z ':=' c1 'in' c2" := (c1 (fun x => .. (fun z => c2) ..))
(at level 100, x binder, z binder, c1 at next level, right associativity).

Notation "sProp+" := (Sort.super sProp).
Definition Anon := (mkBindAnn nAnon Relevant).

(* ### Make Sort  ### *)
Program Definition mk_Prop (s : state) : dSort s :=
  (sProp; sProp+; _).
Next Obligation.
  intros s. apply type_Sort.
  + apply s.
  + constructor.
Qed.




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

Definition mk_Prod_Sort (s : state) (na : aname) (A : dSort s)
  (cc : forall s' (ins : s ⊑ s') (k : skey s'), dType s') :
  dType s.
Proof.
  destruct(cc (add_fresh_vass s na A) add_fresh_vass_in add_fresh_vass_skey) as [B [sB typT]].
  destruct A as [si [sA typA]].
  exists (tProd na (tSort si) B). exists (Sort.sort_of_product sA sB).
  (* Proof Derivation: *)
  eapply type_Prod => //.
  eapply has_sort_TypUniv. tea.
Defined.

Definition mk_Prod (s : state) (na : aname) (A : dType s)
  (cc : forall s' (ins : s ⊑ s') (k : tkey s'), dType s') :
  dType s.
Proof.
  destruct(cc (add_fresh_vass s na A) add_fresh_vass_in add_fresh_vass_tkey) as [B [sB typT]].
  destruct A as [A [sA typA]].
  exists (tProd na A B). exists (Sort.sort_of_product sA sB).
  (* Proof Derivation: *)
  eapply type_Prod => //.
  eapply has_sort_TypUniv. tea.
Defined.

Definition mk_App_type (s : state) (f a : term) (na : aname) (A : term) (sOut : sort)
  (typu : Σ ;;; s |- f : tProd na A (tSort sOut))
  (typv : Σ ;;; s |- a : A) :
  dType s.
Proof.
  exists (tApp f a), sOut.
  destruct (validity typu) as [_ [so [typ_Prod _]]]. cbn in *.
  change (tSort _) with ((tSort sOut) {0 := a}).
  eapply type_App; tea.
Defined.

(*
Inductive state_spine (s : state) : term -> list term -> Type :=
| state_spine_nil : state_spine s (tSort sProp) []
| state_spine_cons :
    forall (hd : term) (tl : list term) (na : aname) (A B : term),
    Σ ;;; state_new_context s |- hd : A ->
    state_spine s (B {0 := hd}) tl ->
    state_spine s (tProd na A B) (hd :: tl).

Definition mk_Apps_sort (s : state) (f : term) ty_f (la : list term)  :
  Σ ;;; state_new_context s |- f : ty_f ->
  state_spine s ty_f la ->
  ∑ (T : term) sT, Σ ;;; (state_new_context s) |- T : tSort sT.
Proof.
  intros X typ_args.
  induction typ_args as [| hd tl na A B typ_hd typ_args IH_typ_args] in f,X |- *.
  + exists f, sProp. done.
  + (* Get sort + Type Deriv for A and B *)
    destruct (validity X) as [_ [so [typ_Prod _]]]. cbn in *.
    eapply inversion_Prod in typ_Prod => //=. 2: apply wfΣ.
    destruct typ_Prod as [sA [sB [typA [typB l]]]].
    (* rec *)
    eapply IH_typ_args with (tApp f hd).
    eapply type_App with (na := na) (A := A) (s := Sort.sort_of_product sA sB).
    all:tea.
    eapply type_Prod => //=.
Defined.
*)

(* ### Make Terms  ### *)
Definition kp_Lambda (s : state) (na : aname) (A : oldType s)
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
Defined.

Definition mk_Lambda_Sort (s : state) (na : aname) (A : dSort s)
  (cc : forall s' (ins : s ⊑ s') (k : skey s'), dTerm s') :
  dTerm s.
Proof.
  destruct(cc (add_fresh_vass s na A) add_fresh_vass_in add_fresh_vass_skey) as [t [B typB]].
  destruct A as [si [sA typA]].
  exists (tLambda na (tSort si) t). exists (tProd na (tSort si) B).
  (* Proof Derivation: *)
  eapply type_Lambda => //.
  eapply has_sort_isType. tea.
Defined.

Definition mk_Lambda (s : state) (na : aname) (A : dType s)
  (cc : forall s' (ins : s ⊑ s') (k : tkey s'), dTerm s') :
  dTerm s.
Proof.
  destruct(cc (add_fresh_vass s na A) add_fresh_vass_in add_fresh_vass_tkey) as [t [B typB]].
  destruct A as [A [sA typA]].
  exists (tLambda na A t). exists (tProd na A B).
  (* Proof Derivation: *)
  eapply type_Lambda => //.
  eapply has_sort_isType. tea.
Defined.


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




(* ************************************************************************** *)
(* ************************************************************************** *)
(* ************************************************************************** *)
(* ************************************************************************** *)
(* ************************************************************************** *)

Notation "let* x y .. z ':=' c1 'in' c2" := (c1 (fun x => fun _ => (fun y => .. (fun z => c2) ..)))
(at level 100, x binder, y binder, z binder, c1 at next level, right associativity).

(* Notation "let* x .. z ':=' c1 'in' c2" := (c1 (fun s ins x => .. (fun z => c2) ..))
(at level 100, x binder, z binder, c1 at next level, right associativity). *)

(* Ltac ssrdone3 := simpl_lift.

(* To replace a goal Σ ;;; Δ |- get_term s k : T  with get_type s k = T *)
Ltac replace_type :=
  match goal with
  | [ |- typing Σ ?Δ (get_term ?s ?k) ?T ] =>
        let H := fresh "H" in
        eenough (H : _ = T);
        [ erewrite <- H; apply well_type_get | idtac]
  end.

Definition well_type_get_lift {s1 s2 s3} (k : tkey s1) {ins1 : s1 ⊑ s2} (ins2 : s2 ⊑ s3)  :
    Σ ;;; state_new_context s3 |- lift_ins ins2 (get_term s2 k) : lift_ins ins1 (get_type s2 k).
Proof.
Admitted.

Ltac replace_type_lift :=
  match goal with
  | [ |- typing Σ ?Δ (lift_ins ?ins2 (get_term ?s ?k)) ?T ] =>
        let H := fresh "H" in
        eenough (H : _ = T);
        [ erewrite <- H; apply (well_type_get_lift k ins2) | idtac]
  end. *)

#[local] Obligation Tactic := cbn [projT1] => //.


(*
#############################
###     Applications 1    ###
#############################
*)

Search lift typing.
(* PCUICWeakeningTyp.weakening: *)

(* TermTyped s T -> Term s
: state -> term -> Type := ∑ t, Σ ;;; s |- t : T. *)
Program Definition weaken_dType {s1} s2 {ins: s1 ⊑ s2} : dType s1 -> dType s2 :=
  fun ' (T; so; typT) => (lift0 #|ins.π1| T; so; _).
Next Obligation.
  intros s1 s2 [Δ eqΔ] **. cbn.
  change (tSort so) with (lift0 #|Δ| (tSort so)).
  rewrite -eqΔ.
  apply PCUICWeakeningTyp.weakening; tea. exact _. rewrite eqΔ.
  apply s2.
Defined.

(* forall (A : Prop) (P : A -> Prop) (a : A), P a : Prop *)
Program Definition type_inhabited : ∑ T sT, Σ ;;; [] |- T : tSort sT :=
  let s := init_state in
  let* s A := mk_Prod_Sort s Anon (mk_Prop s) in
  let* s P := mk_Prod s Anon (
    let* s a := mk_Prod s Anon (get_type s A) in mk_Prop s) in
  let* s a := mk_Prod s Anon (get_type s A) in
  _.

  (* mk_App_sort s (get_term s P) (get_term s a) Anon (get_term s A) sProp _ _. *)
    (* ### Proof Derivation ### *)


Next Obligation.
  intros.
Admitted.

(* Proof Derivation: P *)
(* Proof Derivation: P a *)
(* Next Obligation.
  intros. replace_type. rewrite P.(gty) /3/. f_equal.
  rewrite (get_term_in A s) /3/.
Qed.
Next Obligation. (* type deriv: get_term s A *)
  intros. replace_type. rewrite a.(gty).
  rewrite (get_term_in A s) (get_term_in A s2) /3/.
Qed. *)

(*
#############################
###     Applications 2    ###
#############################
*)

(* ∀ (eq : forall A : Prop, A -> A -> Prop)
   ∀ (A : Prop) (P : A → Prop) (x y : A),
   x = y → P x → P y
*)
Program Definition type_transport : ∑ T sT, Σ ;;; [] |- T : tSort sT :=
  let s := init_state in
  let* s eq := mk_Prod s Anon (
    (* forall A : Prop, A -> A -> Prop : Prop+ *)
    let* s A := mk_Prod_Sort s Anon (mk_Prop s) in
    let* s x := mk_Prod s Anon (get_type s A) in
    let* s y := mk_Prod s Anon (get_type s A) in
    (mk_Prop s)
    ) in
  let* s A := mk_Prod_Sort s Anon (mk_Prop s) in
  let* s P := mk_Prod s Anon (
    let* s a := mk_Prod s Anon (get_type s A) in (mk_Prop s)) in
  let* s x := mk_Prod s Anon (get_type s A) in
  let* s y := mk_Prod s Anon (get_type s A) in
  todo.
  (* let* s eq_xy := mk_Prod s Anon (
    mk_Apps_sort s (get_term s eq) (get_type s eq)
              [get_term s A; get_term s x; get_term s y] _ _) in
  let* s px := mk_Prod s Anon (
      mk_Apps_sort s (get_term s P) (get_type s P) [get_term s x] _ _
    ) in
  mk_Apps_sort s (get_term s P) (get_type s P) [get_term s y] _ _. *)
    (* ### Proof Derivation ### *)
(* Proof Derivation: eq *)
(* Proof Derivation: eq x y *)
(* Next Obligation.
  intros. rewrite eq.(gty) /3/.
  repeat constructor; simpl; fold subst; clear eq.
  + replace_type. rewrite A.(gty) /3/.
  + rewrite lift0_id. replace_type. rewrite x.(gty).
    rewrite (get_term_in A) (get_term_in A s) /3/.
  + rewrite simpl_subst_k //=. replace_type. rewrite y.(gty).
    rewrite (get_term_in A s4) (get_term_in A s) /3/.
Qed.
(* Type Derive P x *)
Next Obligation. (* type: get_term s P *)
  intros. rewrite P.(gty) /3/. repeat constructor.
  replace_type. rewrite x.(gty) (get_term_in A s3) /3/.
Qed.
(* Type Derive P y *)
Next Obligation. (* type: get_term s P *)
  intros. rewrite P.(gty) /3/. repeat constructor.
  replace_type. rewrite y.(gty) /3/.
  rewrite (get_term_in A s4) /3/.
Qed. *)


(*
#############################
###     Applications 3    ###
#############################
*)


Definition relation : Type -> Type :=
  fun A => A -> A -> Type.

Program Definition body_relation : ∑ t T, Σ ;;; [] |- t : T :=
  let s := init_state in
  let* s A := mk_Lambda_Sort s Anon (mk_Prop s) in
  dType_to_dTerm (
    let* s x := mk_Prod s Anon (get_type s A) in
    let* s x := mk_Prod s Anon (get_type s A) in
    mk_Prop s
  ).

Definition reflexive : forall A (R : A -> A -> Type), Type :=
  fun A R => forall x y, R x y -> R y x.

Program Definition body_reflexive : ∑ t T, Σ ;;; [] |- t : T :=
  let s := init_state in
  let* s A := mk_Lambda_Sort s Anon (mk_Prop s) in
  let* s R := mk_Lambda s Anon (
    let* s _ := mk_Prod s Anon (get_type s A) in
    let* s _ := mk_Prod s Anon (get_type s A) in
    mk_Prop s
    ) in
  dType_to_dTerm (
    let* s x := mk_Prod s Anon (get_type s A) in
    let* s y := mk_Prod s Anon (get_type s A) in
    todo).
    (* let* s Rxy := mk_Prod s Anon todo
      (mk_Apps_sort s (get_term s R) (get_type s R) [get_term s x; get_term s y] _ _)
      in
    mk_Apps_sort s (get_term s R) (get_type s R) [get_term s y; get_term s x] _ _
  ). *)
(* Next Obligation.
  intros s0 ins0 A s1 ins1 R s2 ins2 x s3 ins3 y.
  rewrite R.(gty) /3/. repeat constructor; fold subst; clear R.
  + replace_type. rewrite x.(gty). rewrite (get_term_in A) /3/.
  (* tedious ! *)
  + replace_type.
    set s1' := (add_fresh_vass _ _ _ _). rewrite (get_term_in A s1') /3/.
    (* simplify subst and lift *)
    rewrite simpl_lift; try lia. rewrite Nat.add_comm.
    rewrite -(simpl_lift _ _ _ _ 0); try lia.
    rewrite simpl_subst_k //=.
    (* conclude *)
    rewrite y.(gty) /3/. rewrite (get_term_in A) /3/.
Qed.
Next Obligation.
  intros. rewrite R.(gty) /3/. repeat constructor; fold subst.
  + replace_type. rewrite y.(gty). rewrite (get_term_in A) /3/.
  + replace_type.
    set s1' := (add_fresh_vass _ _ _ _). rewrite (get_term_in A s1') /3/.
    (* simplify subst and lift *)
    rewrite simpl_lift; try lia. rewrite Nat.add_comm.
    rewrite -(simpl_lift _ _ _ _ 0); try lia.
    rewrite simpl_subst_k //=.
    (* conclude *)
    rewrite x.(gty) /3/. rewrite (get_term_in A) /3/.
Qed. *)




















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

