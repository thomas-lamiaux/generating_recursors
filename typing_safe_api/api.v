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





(* PP for lifts *)
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



(* Properties get_term and get_type *)
Definition well_type_get {s1} s2 {ins : s1 ⊑ s2} (k : key s1) :
    Σ ;;; state_new_context s2 |- get_term s2 k : get_type s2 k.
Proof.
Admitted.

Definition get_term_in {s1} (k : key s1) s2 {ins : s1 ⊑ s2}   :
    get_term s2 k = lift_ins ins (get_term s1 k).
Proof.
Admitted.

Definition get_type_in {s1} (k : key s1) s2 {ins : s1 ⊑ s2} :
    get_type s2 k = lift_ins ins (get_type s1 k).
Proof.
Admitted.

Program Definition add_old_vass_fresh_key {s na A typA} : key (add_old_vass s na A typA) :=
  mk_key #|state_new_context s| _.
Next Obligation.
  cbn. intros. apply Nat.lt_succ_diag_r.
Qed.


Definition add_old_vass_get_type {s na A typA} :
  forall s' (ins': add_old_vass s na A typA ⊑ s'),
    get_type s' add_old_vass_fresh_key
  = lift_ins ((add_old_vass_in s na A typA) & ins') A.[state_subst s].
Proof.
Admitted.

Program Definition add_fresh_vass_fresh_key {s na A typA} : key (add_fresh_vass s na A typA) :=
  mk_key #|state_new_context s| _.
Next Obligation.
  cbn. intros. apply Nat.lt_succ_diag_r.
Qed.

Definition add_fresh_vass_get_type {s na A typA} :
  forall s' (ins': add_fresh_vass s na A typA ⊑ s'),
    get_type s' add_fresh_vass_fresh_key
  = lift_ins ((add_fresh_vass_in s na A typA) & ins') A.
Proof.
Admitted.




(* ### MAKE TERMS ### *)
Notation "let* x .. z ':=' c1 'in' c2" := (c1 (fun x => .. (fun z => c2) ..))
(at level 100, x binder, z binder, c1 at next level, right associativity).

Definition sort_of_product_idem_sProp s : Sort.sort_of_product s sProp = sProp := eq_refl.

Notation "sProp+" := (Sort.super sProp).
Notation "sProp2+" := (Sort.super sProp+).
Definition Anon := (mkBindAnn nAnon Relevant).

Definition kp_tProd (s : state) (na : aname) (sA : sort)
  (A : ∑ t, Σ ;;; s.(state_old_context) |- t : tSort sA)
  (sOut : sort) (Hs : Sort.sort_of_product sA sOut = sOut)
  (cc : forall s' (ins : s ⊑ s') (k : key s'),
    (forall s'' (ins' : s' ⊑ s''), get_type s'' k = lift_ins (ins & ins') A.π1.[state_subst s]) ->
    ∑ (t : term), Σ ;;; state_new_context s' |- t : tSort sOut) :
  ∑ t, Σ ;;; state_new_context s |- t : tSort sOut.
Proof.
  destruct A as [A typA].
  destruct (cc (add_old_vass s na A (has_sort_isType sA typA))
      (add_old_vass_in s na A _) add_old_vass_fresh_key add_old_vass_get_type)
    as [T typT].
  exists (tProd na A.[state_subst s] T).
  (* Proof Derivation: *)
  rewrite -Hs. eapply type_Prod => //=.
  eapply lift_typing_inst with (j := TypUniv _ _). all: try apply s. exact _.
  apply has_sort_TypUniv. tea.
Defined.

Definition mk_tProd (s : state) (na : aname) (sA : sort)
  (A : ∑ t, Σ ;;; s.(state_new_context) |- t : tSort sA)
  (sOut : sort) (Hs : Sort.sort_of_product sA sOut = sOut)
  (cc : forall s' (ins : s ⊑ s') k,
    (forall s'' (ins' : s' ⊑ s''), get_type s'' k = lift_ins (ins & ins') A.π1) ->
    ∑ (t : term), Σ ;;; state_new_context s' |- t : tSort sOut) :
  ∑ (t : term), Σ ;;; state_new_context s |- t : tSort sOut.
Proof.
  destruct A as [A typA].
  destruct(cc (add_fresh_vass s na A (has_sort_isType sA typA))
      (add_fresh_vass_in s na A _) add_fresh_vass_fresh_key add_fresh_vass_get_type)
    as [T typT].
  exists (tProd na A T).
  (* Proof Derivation: *)
  rewrite -Hs. eapply type_Prod => //.
  eapply has_sort_TypUniv. done.
Defined.

Definition mk_App (s : state) (f a : term) (na : aname) (sA : sort) (A : term)
  (typProd : Σ;;; state_new_context s |- A : tSort sA)
  (typu : Σ;;; s.(state_new_context) |- f : tProd na A (tSort sProp))
  (typv : Σ;;; s.(state_new_context) |- a : A) :
  ∑ t, Σ ;;; state_new_context s |- t : tSort sProp.
Proof.
  exists (tApp f a).
  change (tSort sProp) with ((tSort sProp) {0 := a}).
  eapply type_App with (na := na) (A := A) (s := Sort.sort_of_product sA sProp+).
  all: tea.
  (* WRITE A BETTER LEMMA? *)
  eassert (H : _). 2:apply type_Prod; only 1: exact H.
  + apply has_sort_TypUniv. done.
  + apply type_Sort.
    pose s3 := (add_fresh_vass s na A (isSort_to_isType H)).
    change (state_new_context s,, vass na A) with (state_new_context s3).
    - apply s3.
    - constructor.
Defined.

Inductive state_spine (s : state) : term -> list term -> Type :=
| state_spine_nil : state_spine s (tSort sProp) []
| state_spine_cons :
    forall (hd : term) (tl : list term) (na : aname) (A B : term),
    Σ ;;; state_new_context s |- hd : A ->
    state_spine s (B {0 := hd}) tl ->
    state_spine s (tProd na A B) (hd :: tl).

Definition mk_Apps (s : state) (f : term) ty_f (la : list term)  :
  Σ ;;; state_new_context s |- f : ty_f ->
  state_spine s ty_f la ->
  ∑ (t : term), Σ;;; (state_new_context s) |- t : tSort sProp.
Proof.
  intros X typ_args.
  induction typ_args as [| hd tl na A B typ_hd typ_args IH_typ_args] in f,X |- *.
  + exists f. done.
  + (* Get sort + Type Deriv for sAB *)
    destruct (validity X) as [_ [so [typ_Prod _]]]. cbn in *.
    eapply inversion_Prod in typ_Prod => //=. 2: apply wfΣ.
    destruct typ_Prod as [sA [sB [typA [typB l]]]].
    (* rec *)
    eapply IH_typ_args with (tApp f hd).
    eapply type_App with (na := na) (A := A) (s := Sort.sort_of_product sA sB).
    all:tea.
    eassert (H : _). 2:eapply type_Prod; only 1: exact H.
    - apply typA.
    - eapply typB.
Qed.

Program Definition mk_sProp (s : state) : ∑ t, Σ ;;; state_new_context s |- t : tSort sProp+ :=
  (tSort sProp; _).
Next Obligation.
  intros s. apply type_Sort.
  + apply s.
  + constructor.
Qed.









(*
#############################
###     Applications 1    ###
#############################
*)

(* To replace a goal Σ ;;; Δ |- get_term s k : T  with get_type s k = T *)
Ltac replace_type :=
  match goal with
  | [ |- typing Σ ?Δ (get_term ?s ?k) ?T ] =>
        let H := fresh "H" in
        eenough (H : _ = T);
        [ erewrite <- H; apply well_type_get | idtac]
  end.


#[local] Obligation Tactic := cbn [projT1]; try done.

(* forall (A : Prop) (P : A -> Prop) (a : A), P a : Prop *)
Program Definition type_inhabited : ∑ t, Σ ;;; [] |- t : tSort sProp :=
  let s := init_state in
  let* s ins A gty_A := mk_tProd s Anon sProp+ (mk_sProp s) sProp _ in
  let* s ins P gty_P := mk_tProd s Anon sProp+ (
      let* s ins a gty_a := mk_tProd s Anon sProp ((get_term s A); _) sProp+ _ in
      mk_sProp s) sProp _ in
  let* s ins a gty_a := mk_tProd s Anon sProp ((get_term s A); _) sProp _ in
  mk_App s (get_term s P) (get_term s a) Anon sProp (get_term s A) _ _ _.
(* Proof Derivation: *)
Next Obligation. (* Type A *)
  intros s0 ins0 A gty_A.
  replace_type. rewrite gty_A /=. simpl_lift.
Qed.
Next Obligation. (* type deriv: A *)
  intros s0 ins0 A gty_A s1 ins1 P gty_P.
 replace_type. rewrite gty_A /=. simpl_lift.
Qed.
Next Obligation.
  intros s0 ins0 A gty_A s1 ins1 P gty_P s2 ins2 a gty_a.
  replace_type. rewrite gty_A /=. simpl_lift.
Qed.
Next Obligation. (* type deriv: get_term s P *)
  intros s0 ins0 A gty_A s1 ins1 P gty_P s2 ins2 a gty_a.
  replace_type. rewrite gty_P. simpl_lift. f_equal.
  rewrite (get_term_in A s2). simpl_lift.
Qed.
Next Obligation. (* type deriv: get_term s A *)
  intros s0 ins0 A gty_A s1 ins1 P gty_P s2 ins2 a gty_a.
  replace_type. rewrite gty_a (get_term_in A) (get_term_in A s2).
  simpl_lift.
Qed.

(*
#############################
###     Applications 2    ###
#############################
*)

Definition well_type_get_lift {s1 s2 s3} (k : key s1) {ins1 : s1 ⊑ s2} (ins2 : s2 ⊑ s3)  :
    Σ ;;; state_new_context s3 |- lift_ins ins2 (get_term s2 k) : lift_ins ins1 (get_type s2 k).
Proof.
Admitted.

Ltac replace_type_lift :=
  match goal with
  | [ |- typing Σ ?Δ (lift_ins ?ins2 (get_term ?s ?k)) ?T ] =>
        let H := fresh "H" in
        eenough (H : _ = T);
        [ erewrite <- H; apply (well_type_get_lift k ins2) | idtac]
  end.

(* ∀ (eq : forall A : Prop, A -> A -> Prop)
   ∀ (A : Prop) (P : A → Prop) (x y : A),
   x = y → P x → P y
*)
Program Definition type_transport : ∑ t, Σ ;;; [] |- t : tSort sProp :=
  let s := init_state in
  let* s ins eq gty_eq := mk_tProd s Anon sProp+ (
    (* forall A : Prop, A -> A -> Prop : Prop+ *)
    let* s ins A gty_A := mk_tProd s Anon sProp+ (mk_sProp s) sProp+ _ in
    let* s ins x gty_x := mk_tProd s Anon sProp (get_term s A; _) sProp+ _ in
    let* s ins y gty_y := mk_tProd s Anon sProp (get_term s A; _) sProp+ _ in
    (mk_sProp s)
  ) sProp _ in
  let* s ins A gty_A := mk_tProd s Anon sProp+ (mk_sProp s) sProp _ in
  let* s ins P gty_P := mk_tProd s Anon sProp+ (
    let* s ins a gty_a := mk_tProd s Anon sProp ((get_term s A); _) sProp+ _
      in (mk_sProp s)
    ) sProp _ in
  let* s ins x gty_x := mk_tProd s Anon sProp  ((get_term s A); _) sProp _ in
  let* s ins y gty_y := mk_tProd s Anon sProp  ((get_term s A); _) sProp _ in
  let* s ins eq_xy gty_xy := mk_tProd s Anon sProp (
    mk_Apps s (get_term s eq) (get_type s eq) [get_term s A; get_term s x; get_term s y] _ _) sProp _ in
  let* s ins px gty_px := mk_tProd s Anon sProp (
    mk_App s (get_term s P) (get_term s x) Anon sProp (get_type s x) _ _ _
  ) sProp eq_refl in
  mk_App s (get_term s P) (get_term s x) Anon sProp (get_type s x) _ _ _.
(* ### Proof Derivation ### *)
(* Proof Derivation: eq *)
Next Obligation.
  rewrite sort_of_product_idem. done.
Qed.
Next Obligation.
  intros. replace_type. rewrite gty_A //=.
Qed.
Next Obligation.
  intros. replace_type. rewrite gty_A //=.
Qed.
(* Proof Derivation: A *)
Next Obligation.
  intros. replace_type. rewrite gty_A //=.
Qed.
(* Proof Derivation: P *)
    (* already resolved by redunduncy *)
(* Proof Derivation: x *)
Next Obligation.
  intros. replace_type. rewrite gty_A //=.
Qed.
(* Proof Derivation: y *)
Next Obligation.
  intros. replace_type. rewrite gty_A //=.
Qed.
(* Proof Derivation: eq x y *)
(* type deriv: eq *)
Next Obligation.
  intros. apply well_type_get.
Qed.
(* type deriv app *)
Next Obligation.
  intros. rewrite gty_eq. simpl_lift.
  repeat constructor; simpl; fold subst; clear gty_eq.
  + replace_type. rewrite gty_A //=.
  + rewrite lift0_id. replace_type. rewrite gty_x.
    rewrite (get_term_in A) (get_term_in A s). simpl_lift.
  + rewrite simpl_subst_k //=. replace_type. rewrite gty_y.
    rewrite (get_term_in A s4) (get_term_in A s). simpl_lift.
Qed.
(* Type Derive P x *)
Next Obligation. (* type deriv: get_type s x *)
  intros. rewrite gty_x. replace_type_lift. rewrite gty_A. simpl_lift.
Qed.
Next Obligation. (* type: get_term s P *)
  intros. replace_type. rewrite gty_P gty_x /=. simpl_lift. f_equal.
  rewrite (get_term_in A s3) /=. simpl_lift.
Qed.
Next Obligation. (* type: get_term s x *)
  intros. apply well_type_get.
Qed.
(* Type Derive P y *)
Next Obligation.
  intros. rewrite gty_x /=. replace_type_lift.
  rewrite gty_A /=. simpl_lift.
Qed.
Next Obligation. (* type: get_term s P *)
  intros. replace_type. rewrite gty_P gty_x /=. simpl_lift. f_equal.
  rewrite (get_term_in A s3) /=. simpl_lift.
Qed.
Next Obligation. (* get_term s x *)
  intros. apply well_type_get.
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

