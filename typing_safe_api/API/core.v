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

(* Aux Functions *)
Definition isSome {A} : option A -> bool :=
  fun x => match x with Some _ => true | _ => false end.

Definition fold_right_i {A B} : (nat -> B -> A -> A) -> A -> list B -> A :=
  fun f a =>
  let fix aux n l : A :=
    match l with
    | [] => a
    | b :: l => f n b (aux (S n) l)
  end in
  aux 0.

Definition fold_left_i {A B} : (nat -> A -> B -> A) -> list B -> A -> A :=
  fun f =>
  let fix aux n l a0 : A :=
    match l with
    | [] => a0
    | b :: l => aux (S n) l (f n a0 b)
  end in
  aux 0.

Definition find_errori {A} (p : A -> bool) (l : list A) (default : A) : nat * A :=
  let fix aux n l : nat * A :=
    match l with
    | [] => (n , default)
    | a::l => if p a then (n, a) else aux (S n) l
    end
  in aux 0 l.

Notation "let* x .. z ':=' c1 'in' c2" := (c1 (fun x => .. (fun z => c2) ..))
(at level 100, x binder, z binder, c1 at next level, right associativity).

(*

#############################
###      Constrains       ###
#############################

1. Be able to refer to variables indirectly by names
2. Keep track of the old variables for weakening
3. Be able to replace variables by term on the fly


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
Next Obligation.
  constructor.
Qed.
Next Obligation.
  constructor.
Qed.
Next Obligation.
  unfold wf_subst. intros.
  rewrite (PCUICLiftSubst.subst_empty 0 t).
  rewrite (PCUICLiftSubst.subst_empty 0 T).
  assumption.
Qed.



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

(* 3. Subst a old var / context *)
Program Definition subst_cdecl (s : state) (cdecl : context_decl) (tm : term) : state :=
  mk_state (state_old_context s ,, cdecl)
           (state_new_context s)
           (map (lift0 1) s.(state_subst) ,, tm)
           (* Proofs *)
           _ _ _.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.

(* Program Definition subst_context (s : state) (Δ : context) (ltm : list term) : state :=
  mk_state (state_old_context s,,, Δ)
           (state_new_context s)
           (map (lift0 #|ltm|) s.(state_subst) ,,, ltm)
           (* Proofs *)
           _ _ _.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted. *)

