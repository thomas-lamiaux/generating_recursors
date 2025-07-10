From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.

From PluginNestedElim Require Import unit_tests.

(* nat *)
Inductive nat_param1 : nat -> Type :=
| z_param1 : nat_param1 0
| S_param1 : forall n, nat_param1 n -> nat_param1 (S n).

Definition nat_param1_term : forall (x : nat), nat_param1 x :=
  nat_rec nat_param1 z_param1 (fun n => S_param1 n ).

Definition nat_func : nat -> nat :=
  fun x => x.

MetaRocq Run (get_paramEp nat []).


(* list  *)
Inductive list_param1 A (PA : A -> Type) : list A -> Type :=
| nil_param1 : list_param1 A PA (@nil A)
| cons_param1 : forall a, PA a -> forall l, list_param1 A PA l -> list_param1 A PA (cons a l).

Definition list_param1_term A (PA : A -> Type) (HPA : forall r : A, PA r) (l : list A) : list_param1 A PA l :=
  list_rect (list_param1 A PA)
            (nil_param1 A PA)
            (fun a l0 IHl => cons_param1 A PA a (HPA a) l0 IHl) l.

Definition list_func A A_bis (fA : A -> A_bis) : list A -> list A_bis :=
  fix rec (l : list A) :=
  match l with
  | nil => nil
  | cons a l => cons (fA a) (rec l)
  end.

MetaRocq Run (get_paramEp list []).


(* prod *)
Inductive prod_param1 A (PA : A -> Type) B (PB : B -> Type) : A * B -> Type :=
| pair_param1 : forall a, PA a -> forall b, PB b -> prod_param1 A PA B PB (pair a b).

Definition prod_param1_term A (PA : A -> Type) (HPA : forall a : A, PA a)
                            B (PB : B -> Type) (HPB : forall b : B, PB b)
                            : forall (x : A * B), prod_param1 A PA B PB x :=
  prod_rect (prod_param1 A PA B PB)
            (fun a b => pair_param1 A PA B PB a (HPA a) b (HPB b)).

Definition prod_func A A_bis (fA : A -> A_bis) B B_bis (fB : B -> B_bis) :
  A * B -> A_bis * B_bis :=
  fix rec (x : A * B) :=
  match x with
  | pair a b => pair (fA a) (fB b)
  end.

MetaRocq Run (get_paramEp prod []).


(* vec *)
Inductive vec A : nat -> Type :=
| vnil : vec A 0
| vcons : A -> forall n, vec A n -> vec A (S n).

Inductive vec_param1 A (P : A -> Type) : forall n, vec A n -> Type :=
| vnil_param1 : vec_param1 A P 0 (@vnil A)
| vcons_param1 :    forall a, P a
                 -> forall n,
                    forall v, vec_param1 A P n v
                 -> vec_param1 A P (S n) (vcons _ a n v).

Definition vec_param1_term A (PA : A -> Type) (HPA : forall a : A, PA a)
            n v : vec_param1 A PA n v :=
  vec_rect _ (fun n => vec_param1 A PA n)
              (vnil_param1 A PA)
              (fun a n v IHv => vcons_param1 A PA a (HPA a) n v IHv)
              n v.

Definition vec_func A A_bis (fA : A -> A_bis) : forall n, vec A n -> vec A_bis n :=
  fix rec n (v : vec A n) :=
  match v with
  | vnil => vnil _
  | vcons a n v => vcons _ (fA a) n (rec n v)
  end.

MetaRocq Run (get_paramEp vec []).


(* Add the parametricty *)
Inductive eq_param1 (A : Type) (PA : A -> Type) (x : A) : forall y, @eq A x y -> Prop :=
  eq_refl_param1 : eq_param1 A PA x x (@eq_refl A x).

Definition eq_param1_term A PA (HPA: forall a, PA a) x :
  forall y p, eq_param1 A PA x y p.
Proof.
  intros y p; destruct p; constructor; try easy.
Defined.

Definition eq_func A (x : A) : forall y, x = y -> x = y :=
  fix rec y p :=
  match p with
  | eq_refl => eq_refl
  end.

MetaRocq Run (get_paramEp (@eq) []).


(* Non strict positive parameter *)
Inductive Nstrpos (A : Type) : Type :=
| Nstrpos1 : Nstrpos A
| Nstrpos2 : (A -> Nstrpos A) -> Nstrpos A.

Inductive Nstrpos_param1 (A : Type) : Nstrpos A -> Type :=
| Nstrpos1_param1 : Nstrpos_param1 A (Nstrpos1 A)
| Nstrpos2_param1 :forall f, Nstrpos_param1 A (Nstrpos2 A f).

Definition Nstrpos_param1_term A : forall x, Nstrpos_param1 A x.
Proof.
  intros x; induction x; constructor; try easy.
Defined.

Definition Nstrpos_func A : Nstrpos A -> Nstrpos A :=
  fix rec (x : Nstrpos A) :=
  match x with
  | Nstrpos1 => Nstrpos1 A
  | Nstrpos2 f => Nstrpos2 A (fun a => rec (f a))
  end.

MetaRocq Run (get_paramEp Nstrpos []).


(* A uniform parameters centered  *)
Inductive non_strpos10 (A B : Type) (n : nat) : Type :=
| nstrpos101 : n = 0 -> non_strpos10 A B n
| nstrpos102 : (A -> nat) -> list B -> non_strpos10 A B n.

Inductive non_strpos10_param1 (A B : Type) (PB : B -> Type) (n : nat) : non_strpos10 A B n -> Type :=
| nstrpos101_param1 : forall (x : n = 0), non_strpos10_param1 A B PB n (nstrpos101 A B n x)
| nstrpos102_param1 : forall (f : A -> nat),
                      forall l : list B, list_param1 _ PB l ->
                      non_strpos10_param1 A B PB n (nstrpos102 A B n f l).

Definition non_strpos10_param1_term A B PB (HPB: forall b, PB b) n :
  forall x, non_strpos10_param1 A B PB n x.
Proof.
  intro x; induction x; constructor; try easy. apply list_param1_term; easy.
Defined.

Definition non_strpos10_func A B B_bis (fB : B -> B_bis) n : non_strpos10 A B n -> non_strpos10 A B_bis n :=
  fix rec (x : non_strpos10 A B n) :=
  match x with
  | nstrpos101 H => nstrpos101 A B_bis n H
  | nstrpos102 f l => nstrpos102 A B_bis n f (list_func B B_bis fB l)
  end.

(* MetaRocq Run (get_paramEp non_strpos10 [kmp_list; kmp_eq]). *)
MetaRocq Run (get_paramEp non_strpos10 [kmp_list; kmp_eq]).


(* A non uniform prameters *)
Inductive mixed1 (A B C : Type) : Type :=
| mc11 : mixed1 A B C
| mc12 : mixed1 A nat C -> mixed1 A B C.

Inductive mixed1_param1 A (PA : A -> Prop) B C : mixed1 A B C -> Type :=
| mc11_param1 : mixed1_param1 A PA B C (mc11 A B C)
| mc12_param1 : forall x, mixed1_param1 A PA nat C x ->
                mixed1_param1 A PA B C (mc12 A B C x).

Definition mixed1_param1_term A PA (HPA : forall a, PA a) B C : forall x, mixed1_param1 A PA B C x.
Proof.
  intros x; induction x; constructor; try easy.
Defined.

Definition mixed1_func A A_bis (fA : A -> A_bis) : forall B C, mixed1 A B C -> mixed1 A_bis B C :=
  fix rec B C (x : mixed1 A B C) :=
  match x with
  | mc11 => mc11 A_bis B C
  | mc12 y => mc12 A_bis B C (rec nat C y)
  end.

MetaRocq Run (get_paramEp mixed1 []).

Definition Ep' := [kmp_nat; kmp_list; kmp_prod ; kmp_vec; kmp_eq; kmp_Nstrpos; kmp_non_strpos10 ; kmp_mixed1].


(* Nesting with a function *)
Inductive All2i (A B : Type) (R : nat -> A -> B -> Type) (n : nat) : list A -> list B -> Type :=
	| All2i_nil : All2i A B R n [] []
  | All2i_cons : forall (a : A) (b : B) (lA : list A) (lB : list B),
                 R n a b -> All2i A B R (S n) lA lB -> All2i A B R n (a :: lA) (b :: lB).

Inductive All2i_param1 (A B : Type) (R : nat -> A -> B -> Type) (PR : forall n a b, R n a b -> Prop)
              (n : nat) : forall (lA : list A) (lB : list B), All2i A B R n lA lB -> Prop :=
| All2i_nil_param1 : All2i_param1 A B R PR n [] [] (All2i_nil A B R n)
| All2i_cons_param1 : forall (a : A) (b : B) (lA : list A) (lB : list B),
                      forall (r : R n a b), PR n a b r ->
                      forall (al : All2i A B R (S n) lA lB), All2i_param1 A B R PR (S n) lA lB al ->
                      All2i_param1 A B R PR n (a :: lA) (b :: lB) (All2i_cons A B R n a b lA lB r al).

Definition All2i_param1_term A B R PR (HPR : forall n a b r, PR n a b r) n la lb : forall x, @All2i_param1 A B R PR n la lb x.
Proof.
  intros x; induction x; constructor; try easy.
Defined.

Definition All2i_func A B R R_bis (fR : forall n a b, R n a b -> R_bis n a b) n :
  forall lA lB, All2i A B R n lA lB -> All2i A B R_bis n lA lB.
Proof.
  intros lA lb x; induction x; constructor ; eauto.
Defined.

MetaRocq Run (get_paramEp (@All2i) Ep').

(* Nesting context *)
Definition Ep := [kmp_nat; kmp_list; kmp_prod ; kmp_vec; kmp_eq; kmp_Nstrpos; kmp_non_strpos10 ; kmp_mixed1 ; kmp_All2i].
