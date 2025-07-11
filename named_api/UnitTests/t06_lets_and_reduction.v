From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.

From NamedAPI Require Import unit_tests.
From NamedAPI Require Import nesting_param.

Inductive b_let (A : Type) : Type :=
| b_letz : b_let A
| b_lets (n m : nat) : let x := n + 0 in x = m -> x = m + 1 -> b_let A -> b_let A.

Inductive b_let_param1 A (PA : A -> Prop) : b_let A -> Type :=
| b_letz_param1 : b_let_param1 A PA (b_letz A)
| b_lets_param1 : forall n m, let x := n + 0 in forall Hm,
                  forall Hm1, forall x, b_let_param1 A PA x ->
                  b_let_param1 A PA (b_lets A n m Hm Hm1 x).


MetaRocq Run (tmMsg "01/10 btlet").
Redirect "named_api/UnitTests/tests/06_01_b_let_coq" MetaRocq Run (print_rec "b_let").
Redirect "named_api/UnitTests/tests/06_01_b_let_gen" MetaRocq Run (generate Ep b_let).

Inductive rc_let (A : Type) : Type :=
| rc_letz : rc_let A
| rc_lets (a : A) : let x := rc_let A in x -> rc_let A.

Inductive rc_let_param1 A (PA : A -> Prop) : rc_let A -> Type :=
| rc_letz_param1 : rc_let_param1 A PA (rc_letz A)
| rc_lets_param1 : forall a, PA a ->
                   let x := rc_let A in
                   forall x, rc_let_param1 A PA x ->
                   rc_let_param1 A PA (rc_lets A a x).

MetaRocq Run (tmMsg "02/10 rc_let").
Redirect "named_api/UnitTests/tests/06_02_rc_let_coq" MetaRocq Run (print_rec "rc_let").
Redirect "named_api/UnitTests/tests/06_02_rc_let_gen" MetaRocq Run (generate Ep rc_let).

Inductive rc_letpar (A : Prop) : Type :=
| rc_letparz : rc_letpar A
| rc_letpars (n m : nat) : rc_letpar A -> (let y := rc_letpar A in y) -> rc_letpar A.

Inductive rc_letpar_param1 A (PA : A -> Prop) : rc_letpar A -> Type :=
| rc_letparz_param1 : rc_letpar_param1 A PA (rc_letparz A)
| rc_letpars_param1 : forall n m,
                      forall x, rc_letpar_param1 A PA x ->
                      forall z, rc_letpar_param1 A PA z ->
                      rc_letpar_param1 A PA (rc_letpars A n m x z).

MetaRocq Run (tmMsg "03/10 re_letpar").
Redirect "named_api/UnitTests/tests/06_03_rc_letpar_coq" MetaRocq Run (print_rec "rc_letpar").
Redirect "named_api/UnitTests/tests/06_03_rc_letpar_gen" MetaRocq Run (generate Ep rc_letpar).

Inductive crazy1 : nat -> Type :=
| crazy1_z : crazy1 0
| crazy1_s (n : nat) : let x := n + 0 in crazy1 x.

Inductive crazy1_param1 : forall n, crazy1 n -> Type :=
| crazy1_z_param1 : crazy1_param1 0 crazy1_z
| crazy1_s_param1 : forall n x, crazy1_param1 n x.

MetaRocq Run (tmMsg "04/10 crazy1").
Redirect "named_api/UnitTests/tests/06_04_crazy1_coq" MetaRocq Run (print_rec "crazy1").
Redirect "named_api/UnitTests/tests/06_04_crazy1_gen" MetaRocq Run (generate Ep crazy1).

Inductive crazy2 (A : let y := Prop in y + Prop) : (let y := bool in bool + nat) -> Type :=
| crazy2_z : crazy2 A (inr 0)
| crazy2_s (k n m : nat) : let x := n + 0 in x = m -> x = m + 1 -> crazy2 A (inl true) ->
                     let z := 0 in crazy2 A (let y := 0 in inr (x + y)).

Inductive crazy2_param1 (A : let y := Prop in y + Prop) : forall z, crazy2 A z -> Type :=
| crazy2_z_param1 : crazy2_param1 A (inr 0) (crazy2_z A)
| crazy2_s_param1 : forall k n m, let x := n + 0 in forall Hm Hm1,
                    forall c, crazy2_param1 A (inl true) c ->
                    let z := 0 in
                    crazy2_param1 A (let y := 0 in inr (x + y)) (crazy2_s A k n m Hm Hm1 c).

MetaRocq Run (tmMsg "05/10 crazy2").
Redirect "named_api/UnitTests/tests/06_05_crazy2_coq" MetaRocq Run (print_rec "crazy2").
Redirect "named_api/UnitTests/tests/06_05_crazy2_gen" MetaRocq Run (generate Ep crazy2).

Inductive diag : term -> term -> Type :=
| dcons c : diag c c -> let ptm := c in diag c c.

Inductive diag_param1 : forall t1 t2, diag t1 t2 -> Type :=
| dcons_param1 : forall c,
                 forall x, diag_param1 c c x ->
                 let ptm := c in
                 diag_param1 c c (dcons c x).

MetaRocq Run (tmMsg "06/10 diag").
Redirect "named_api/UnitTests/tests/06_06_diag_coq" MetaRocq Run (print_rec "diag").
Redirect "named_api/UnitTests/tests/06_06_diag_gen" MetaRocq Run (generate Ep diag).

Inductive redc : nat -> Type :=
| redc0 : redc 0
| redc1 n : (redc ((fun x => 2 + x) n)) -> redc n.

Inductive redc_param1 : forall n, redc n -> Type :=
| redc0_param1 : redc_param1 0 redc0
| redc1_param1 : forall n,
                 forall x, redc_param1 ((fun x => 2 + x) n) x ->
                 redc_param1 n (redc1 n x).

MetaRocq Run (tmMsg "07/10 redc").
Redirect "named_api/UnitTests/tests/06_07_redc_coq" MetaRocq Run (print_rec "redc").
Redirect "named_api/UnitTests/tests/06_07_redc_gen" MetaRocq Run (generate Ep redc).

Definition foo : Type -> Type := fun x => x.

Inductive redEnv : Type :=
| redEnv0 : redEnv
| redEnv1 : redEnv -> foo redEnv -> redEnv.

Inductive redEnv_param1 : redEnv -> Type :=
| redEnv0_param1 : redEnv_param1 redEnv0
| redEnv1_param1 : forall x, redEnv_param1 x ->
                   forall y, redEnv_param1 y ->
                   redEnv_param1 (redEnv1 x y).

MetaRocq Run (tmMsg "08/10 redEnv").
Redirect "named_api/UnitTests/tests/06_08_redEnv_coq" MetaRocq Run (print_rec "redEnv").
Redirect "named_api/UnitTests/tests/06_08_redEnv_gen" MetaRocq Run (generate Ep redEnv).

Inductive nu_let1 (A : Type) : Type :=
| nu_let1_nil : nu_let1 A
| nu_let1_cons : let x := A in nu_let1 x -> nu_let1 A.

Inductive nu_let1_param1 A (PA : A -> Type) : nu_let1 A -> Type :=
| nu_let1_nil_param1 : nu_let1_param1 A PA (nu_let1_nil A)
| nu_let1_cons_param1 : let x := A in forall z, nu_let1_param1 x PA z ->
                        nu_let1_param1 A PA (nu_let1_cons A z).

MetaRocq Run (tmMsg "09/10 nu_let1").
Redirect "named_api/UnitTests/tests/06_09_nu_let1_coq" MetaRocq Run (print_rec "nu_let1").
Redirect "named_api/UnitTests/tests/06_09_nu_let1_gen" MetaRocq Run (generate Ep nu_let1).

Inductive nu_let2 (A : Type) : Type :=
| nu_let2_nil : nu_let2 A
| nu_let2_cons : let x := A * A in nu_let2 x -> nu_let2 A.

Inductive nu_let2_param1 A : nu_let2 A -> Type :=
| nu_let2_nil_param1 : nu_let2_param1 A (nu_let2_nil A)
| nu_let2_cons_param1 : let x := A * A in forall z, nu_let2_param1 x z ->
                        nu_let2_param1 A (nu_let2_cons A z).

MetaRocq Run (tmMsg "10/10 nu_let2").
Redirect "named_api/UnitTests/tests/06_10_nu_let2_coq" MetaRocq Run (print_rec "nu_let2").
Redirect "named_api/UnitTests/tests/06_10_nu_let2_gen" MetaRocq Run (generate Ep nu_let2).