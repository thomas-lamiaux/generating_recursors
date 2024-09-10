From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import All.

From RecAPI Require Import unit_tests.

Inductive b_let (A : Prop) : Type :=
| b_letz : b_let A
| b_lets (n m : nat) : let x := n + 0 in x = m -> x = m + 1 -> b_let A -> b_let A.

Redirect "recursors_api/unit_tests/tests/07_01_b_let_coq" MetaCoq Run (print_rec "b_let").
Redirect "recursors_api/unit_tests/tests/07_01_b_let_gen" MetaCoq Run (gen_rec <% b_let %>).

Inductive rc_let (A : Prop) : Type :=
| rc_letz : rc_let A
| rc_lets (a : A) : let x := rc_let A in x -> rc_let A.

Redirect "recursors_api/unit_tests/tests/07_02_rc_let_coq" MetaCoq Run (print_rec "rc_let").
Redirect "recursors_api/unit_tests/tests/07_02_rc_let_gen" MetaCoq Run (gen_rec  <% rc_let %>).

Inductive rc_letpar (A : Prop) : Type :=
| rc_letparz : rc_letpar A
| rc_letpars (n m : nat) : rc_letpar A -> (let y := rc_letpar A in y) -> rc_letpar A.

Redirect "recursors_api/unit_tests/tests/07_03_rc_let_coq" MetaCoq Run (print_rec "rc_letpar").
Redirect "recursors_api/unit_tests/tests/07_03_rc_let_gen" MetaCoq Run (gen_rec  <% rc_letpar %>).

Inductive crazy1 : nat -> Type :=
| crazy1_z : crazy1 0
| crazy1_s (n : nat) : let x := n + 0 in crazy1 x.

Redirect "recursors_api/unit_tests/tests/07_04_crazy1_coq" MetaCoq Run (print_rec "crazy1").
Redirect "recursors_api/unit_tests/tests/07_04_crazy1_gen" MetaCoq Run (gen_rec  <% crazy1 %>).

Inductive crazy2 (A : let y := Prop in y +  Prop) : (let y := bool in bool + nat) -> Type :=
| crazy2_z : crazy2 A (inr 0)
| crazy2_s (k n m : nat) : let x := n + 0 in x = m -> x = m + 1 -> crazy2 A (inl true) ->
                     let z := 0 in crazy2 A (let y := 0 in inr (x + y)).

Redirect "recursors_api/unit_tests/tests/07_05_crazy2_coq" MetaCoq Run (print_rec "crazy2").
Redirect "recursors_api/unit_tests/tests/07_05_crazy2_gen" MetaCoq Run (gen_rec  <% crazy2 %>).

Inductive diag : term -> term -> Type :=
| dcons c :
  diag c c ->
  let ptm := c in
  diag c c.

Redirect "recursors_api/unit_tests/tests/07_06_diag_coq" MetaCoq Run (print_rec "diag").
Redirect "recursors_api/unit_tests/tests/07_06_diag_gen" MetaCoq Run (gen_rec  <% diag %>).


Inductive redc : Type :=
| redc0 : redc
| redc1 : ((fun x => x) redc) -> redc.

Redirect "recursors_api/unit_tests/tests/07_07_redc_coq" MetaCoq Run (print_rec "redc").
Redirect "recursors_api/unit_tests/tests/07_07_redc_gen" MetaCoq Run (gen_rec  <% redc %>).