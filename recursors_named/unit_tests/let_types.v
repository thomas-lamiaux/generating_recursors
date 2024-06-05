From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import All.

Require Import unit_tests.

Inductive b_let (A : Prop) : Type :=
| b_letz : b_let A
| b_lets (n m : nat) : let x := n + 0 in x = m -> x = m + 1 -> b_let A -> b_let A.

Redirect "recursors_named/tests/06_01_b_let_custom" Print b_let_ind.
Redirect "recursors_named/tests/06_01_b_let_gen" MetaCoq Run (gen_rec [] <% b_let %>).

Inductive rc_let (A : Prop) : Type :=
| rc_letz : rc_let A
| rc_lets (n m : nat) : let x := rc_let A in rc_let A -> x -> rc_let A.


Redirect "recursors_named/tests/06_03_rc_let_custom" Print rc_let_ind.
Redirect "recursors_named/tests/06_03_rc_let_gen" MetaCoq Run (gen_rec [] <% rc_let %>).

Inductive rc_letlet (A : Prop) : Type :=
| rc_letletz : rc_letlet A
| rc_letlets (n m : nat) : let x := rc_letlet A in rc_letlet A ->
                            x -> (let y := rc_letlet A in y) -> rc_letlet A.

Redirect "recursors_named/tests/06_04_rc_let_custom" Print rc_letlet_ind.
Redirect "recursors_named/tests/06_04_rc_let_gen" MetaCoq Run (gen_rec [] <% rc_letlet %>).

Inductive crazy (A : let y := Prop in y +  Prop) : (let y := bool in bool + nat) -> Type :=
| crazy_z : crazy A (inr 0)
| crazy_s (k n m : nat) : let x := n + 0 in x = m -> x = m + 1 -> crazy A (inl true) ->
                     let z := 0 in crazy A (let y := 0 in inr (x + y)).

Redirect "recursors_named/tests/06_05_crazy_custom" Print crazy_ind.
Redirect "recursors_named/tests/06_05_crazy_gen" MetaCoq Run (gen_rec [] <% crazy %>).

