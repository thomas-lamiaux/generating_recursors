From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.

From RecNamed Require Import unit_tests.

(* ################################################# *)
(* 5. Mutual : YES / Parameters : NO / Indices : NO *)

Inductive teven : Prop :=
| teven0 : teven
| tevenS : todd -> teven
with
  todd : Prop :=
  | toddS : teven -> todd.

Scheme teven_todd_ind := Induction for teven Sort Prop
  with todd_teven_ind := Induction for todd Sort Prop.

Redirect "recursors_named/unit_tests/tests/04_01_teven_coq" MetaRocq Run (print_rec "teven_todd").
Redirect "recursors_named/unit_tests/tests/04_01_teven_gen" MetaRocq Run (gen_rec [] <% teven %>).
Redirect "recursors_named/unit_tests/tests/04_02_todd_coq" MetaRocq Run (print_rec "todd_teven").
Redirect "recursors_named/unit_tests/tests/04_02_todd_gen" MetaRocq Run (gen_rec [] <% todd %>).

(* ################################################# *)
(* 6. Mutual : YES / Parameters : Yes / Indices : NO *)


(* ################################################# *)
(* 7. Mutual : YES / Parameters : NO / Indices : YES *)
Inductive even : nat -> Prop :=
  | even0   : even 0
  | evenS n : odd n -> even (S n)
with
  odd : nat -> Prop :=
  | oddS n : even n -> odd (S n).

Scheme even_odd_ind := Induction for even Sort SProp
  with odd_even_ind := Induction for odd Sort SProp.

  Redirect "recursors_named/unit_tests/tests/04_03_even_coq" MetaRocq Run (print_rec "even_odd").
  Redirect "recursors_named/unit_tests/tests/04_03_even_gen" MetaRocq Run (gen_rec [] <% even %>).
  Redirect "recursors_named/unit_tests/tests/04_04_odd_coq" MetaRocq Run (print_rec "odd_even").
  Redirect "recursors_named/unit_tests/tests/04_04_odd_gen" MetaRocq Run (gen_rec [] <% odd %>).