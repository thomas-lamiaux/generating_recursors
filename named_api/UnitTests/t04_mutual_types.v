From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import All.

From NamedAPI Require Import unit_tests.

Unset Elimination Schemes.

(* ################################################# *)
(* 5. Mutual : YES / Parameters : NO / Indices : NO *)

Inductive teven : Prop :=
| teven0 : teven
| tevenS : todd -> teven
with
todd : Prop :=
| toddS : teven -> todd.

Scheme teven_ind := Induction for teven Sort Prop
  with todd_ind  := Induction for todd Sort Prop.

Inductive teven_param1 : teven -> Prop :=
| teven0_param1 : teven_param1 teven0
| tevenS_param1 : forall to, todd_param1 to -> teven_param1 (tevenS to)
with
todd_param1 : todd -> Prop :=
| toddS_param1 : forall te, teven_param1 te -> todd_param1 (toddS te).

MetaCoq Run (tmMsg "01/02 teven").
Redirect "UnitTests/tests/04_01_teven_coq" MetaCoq Run (print_rec "teven").
Redirect "UnitTests/tests/04_01_teven_gen" MetaCoq Run (generate [] teven).
(* Redirect "UnitTests/tests/04_02_todd_coq" MetaCoq Run (print_rec "todd"). *)
(* Redirect "UnitTests/tests/04_02_todd_gen" MetaCoq Run (generate [] todd). *)

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

Scheme even_ind := Induction for even Sort SProp
  with odd_ind  := Induction for odd Sort SProp.

Inductive even_param1 : forall n, even n -> Prop :=
| even0_param1 : even_param1 0 even0
| evenS_param1 : forall n, forall o, odd_param1 n o -> even_param1 (S n) (evenS n o)
with
odd_param1 : forall n, odd n -> Prop :=
| oddS_param1 : forall n, forall e, even_param1 n e -> odd_param1 (S n) (oddS n e).

MetaCoq Run (tmMsg "02/02 even").
Redirect "UnitTests/tests/04_03_even_coq" MetaCoq Run (print_rec "even").
Redirect "UnitTests/tests/04_03_even_gen" MetaCoq Run (generate [] even).
(* Redirect "UnitTests/tests/04_04_odd_coq" MetaCoq Run (print_rec "odd"). *)
(* Redirect "UnitTests/tests/04_04_odd_gen" MetaCoq Run (generate [] odd). *)