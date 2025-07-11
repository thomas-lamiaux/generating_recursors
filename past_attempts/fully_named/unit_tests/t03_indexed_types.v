From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.

From RecNamed Require Import unit_tests.

(* ################################################# *)
(* 3. Mutual : NO / Parameters : NO / Indices : YES *)

(* One indice *)
Inductive vec1 : nat -> Set :=
| vnil1    : vec1 0
| vcons1 n : vec1 n -> vec1 (S n).

Redirect "recursors_named/unit_tests/tests/03_01_vec1_coq" MetaRocq Run (print_rec "vec1").
Redirect "recursors_named/unit_tests/tests/03_01_vec1_gen" MetaRocq Run (gen_rec [] <% vec1 %>).

(* Two indices *)
Inductive vec2 : nat -> bool -> Set :=
| vnil2     : vec2 0 true
| vcons2  n : vec2 n false -> vec2 (S n) true.

Redirect "recursors_named/unit_tests/tests/03_02_vec2_coq" MetaRocq Run (print_rec "vec2").
Redirect "recursors_named/unit_tests/tests/03_02_vec2_gen" MetaRocq Run (gen_rec [] <% vec2 %>).


(* ################################################# *)
(* 4. Mutual : NO / Parameters : YES / Indices : YES *)

(* Vec param + indice *)
Inductive vec3 (A : Set) : nat -> Set :=
| vnil3    : vec3 A 0
| vcons3 n : A -> vec3 A n -> vec3 A (S n).

Redirect "recursors_named/unit_tests/tests/03_03_vec3_coq" MetaRocq Run (print_rec "vec3").
Redirect "recursors_named/unit_tests/tests/03_03_vec3_gen" MetaRocq Run (gen_rec [] <% vec3 %>).

(* two param / two indice *)
Inductive vec4 (A B : Set) : nat -> bool -> Set :=
| vnil4 (a : A)    : vec4 A B 0 true
| vcons4 (b : B) n : vec4 A B n false.

Redirect "recursors_named/unit_tests/tests/03_04_vec4_coq" MetaRocq Run (print_rec "vec4").
Redirect "recursors_named/unit_tests/tests/03_04_vec4_gen" MetaRocq Run (gen_rec [] <% vec4 %>).

(* two param / two indice *)
Inductive vec5 (A B : Set) : nat -> nat -> Set :=
| vnil5 (a : A)    : vec5 A B 0 0
| vcons (b : B) n m : vec5 A B n m.

Redirect "recursors_named/unit_tests/tests/03_05_vec5_coq" MetaRocq Run (print_rec "vec5").
Redirect "recursors_named/unit_tests/tests/03_05_vec5_gen" MetaRocq Run (gen_rec [] <% vec5 %>).

(*
Unset Elimination Schemes.

(* Eq indice dep on param  *)
Inductive eq (w y :nat) : nat -> nat -> Prop :=
    eq_refl : eq w y w y.

(* where "x = y :> A" := (@eq A x y) : type_scope. *)

Definition eq_ind (x y : nat) (P : forall u v, eq x y u v -> Prop)
  (f0 : P x y (eq_refl x y)) : forall u v, forall q : eq x y u v, P u v q.
Proof.
  intros. destruct q. exact f0.
Defined.



Redirect "recursors_named/unit_tests/tests/03_06_eq_coq" MetaRocq Run (print_rec "eq").
Redirect "recursors_named/unit_tests/tests/03_06_eq_gen" MetaRocq Run (gen_rec [] <% eq %>).

Inductive foo (A : Type) : list A -> Type :=
| cf : foo A (@nil A).

Definition foo_ind A (P : forall l, foo A l -> Prop)
  (f0 : P (@nil A) (cf A)) : forall l, forall x : foo A l, P l x.
Proof.
  intros. destruct x. exact f0.
Defined.


Redirect "recursors_named/unit_tests/tests/03_07_foo_coq" MetaRocq Run (print_rec "foo").
Redirect "recursors_named/unit_tests/tests/03_07_foo_gen" MetaRocq Run (gen_rec [] <% foo %>).
*)