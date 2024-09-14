From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import All.

From RecAPI Require Import unit_tests.

(* ################################################# *)
(* 3. Mutual : NO / Parameters : NO / Indices : YES *)

(* One indice *)
Inductive vec1 : nat -> Set :=
| vnil1    : vec1 0
| vcons1 n : vec1 n -> vec1 (S n).

Redirect "recursors_api/unit_tests/tests/03_01_vec1_coq" MetaCoq Run (print_rec "vec1").
Redirect "recursors_api/unit_tests/tests/03_01_vec1_gen" MetaCoq Run (gen_rec vec1).

(* Two indices *)
Inductive vec2 : nat -> bool -> Set :=
| vnil2     : vec2 0 true
| vcons2  n : vec2 n false -> vec2 (S n) true.

Redirect "recursors_api/unit_tests/tests/03_02_vec2_coq" MetaCoq Run (print_rec "vec2").
Redirect "recursors_api/unit_tests/tests/03_02_vec2_gen" MetaCoq Run (gen_rec vec2).


(* ################################################# *)
(* 4. Mutual : NO / Parameters : YES / Indices : YES *)

(* Vec param + indice *)
Inductive vec3 (A : Set) : nat -> Set :=
| vnil3    : vec3 A 0
| vcons3 n : A -> vec3 A n -> vec3 A (S n).

Redirect "recursors_api/unit_tests/tests/03_03_vec3_coq" MetaCoq Run (print_rec "vec3").
Redirect "recursors_api/unit_tests/tests/03_03_vec3_gen" MetaCoq Run (gen_rec vec3).

(* two param / two indice *)
Inductive vec4 (A B : Set) : nat -> bool -> Set :=
| vnil4 (a : A)    : vec4 A B 0 true
| vcons4 (b : B) n : vec4 A B n false.

Redirect "recursors_api/unit_tests/tests/03_04_vec4_coq" MetaCoq Run (print_rec "vec4").
Redirect "recursors_api/unit_tests/tests/03_04_vec4_gen" MetaCoq Run (gen_rec vec4).

(* two param / two indice *)
Inductive vec5 (A B : Set) : nat -> nat -> Set :=
| vnil5 (a : A)    : vec5 A B 0 0
| vcons (b : B) n m : vec5 A B n m.

Redirect "recursors_api/unit_tests/tests/03_05_vec5_coq" MetaCoq Run (print_rec "vec5").
Redirect "recursors_api/unit_tests/tests/03_05_vec5_gen" MetaCoq Run (gen_rec vec5).


Unset Elimination Schemes.

(* Eq indice dep on param  *)
Inductive eq (A : Type) (x:A) : A -> Prop :=
    eq_refl : eq A x x.

Definition eq_ind A (x: A) (P : forall u, eq A x u -> Prop)
  (f0 : P x (eq_refl A x)) : forall u, forall q : eq A x u, P u q.
Proof.
  intros. destruct q. exact f0.
Defined.

Redirect "recursors_api/unit_tests/tests/03_06_eq_coq" MetaCoq Run (print_rec "eq").
Redirect "recursors_api/unit_tests/tests/03_06_eq_gen" MetaCoq Run (gen_rec eq).

Inductive foo (A : Type) : list A -> Type :=
| cf : foo A (@nil A).

Definition foo_ind A (P : forall l, foo A l -> Prop)
  (f0 : P (@nil A) (cf A)) : forall l, forall x : foo A l, P l x.
Proof.
  intros. destruct x. exact f0.
Defined.

Redirect "recursors_api/unit_tests/tests/03_07_foo_coq" MetaCoq Run (print_rec "foo").
Redirect "recursors_api/unit_tests/tests/03_07_foo_gen" MetaCoq Run (gen_rec foo).

Inductive vectree A : nat -> Type :=
| vleaf : A -> vectree A 0
| fnode : forall n, (nat -> vectree A n) -> vectree A (S n).

Redirect "recursors_api/unit_tests/tests/03_08_vectree_coq" MetaCoq Run (print_rec "vectree").
Redirect "recursors_api/unit_tests/tests/03_08_vectree_gen" MetaCoq Run (gen_rec vectree).

Inductive vectree2 A : nat -> Type :=
| vleaf2 : A -> vectree2 A 0
| vnode2 : forall n, (nat -> bool -> vectree2 A n) -> vectree2 A (S n).

Redirect "recursors_api/unit_tests/tests/03_09_vectree2_coq" MetaCoq Run (print_rec "vectree2").
Redirect "recursors_api/unit_tests/tests/03_09_vectree2_gen" MetaCoq Run (gen_rec vectree2).
