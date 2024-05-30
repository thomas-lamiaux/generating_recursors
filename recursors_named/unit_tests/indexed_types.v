From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import All.

Require Import unit_tests.

(* ################################################# *)
(* 3. Mutual : NO / Parameters : NO / Indices : YES *)

(* One indice *)
Inductive vec1 : nat -> Set :=
| vnil1    : vec1 0
| vcons1 n : vec1 n -> vec1 (S n).

Redirect "recursors_named/tests/03_01_vec1_coq" MetaCoq Run (print_rec "vec1_ind").
Redirect "recursors_named/tests/03_01_vec1_gen" MetaCoq Run (gen_rec <% vec1 %>).

(* Two indices *)
Inductive vec2 : nat -> bool -> Set :=
| vnil2     : vec2 0 true
| vcons2  n : vec2 n false -> vec2 (S n) true.

Redirect "recursors_named/tests/03_02_vec2_coq" MetaCoq Run (print_rec "vec2_ind").
Redirect "recursors_named/tests/03_02_vec2_gen" MetaCoq Run (gen_rec <% vec2 %>).


(* ################################################# *)
(* 4. Mutual : NO / Parameters : YES / Indices : YES *)

(* Vec param + indice *)
Inductive vec3 (A : Set) : nat -> Set :=
| vnil3    : vec3 A 0
| vcons3 n : A -> vec3 A n -> vec3 A (S n).

Redirect "recursors_named/tests/04_03_vec3_coq" MetaCoq Run (print_rec "vec3_ind").
Redirect "recursors_named/tests/04_03_vec3_gen" MetaCoq Run (gen_rec <% vec3 %>).

(* two param / two indice *)
Inductive vec4 (A B : Set) : nat -> bool -> Set :=
| vnil4 (a : A)    : vec4 A B 0 true
| vcons4 (b : B) n : vec4 A B n false.

Redirect "recursors_named/tests/04_04_vec4_coq" MetaCoq Run (print_rec "vec4_ind").
Redirect "recursors_named/tests/04_04_vec4_gen" MetaCoq Run (gen_rec <% vec4 %>).


(* Eq indice dep on param *)
Inductive eq (A:Type) (z:A) : A -> Prop :=
    eq_refl : z = z :> A

where "x = y :> A" := (@eq A x y) : type_scope.

Redirect "recursors_named/tests/04_05_eq_coq" MetaCoq Run (print_rec "eq_ind").
Redirect "recursors_named/tests/04_05_eq_gen" MetaCoq Run (gen_rec <% eq %>).