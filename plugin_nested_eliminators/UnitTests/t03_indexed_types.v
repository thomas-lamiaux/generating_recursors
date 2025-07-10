From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.

From PluginNestedElim Require Import unit_tests.

(* ################################################# *)
(* 3. Mutual : NO / Parameters : NO / Indices : YES *)

(* One indice *)
Inductive vec1 : nat -> Type :=
| vnil1    : vec1 0
| vcons1 n : vec1 n -> vec1 (S n).

Inductive vec1_param1 : forall n, vec1 n -> Type :=
| vnil1_param1  : vec1_param1 0 (vnil1)
| vcons1_param1 : forall n,
                  forall v, vec1_param1 n v ->
                  vec1_param1 (S n) (vcons1 n v).

MetaRocq Run (tmMsg "01/09 vec1").
Redirect "plugin_nested_eliminators/UnitTests/tests/03_01_vec1_coq" MetaRocq Run (print_rec "vec1").
Redirect "plugin_nested_eliminators/UnitTests/tests/03_01_vec1_gen" MetaRocq Run (generate [] vec1).

(* Two indices *)
Inductive vec2 : nat -> bool -> Type :=
| vnil2     : vec2 0 true
| vcons2  n : vec2 n false -> vec2 (S n) true.

Inductive vec2_param1 : forall n b, vec2 n b -> Type :=
| vnil2_param1  : vec2_param1 0 true (vnil2)
| vcons2_param1 : forall n,
                  forall v, vec2_param1 n false v ->
                  vec2_param1 (S n) true (vcons2 n v).

MetaRocq Run (tmMsg "02/09 vec2").
Redirect "plugin_nested_eliminators/UnitTests/tests/03_02_vec2_coq" MetaRocq Run (print_rec "vec2").
Redirect "plugin_nested_eliminators/UnitTests/tests/03_02_vec2_gen" MetaRocq Run (generate [] vec2).


(* ################################################# *)
(* 4. Mutual : NO / Parameters : YES / Indices : YES *)

(* Vec param + indice *)
Inductive vec3 (A : Type) : nat -> Type :=
| vnil3    : vec3 A 0
| vcons3 n : A -> vec3 A n -> vec3 A (S n).

Inductive vec3_param1 A (PA : A -> Prop) : forall n, vec3 A n -> Type :=
| vnil3_param1  : vec3_param1 A PA 0 (vnil3 A)
| vcons3_param1 : forall n,
                  forall a, PA a ->
                  forall v, vec3_param1 A PA n v ->
                  vec3_param1 A PA (S n) (vcons3 A n a v).

MetaRocq Run (tmMsg "03/09 vec3").
Redirect "plugin_nested_eliminators/UnitTests/tests/03_03_vec3_coq" MetaRocq Run (print_rec "vec3").
Redirect "plugin_nested_eliminators/UnitTests/tests/03_03_vec3_gen" MetaRocq Run (generate [] vec3).

(* two param / two indice *)
Inductive vec4 (A B : Type) : nat -> bool -> Type :=
| vnil4 (a : A)    : vec4 A B 0 true
| vcons4 (b : B) n : vec4 A B n false.

Inductive vec4_param1 A (PA : A -> Prop) B (PB : B -> Prop) : forall n b, vec4 A B n b -> Type :=
| vnil4_param1  : forall a, PA a -> vec4_param1 A PA B PB 0 true (vnil4 A B a)
| vcons4_param1 : forall b, PB b ->
                  forall n,
                  vec4_param1 A PA B PB n false (vcons4 A B b n).

MetaRocq Run (tmMsg "04/09 vec4").
Redirect "plugin_nested_eliminators/UnitTests/tests/03_04_vec4_coq" MetaRocq Run (print_rec "vec4").
Redirect "plugin_nested_eliminators/UnitTests/tests/03_04_vec4_gen" MetaRocq Run (generate [] vec4).

(* two param / two indice *)
Inductive vec5 (A B : Type) : nat -> nat -> Type :=
| vnil5  (a : A)    : vec5 A B 0 0
| vcons5 (b : B) n m : vec5 A B n m.

Inductive vec5_param1 A (PA : A -> Prop) B (PB : B -> Prop) : forall n m, vec5 A B n m -> Type :=
| vnil5_param1  : forall a, PA a -> vec5_param1 A PA B PB 0 0 (vnil5 A B a)
| vcons5_param1 : forall b, PB b ->
                  forall n m,
                  vec5_param1 A PA B PB n m (vcons5 A B b n m).

MetaRocq Run (tmMsg "05/09 vec5").
Redirect "plugin_nested_eliminators/UnitTests/tests/03_05_vec5_coq" MetaRocq Run (print_rec "vec5").
Redirect "plugin_nested_eliminators/UnitTests/tests/03_05_vec5_gen" MetaRocq Run (generate [] vec5).

(* Eq indice dep on param  *)
Unset Elimination Schemes.

Inductive eq (A : Type) (x:A) : A -> Prop :=
    eq_refl : eq A x x.

Definition eq_ind A x (P : forall y, eq A x y -> Prop) (f00 : P x (eq_refl A x)) :=
  fix F y (z : eq A x y) : P y z :=
    match z with
    | eq_refl => f00
    end.

Set Elimination Schemes.

Inductive eq_param1 (A : Type) (x:A) : forall y, eq A x y -> Type :=
eq_refl_param1 : eq_param1 A x x (eq_refl A x).

MetaRocq Run (tmMsg "06/09 eq").
Redirect "plugin_nested_eliminators/UnitTests/tests/03_06_eq_coq" MetaRocq Run (print_rec "eq").
Redirect "plugin_nested_eliminators/UnitTests/tests/03_06_eq_gen" MetaRocq Run (generate [] eq).

Inductive foo (A : Type) : list A -> Type :=
| cf : foo A (@nil A).

Inductive foo_param1 (A : Type) : forall l, foo A l -> Type :=
| cf_cparam1 : foo_param1 A (@nil A) (cf A).

MetaRocq Run (tmMsg "07/09 foo").
Redirect "plugin_nested_eliminators/UnitTests/tests/03_07_foo_coq" MetaRocq Run (print_rec "foo").
Redirect "plugin_nested_eliminators/UnitTests/tests/03_07_foo_gen" MetaRocq Run (generate [] foo).

Inductive vectree A : nat -> Type :=
| vleaf : A -> vectree A 0
| vnode : forall n, (nat -> vectree A n) -> vectree A (S n).

Inductive vectree_param1 A (PA : A -> Prop) : forall n, vectree A n -> Type :=
| vleaf_param1 : forall a, PA a -> vectree_param1 A PA 0 (vleaf A a)
| vnode_param1 : forall n,
                 forall f, (forall m, vectree_param1 A PA n (f m)) ->
                 vectree_param1 A PA (S n) (vnode A n f).

MetaRocq Run (tmMsg "08/09 vectree").
Redirect "plugin_nested_eliminators/UnitTests/tests/03_08_vectree_coq" MetaRocq Run (print_rec "vectree").
Redirect "plugin_nested_eliminators/UnitTests/tests/03_08_vectree_gen" MetaRocq Run (generate [] vectree).

Inductive vectree2 A : nat -> Type :=
| vleaf2 : A -> vectree2 A 0
| vnode2 : forall n, (nat -> bool -> vectree2 A n) -> vectree2 A (S n).

Inductive vectree2_param1 A (PA : A -> Prop) : forall n, vectree2 A n -> Type :=
| vleaf2_param1 : forall a, PA a -> vectree2_param1 A PA 0 (vleaf2 A a)
| fnode2_param1 : forall n,
                  forall f, (forall m b, vectree2_param1 A PA n (f m b)) ->
                  vectree2_param1 A PA (S n) (vnode2 A n f).

MetaRocq Run (tmMsg "09/09 vectree2").
Redirect "plugin_nested_eliminators/UnitTests/tests/03_09_vectree2_coq" MetaRocq Run (print_rec "vectree2").
Redirect "plugin_nested_eliminators/UnitTests/tests/03_09_vectree2_gen" MetaRocq Run (generate [] vectree2).
