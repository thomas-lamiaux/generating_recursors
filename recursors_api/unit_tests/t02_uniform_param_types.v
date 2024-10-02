From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import All.

From RecAPI Require Import unit_tests.

(* ################################################# *)
(* 2. Mutual : NO / Parameters : YES / Indices : NO *)

(* Inductive list0 (A : Type) : Type :=
| nil  : list0 A
| cons : list0 A -> list0 A.

(* List *)
Redirect "recursors_api/unit_tests/tests/02_00_list0_coq" MetaCoq Run (print_rec "list0").
Redirect "recursors_api/unit_tests/tests/02_00_list0_gen" MetaCoq Run (gen_rec [] list0). *)

(* List *)
Redirect "recursors_api/unit_tests/tests/02_01_list_coq" MetaCoq Run (print_rec "list").
Redirect "recursors_api/unit_tests/tests/02_01_list_gen" MetaCoq Run (gen_rec [] list).

(* Prod *)
Redirect "recursors_api/unit_tests/tests/02_02_prod_coq" MetaCoq Run (print_rec "prod").
Redirect "recursors_api/unit_tests/tests/02_02_prod_gen" MetaCoq Run (gen_rec [] prod).

(* Sum *)
Redirect "recursors_api/unit_tests/tests/02_03_sum_coq" MetaCoq Run (print_rec "sum").
Redirect "recursors_api/unit_tests/tests/02_03_sum_gen" MetaCoq Run (gen_rec [] sum).

(* Prod4 *)
Unset Elimination Schemes.

Inductive prod4 (A B C D : Set) : Set :=
| cst : A -> B -> C -> D -> prod4 A B C D.

Definition prod4_ind A B C D (P : prod4 A B C D -> Prop)
(f00 : forall a b c d, P (cst A B C D a b c d)) :=
  fix F (x : prod4 A B C D) : P x :=
  match x with
  | cst a b c d => f00 a b c d
  end.

Set Elimination Schemes.

Redirect "recursors_api/unit_tests/tests/02_04_prod4_coq" MetaCoq Run (print_rec "prod4").
Redirect "recursors_api/unit_tests/tests/02_04_prod4_gen" MetaCoq Run (gen_rec [] prod4).

(* Infinitely branching tree *)
Inductive ftree (A : Type) : Type :=
| fleaf : A -> ftree A
| fnode : (nat -> ftree A) -> ftree A.

Redirect "recursors_api/unit_tests/tests/02_05_ftree_coq" MetaCoq Run (print_rec "ftree").
Redirect "recursors_api/unit_tests/tests/02_05_ftree_gen" MetaCoq Run (gen_rec [] ftree).

Inductive ftree2 (A : Type) : Type :=
| fleaf2 : ftree2 A
| fnode2 : (nat -> bool -> ftree2 A) -> ftree2 A.

Redirect "recursors_api/unit_tests/tests/02_06_ftree2_coq" MetaCoq Run (print_rec "ftree2").
Redirect "recursors_api/unit_tests/tests/02_06_ftree2_gen" MetaCoq Run (gen_rec [] ftree2).