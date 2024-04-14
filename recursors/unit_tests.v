From MetaCoq.Utils Require Import utils.
From MetaCoq.Utils Require Import MCString.
From MetaCoq.Template Require Import All.
From MetaCoq.Common Require Import Universes.

Import MCMonadNotation.

Require Import preliminary.
Require Import named_to_debruijn.
Require Import generate_rec_types_named.


(* ############################
   ###    Tests Functions   ###
   ############################ *)

Polymorphic Definition test_term (tm : Ast.term) : TemplateMonad _ :=
  match tm with
  | tInd ind0 _ =>
    mdecl <- tmQuoteInductive (inductive_mind ind0) ;;
    let foo := nth_error mdecl.(ind_bodies) (inductive_ind ind0) in
    match foo with
    | Some indb =>
      named_rec_type <- tmEval all (gen_rec_type (inductive_mind ind0) (inductive_ind ind0) mdecl indb) ;;
      (* tmPrint named_rec_type;; *)
      let debruijn_rec_type := tmEval all (named_to_debruijn 100 named_rec_type) in
      debruijn_rec_type
      (* let prepro_mdecl := tmEval all (preprocessing_mind (inductive_mind ind0) mdecl) in
      prepro_mdecl *)
    | None    => tmFail "Error"
    end
  | _ => tmPrint tm ;; tmFail " is not an inductive"
  end.

Polymorphic Definition test (tm : Ast.term) : TemplateMonad unit :=
  t <- test_term tm ;;
  (* tmPrint t. *)
  x <- (tmUnquote t) ;;
  y <- (tmEval all x.(my_projT2)) ;;
  tmPrint y.


(* ############################
   ###      Quick Tests     ###
   ############################ *)

(* No Parameters *)
(* MetaCoq Run (printInductive "False"). *)
MetaCoq Run (test <% False %>).

(* MetaCoq Run (printInductive "bool"). *)
MetaCoq Run (test <% bool %>).

(* MetaCoq Run (printInductive "nat"). *)
MetaCoq Run (test <% nat %>).

Inductive bnat : Set :=
| bO : bnat
| bS : bnat -> bool -> bnat -> bnat.

(* MetaCoq Run (printInductive "bnat"). *)
MetaCoq Run (test <% bnat %>).

(* MetaCoq Run (printInductive "list"). *)
MetaCoq Run (test <% list %>).

(* MetaCoq Run (printInductive "prod"). *)
MetaCoq Run (test <% prod %>).

Inductive prod4 (A B C D : Set) : Set :=
  | inj : A -> B -> C -> D -> prod4 A B C D.

MetaCoq Run (test <% prod4 %>).

Inductive vec : nat -> Set :=
| vec0   : vec 0
| vecS n m : vec n -> vec m -> vec (S n).

MetaCoq Run (test <% vec %>).

Inductive vec2 : nat -> bool -> Set :=
| vnil2   : vec2 0 true
| vin2  n : vec2 n false.

MetaCoq Run (test <% vec2 %>).

Inductive vec3 (A B : Set) : nat -> bool -> Set :=
| vnil3 (a : A)   : vec3 A B 0 true
| vin3  (b : B) n : vec3 A B n false.

MetaCoq Run (test <% vec3 %>).

Inductive teven : Prop :=
| tevenb  : teven
| tevenS : todd -> teven
with
  todd : Prop :=
  | toddS : teven ->  todd.

(* MetaCoq Run (printInductive "teven"). *)
MetaCoq Run (test <% teven %>).

Inductive even : nat -> Prop :=
  | even0   : even 0
  | evenS n : odd n -> even (S n)
with
  odd : nat -> Prop :=
  | oddS n : even n -> odd (S n).

MetaCoq Run (test <% even %>).
MetaCoq Run (test <% odd %>).