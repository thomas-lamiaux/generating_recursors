From MetaCoq.Utils Require Import utils.
From MetaCoq.Utils Require Import MCString.
From MetaCoq.Template Require Import All.

Import MCMonadNotation.

Require Import preliminary.
Require Import preprocess_debruijn_to_named.
Require Import generate_rec_types_named.
Require Import postprocess_named_to_debruijn.


(* ############################
   ###    Tests Functions   ###
   ############################ *)

Definition gen_rec_term := tRel 0.

Definition tmPrintb {A} (b : bool) (a : A) : TemplateMonad unit :=
  if b then tmPrint a else tmMsg "".

Definition test_term (print_mdecl print_term print_type : bool) (tm : term)
  : TemplateMonad _ :=
  match tm with
  | tInd ind0 _ =>
    let kname := inductive_mind ind0 in
    let pos_block := inductive_ind ind0 in
    (* Get the mdecl definition and preprocess it *)
    mdecl <- tmQuoteInductive (inductive_mind ind0) ;;
    process_mdecl <- tmEval cbv (preprocessing_mind kname mdecl) ;;
    tmPrintb print_mdecl process_mdecl ;;
    (* Get the pos_block body under scrutiny *)
    match nth_error process_mdecl.(ind_bodies) pos_block with
      | Some indb =>
        (* Compute term *)
        named_tm_rec <- tmEval all (gen_rec_term) ;;
        tmPrintb print_term named_tm_rec ;;
        debruijn_tm_rec <- tmEval all (named_to_debruijn 100 named_tm_rec) ;;
        (* Compute type *)
        named_ty_rec <- tmEval all (gen_rec_type kname pos_block process_mdecl indb) ;;
        tmPrintb print_type named_ty_rec ;;
        debruijn_ty_rec <- tmEval all (named_to_debruijn 100 named_ty_rec) ;;
        (* return *)
        tmReturn (debruijn_tm_rec, debruijn_ty_rec)
      | None    => tmFail "Error"
    end
  | _ => tmPrint tm ;; tmFail " is not an inductive"
  end.

Inductive mode :=
| Debug     : mode
| PrintType : mode
| PrintTerm : mode
| TestBoth  : mode.

Definition test_option (m : mode) (print_mdecl print_term print_type : bool)
    (tm : term) : TemplateMonad unit :=
  t <- test_term print_mdecl print_term print_type tm ;;
  let tm_rec := fst t in
  let ty_rec := snd t in
  match m with
  | Debug => tmMsg ""
  | PrintType =>  x <- (tmUnquote ty_rec) ;;
                  ker_ty_rec <- (tmEval all x.(my_projT2)) ;;
                  tmPrint ker_ty_rec
  | PrintTerm =>  x <- (tmUnquote tm_rec) ;;
                  ker_tm_rec <- (tmEval all x.(my_projT2)) ;;
                  tmPrint ker_tm_rec
  | TestBoth  => tmFail "bugs at the moment"
                 (* x <- (tmUnquote ty_rec) ;;
                 ker_ty_rec <- (tmEval all x.(my_projT2)) ;;
                 ker_tm_rec <- tmUnquoteTyped ker_ty_rec tm_rec ;;
                 tmPrint ker_tm_rec ;;
                 tmPrint ker_ty_rec *)
  end.

(* Definition test (tm : term) := test_option Debug false false true tm. *)
Definition test (tm : term) := test_option PrintType false false false tm.



(* ############################
   ###      Quick Tests     ###
   ############################ *)


(* ################################################# *)
(* 1. Mutual : NO / Parameters : NO / Indices : NO *)

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


(* ################################################# *)
(* 2. Mutual : NO / Parameters : YES / Indices : NO *)

(* MetaCoq Run (printInductive "list"). *)
MetaCoq Run (test <% list %>).

(* MetaCoq Run (printInductive "prod"). *)
MetaCoq Run (test <% prod %>).

Inductive prod4 (A B C D : Set) : Set :=
| cst : A -> B -> C -> D -> prod4 A B C D.

MetaCoq Run (test <% prod4 %>).

(* MetaCoq Run (printInductive "sum"). *)
MetaCoq Run (test <% sum %>).

(* ################################################# *)
(* 3. Mutual : NO / Parameters : NO / Indices : YES *)

Inductive vec1 : nat -> Set :=
| vnil1    : vec1 0
| vcons1 n : vec1 n -> vec1 (S n).

(* MetaCoq Run (printInductive "vec1"). *)
MetaCoq Run (test <% vec1 %>).

Inductive vec2 : nat -> bool -> Set :=
| vnil2     : vec2 0 true
| vcons2  n : vec2 n false.

(* MetaCoq Run (printInductive "vec2"). *)
MetaCoq Run (test <% vec2 %>).


(* ################################################# *)
(* 4. Mutual : NO / Parameters : YES / Indices : YES *)

Inductive vec3 (A : Set) : nat -> Set :=
| vnil3    : vec3 A 0
| vcons3 n : A -> vec3 A n -> vec3 A (S n).

(* MetaCoq Run (printInductive "vec3"). *)
MetaCoq Run (test <% vec3 %>).

Inductive vec4 (A B : Set) : nat -> bool -> Set :=
| vnil4 (a : A)    : vec4 A B 0 true
| vcons4 (b : B) n : vec4 A B n false.

(* MetaCoq Run (printInductive "vec4"). *)
MetaCoq Run (test <% vec4 %>).

Inductive eq (A:Type) (y:A) : A -> Prop :=
    eq_refl : y = y :>A

where "x = y :> A" := (@eq A x y) : type_scope.

MetaCoq Run (test <% eq %>).


(* ################################################# *)
(* 5. Mutual : YES / Parameters : NO / Indices : NO *)

Inductive teven : Prop :=
| tevenb : teven
| tevenS : todd -> teven
with
  todd : Prop :=
  | toddS : teven ->  todd.

(* MetaCoq Run (printInductive "teven"). *)
MetaCoq Run (test <% teven %>).

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

Scheme even_odd_rec := Induction for even Sort Prop
  with odd_even_rec := Induction for odd Sort Prop.

Check even_odd_rec.

MetaCoq Run (test <% even %>).
MetaCoq Run (test <% odd %>).

(* ################################################# *)
(* 8. Mutual : YES / Parameters : Yes / Indices : YES *)