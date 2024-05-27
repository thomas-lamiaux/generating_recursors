From MetaCoq.Utils Require Import utils.
From MetaCoq.Utils Require Import MCString.
From MetaCoq.Template Require Import All.

Import MCMonadNotation.

Require Import preliminary.
Require Import namming.
Require Import commons.
Require Import preprocess_debruijn_to_named.
Require Import generate_rec_type.
Require Import generate_rec_term.
Require Import postprocess_named_to_debruijn.


(* ############################
   ###    Tests Functions   ###
   ############################ *)


Definition tmPrintb {A} (b : bool) (a : A) : TemplateMonad unit :=
  if b then tmPrint a else tmMsg "".

Definition gen_rec_options (print_mdecl print_type print_term post : bool) (tm : term)
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
        named_tm_rec <- tmEval all (gen_rec_term kname pos_block process_mdecl indb) ;;
        tmPrintb (print_term && (negb post)) named_tm_rec ;;
        debruijn_tm_rec <- tmEval all (named_to_debruijn 1000 named_tm_rec) ;;
        tmPrintb (print_term && post) debruijn_tm_rec ;;
        (* Compute type *)
        named_ty_rec <- tmEval all (gen_rec_type kname pos_block process_mdecl indb) ;;
        tmPrintb (print_type && (negb post)) named_ty_rec ;;
        debruijn_ty_rec <- tmEval all (named_to_debruijn 1000 named_ty_rec) ;;
        tmPrintb (print_type && post) debruijn_ty_rec ;;
        (* return *)
        tmReturn (debruijn_tm_rec, debruijn_ty_rec)
      | None    => tmFail "Error"
    end
  | _ => tmPrint tm ;; tmFail " is not an inductive"
  end.

Inductive mode :=
| Debug     : mode
| TestType : mode
| TestTerm : mode
| TestBoth  : mode.

Definition gen_rec_mode_options (m : mode) (print_mdecl print_type print_term  post : bool)
    (tm : term) : TemplateMonad unit :=
  t <- gen_rec_options print_mdecl print_type print_term post tm ;;
  let tm_rec := fst t in
  let ty_rec := snd t in
  match m with
  | Debug => tmMsg ""
  | TestType =>  x <- (tmUnquote ty_rec) ;;
                  ker_ty_rec <- (tmEval all x.(my_projT2)) ;;
                  tmPrint ker_ty_rec
  | TestTerm =>  x <- (tmUnquote tm_rec) ;;
                  ker_tm_rec <- (tmEval all x.(my_projT2)) ;;
                  tmPrint ker_tm_rec
  | TestBoth  => tmFail "bugs at the moment"
                 (* x <- (tmUnquote ty_rec) ;;
                 ker_ty_rec <- (tmEval all x.(my_projT2)) ;;
                 ker_tm_rec <- tmUnquoteTyped ker_ty_rec tm_rec ;;
                 tmPrint ker_tm_rec ;;
                 tmPrint ker_ty_rec *)
  end.

Definition print_rec_options (print_mdecl print_type print_term : bool) (q : qualid) :=
  if print_mdecl then printInductive q else tmMsg "";;
  if print_type then printConstantType q true else tmMsg "";;
  if print_term then printConstantBody q true else tmMsg "".

(* Debug preprocessing *)
(* Definition print_rec (q : qualid) := print_rec_options false false false q.
Definition gen_rec (tm : term) := gen_rec_mode_options Debug true false false false tm. *)

(* Debug Types *)
(* Definition print_rec (q : qualid) := print_rec_options false true false q.
Definition gen_rec (tm : term) := gen_rec_mode_options Debug false true false false tm. *)
(* Debug Terms *)
(* Definition print_rec (q : qualid) := print_rec_options false false true q.
Definition gen_rec (tm : term) := gen_rec_mode_options Debug false false true true tm. *)

(* Test Types  *)
(* Definition print_rec (q : qualid) := print_rec_options false false false q.
Definition gen_rec (tm : term) := gen_rec_mode_options TestType false false false false tm. *)
(* Test Terms *)
Definition print_rec (q : qualid) := print_rec_options false false false q.
Definition gen_rec (tm : term) := gen_rec_mode_options TestTerm false false false false tm.





(* ############################
   ###      Quick Tests     ###
   ############################ *)


(* ################################################# *)
(* 1. Mutual : NO / Parameters : NO / Indices : NO *)

(* False *)
Redirect "recursors_named/tests/01_false_rec_ind" MetaCoq Run (print_rec "False_ind").
Redirect "recursors_named/tests/01_false_rec_gen" MetaCoq Run (gen_rec <% False %>).

(* Bool *)
Redirect "recursors_named/tests/02_bool_rec_ind" MetaCoq Run (print_rec "bool_ind").
Redirect "recursors_named/tests/02_bool_rec_gen" MetaCoq Run (gen_rec <% bool %>).

(* Nat *)
Redirect "recursors_named/tests/03_nat_rec_ind" MetaCoq Run (print_rec "nat_ind").
Redirect "recursors_named/tests/03_nat_rec_gen" MetaCoq Run (gen_rec <% nat %>).

(* Bnat *)
Inductive bnat : Set :=
| bO : bnat
| bS : bnat -> bnat -> bool -> bnat.

Redirect "recursors_named/tests/04_bnat_rec_ind" MetaCoq Run (print_rec "bnat_ind").
Redirect "recursors_named/tests/04_bnat_rec_gen" MetaCoq Run (gen_rec <% bnat %>).

(* ################################################# *)
(* 2. Mutual : NO / Parameters : YES / Indices : NO *)

(* List *)
Redirect "recursors_named/tests/05_list_rec_ind" MetaCoq Run (print_rec "list_ind").
Redirect "recursors_named/tests/05_list_rec_gen" MetaCoq Run (gen_rec <% list %>).

(* Prod *)
Redirect "recursors_named/tests/06_prod_rec_ind" MetaCoq Run (print_rec "prod_ind").
Redirect "recursors_named/tests/06_prod_rec_gen" MetaCoq Run (gen_rec <% prod %>).

(* Sum *)
Redirect "recursors_named/tests/07_sum_rec_ind" MetaCoq Run (print_rec "sum_ind").
Redirect "recursors_named/tests/07_sum_rec_gen" MetaCoq Run (gen_rec <% sum %>).

(* Prod4 *)
Inductive prod4 (A B C D : Set) : Set :=
| cst : A -> B -> C -> D -> prod4 A B C D.

Redirect "recursors_named/tests/08_prod4_rec_ind" MetaCoq Run (print_rec "prod4_ind").
Redirect "recursors_named/tests/08_prod4_rec_gen" MetaCoq Run (gen_rec <% prod4 %>).


(* ################################################# *)
(* 3. Mutual : NO / Parameters : NO / Indices : YES *)

(* One indice *)
Inductive vec1 : nat -> Set :=
| vnil1    : vec1 0
| vcons1 n : vec1 n -> vec1 (S n).

Redirect "recursors_named/tests/09_vec1_rec_ind" MetaCoq Run (print_rec "vec1_ind").
Redirect "recursors_named/tests/09_vec1_rec_gen" MetaCoq Run (gen_rec <% vec1 %>).

(* Two indices *)
Inductive vec2 : nat -> bool -> Set :=
| vnil2     : vec2 0 true
| vcons2  n : vec2 n false -> vec2 (S n) true.

Redirect "recursors_named/tests/10_vec2_rec_ind" MetaCoq Run (print_rec "vec2_ind").
Redirect "recursors_named/tests/10_vec2_rec_gen" MetaCoq Run (gen_rec <% vec2 %>).


(* ################################################# *)
(* 4. Mutual : NO / Parameters : YES / Indices : YES *)

(* Vec param + indice *)
Inductive vec3 (A : Set) : nat -> Set :=
| vnil3    : vec3 A 0
| vcons3 n : A -> vec3 A n -> vec3 A (S n).

Redirect "recursors_named/tests/11_vec3_rec_ind" MetaCoq Run (print_rec "vec3_ind").
Redirect "recursors_named/tests/11_vec3_rec_gen" MetaCoq Run (gen_rec <% vec3 %>).

(* two param / two indice *)
Inductive vec4 (A B : Set) : nat -> bool -> Set :=
| vnil4 (a : A)    : vec4 A B 0 true
| vcons4 (b : B) n : vec4 A B n false.

Redirect "recursors_named/tests/12_vec4_rec_ind" MetaCoq Run (print_rec "vec4_ind").
Redirect "recursors_named/tests/12_vec4_rec_gen" MetaCoq Run (gen_rec <% vec4 %>).


(* Eq indice dep on param *)
Inductive eq (A:Type) (z:A) : A -> Prop :=
    eq_refl : z = z :> A

where "x = y :> A" := (@eq A x y) : type_scope.

Redirect "recursors_named/tests/13_eq_rec_ind" MetaCoq Run (print_rec "eq_ind").
Redirect "recursors_named/tests/13_eq_rec_gen" MetaCoq Run (gen_rec <% eq %>).


(* ################################################# *)
(* 5. Mutual : YES / Parameters : NO / Indices : NO *)

Inductive teven : Prop :=
| teven0 : teven
| tevenS : todd -> teven
with
  todd : Prop :=
  | toddS : teven -> todd.

Scheme teven_todd_rec := Induction for teven Sort Prop
  with todd_teven_rec := Induction for todd Sort Prop.

Redirect "recursors_named/tests/14_teven_rec_ind" MetaCoq Run (print_rec "teven_todd_rec").
Redirect "recursors_named/tests/14_teven_rec_gen" MetaCoq Run (gen_rec <% teven %>).
Redirect "recursors_named/tests/15_todd_rec_ind" MetaCoq Run (print_rec "todd_teven_rec").
Redirect "recursors_named/tests/15_todd_rec_gen" MetaCoq Run (gen_rec <% todd %>).

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

  Redirect "recursors_named/tests/16_even_rec_ind" MetaCoq Run (print_rec "even_odd_rec").
  Redirect "recursors_named/tests/16_even_rec_gen" MetaCoq Run (gen_rec <% even %>).
  Redirect "recursors_named/tests/17_odd_rec_ind" MetaCoq Run (print_rec "odd_even_rec").
  Redirect "recursors_named/tests/17_odd_rec_gen" MetaCoq Run (gen_rec <% odd %>).

(* ################################################# *)
(* 8. Mutual : YES / Parameters : Yes / Indices : YES *)
