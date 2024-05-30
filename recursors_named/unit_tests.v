From MetaCoq.Utils Require Import utils.
From MetaCoq.Utils Require Import MCString.
From MetaCoq.Template Require Import All.

Import MCMonadNotation.

Require Import preliminary.
Require Import naming.
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
  let U := tSort sProp in
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
        named_tm_rec <- tmEval all (gen_rec_term kname process_mdecl U pos_block indb) ;;
        tmPrintb (print_term && (negb post)) named_tm_rec ;;
        debruijn_tm_rec <- tmEval all (named_to_debruijn 1000 named_tm_rec) ;;
        tmPrintb (print_term && post) debruijn_tm_rec ;;
        (* Compute type *)
        named_ty_rec <- tmEval all (gen_rec_type kname process_mdecl U pos_block indb) ;;
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
| Debug    : mode
| TestType : mode
| TestTerm : mode
| TestBoth : mode.

(* Inductive Box : Type := box (A : SProp). *)

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
