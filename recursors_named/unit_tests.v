From MetaCoq.Utils Require Import utils.
From MetaCoq.Utils Require Import MCString.
From MetaCoq.Template Require Import All.

Import MCMonadNotation.

Require Import naming.
Require Import commons.
Require Import preprocess_debruijn_to_named.
Require Import generate_rec_type.
Require Import generate_rec_term.
Require Import postprocess_named_to_debruijn.


(* ############################
   ###  Printing functions  ###
   ############################ *)

Definition printInductive (q : qualid): TemplateMonad unit :=
  kn <- tmLocate1 q ;;
  match kn with
  | IndRef ind => (tmQuoteInductive ind.(inductive_mind)) >>= tmPrint
  | _ => tmFail ("[" ^ q ^ "] is not an inductive")
  end.

Definition printConstantBody (q : qualid) b : TemplateMonad unit :=
  kn <- tmLocate1 q ;;
  match kn with
  | ConstRef kn => x <- (tmQuoteConstant kn b) ;;
                   y <- tmEval all x.(cst_body) ;;
                   tmPrint y
  | _ => tmFail ("[" ^ q ^ "] is not a constant")
  end.

Definition printConstantType (q : qualid) b : TemplateMonad unit :=
  kn <- tmLocate1 q ;;
  match kn with
  | ConstRef kn => x <- (tmQuoteConstant kn b) ;;
                   y <- tmEval all x.(cst_type) ;;
                   tmPrint y
  | _ => tmFail ("[" ^ q ^ "] is not a constant")
  end.

(* ############################
   ###    Tests Functions   ###
   ############################ *)

(* Given an inductive type => returns kname, medecl, kname_param1, kname_param1_term  *)
Definition get_paramE (q : qualid) : TemplateMonad unit :=
  ref_ind <- tmLocate1 q ;;
  match ref_ind with
  | IndRef ind =>
    let kname := ind.(inductive_mind) in
    mdecl <- tmQuoteInductive kname ;;
    ref_param1 <- tmLocate1 (q ^ "_param1") ;;
    match ref_param1 with
    | IndRef ind_param1 =>
      let kname_param1 := ind_param1.(inductive_mind) in
      ref_param1_term <- tmLocate1 (q ^ "_param1_term") ;;
      match ref_param1_term with
      | ConstRef kname_param1_term =>
          tmDefinition ("kmp" ^ q) (kname, mdecl , kname_param1, kname_param1_term) ;;
          ret tt
      | _ => tmFail "Not a constant"
      end
    | _ => tmFail "Not an inductive"
    end
  | _ => tmFail "Not an inductive"
  end.

Definition tmPrintb {A} (b : bool) (a : A) : TemplateMonad unit :=
  if b then tmPrint a else tmMsg "".

Section TestFunctions.
  Context (print_mdecl print_type print_term post : bool).
  Context (E : list (kername * mutual_inductive_body * kername * kername)).

  Definition gen_rec_options (tm : term)
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
          named_tm_rec <- tmEval all (gen_rec_term kname process_mdecl U pos_block E indb) ;;
          tmPrintb (print_term && (negb post)) named_tm_rec ;;
          debruijn_tm_rec <- tmEval all (named_to_debruijn 1000 named_tm_rec) ;;
          tmPrintb (print_term && post) debruijn_tm_rec ;;
          (* Compute type *)
          named_ty_rec <- tmEval all (gen_rec_type kname process_mdecl U pos_block E indb) ;;
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

  (* Inductive Box : Type := box (A : SProp).  *)

  Definition gen_rec_mode_options (m : mode)
      (tm : term) : TemplateMonad unit :=
    t <- gen_rec_options tm ;;
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

  Definition print_rec_options (q : qualid) :=
    if print_mdecl then printInductive q else tmMsg "";;
    if print_type then printConstantType q true else tmMsg "";;
    if print_term then printConstantBody q true else tmMsg "".

End TestFunctions.

(* Debug preprocessing *)
Definition print_rec := print_rec_options false false false.
Definition gen_rec E := gen_rec_mode_options true false false false E Debug.

(* Debug Types *)
(* Definition print_rec := print_rec_options false true false.
Definition gen_rec E := gen_rec_mode_options false true false false E Debug. *)
(* Debug Terms *)
(* Definition print_rec := print_rec_options false false true.
Definition gen_rec E := gen_rec_mode_options false false true true E Debug. *)

(* Test Types  *)
  (* Definition print_rec := print_rec_options false false false.
  Definition gen_rec E := gen_rec_mode_options false false false false E TestType. *)
(* Test Terms  *)
(* Definition print_rec := print_rec_options false false false.
Definition gen_rec E := gen_rec_mode_options false false false false E TestTerm. *)

