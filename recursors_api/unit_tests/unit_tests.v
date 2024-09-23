From RecAPI Require Import commons.
From RecAPI Require Import preprocess_uparams.
From RecAPI Require Import compute_strict_pos_uparams.
From RecAPI Require Import generate_custom_param.
From RecAPI Require Import generate_rec_type.

From MetaCoq.Utils Require Export utils.
From MetaCoq.Template Require Export All.

Import MCMonadNotation.


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
          tmDefinition ("kmp" ^ q)
          (mk_one_env_param kname mdecl kname_param1 kname_param1_term) ;;
          ret tt
      | _ => tmFail "Not a constant"
      end
    | _ => tmFail "Not an inductive"
    end
  | _ => tmFail "Not an inductive"
  end.


Definition tmPrintb {A} (b : bool) (a : A) : TemplateMonad unit :=
  if b then tmPrint a else tmMsg "".

Definition tmPrintbInd (b : bool) (s : qualid) : TemplateMonad unit :=
  if b then printInductive s else tmMsg "".


Section TestFunctions.
  Context (print_nuparams print_strpos print_cparam print_type print_term : bool).
  Context (E : env_param).

Definition U := mk_output_univ (tSort sProp) (relev_sort (tSort sProp)).


  Definition gen_rec_options {A} (s : A) : TemplateMonad (term * term) :=
    (* 1. Get env and term *)
    tmPrint s ;;
    x <- tmQuoteRec s ;;
    let ' (E, tm) := x in
    etm <- tmEval hnf tm ;;
    let ' (hd, iargs) := decompose_app etm in
    (* 2. Check and get the mdecl *)
    match hd with
    | tInd idecl _ =>
      let kname := inductive_mind idecl in
      let pos_block := inductive_ind idecl in
      mdecl <- tmQuoteInductive (inductive_mind idecl) ;;
      (* DEBUG FUNCTIONS *)
        (* Check computation uniform parameters *)
        nb_uparams <- tmEval cbv (debug_nuparams kname mdecl) ;;
        tmPrintb print_nuparams nb_uparams ;;
        (* Check computation strict positive parameters *)
        strpos_uparams <- tmEval cbv (strpos_preprocess_ctors kname mdecl E) ;;
        tmPrintb print_strpos strpos_uparams ;;
        (* Check computation custom parametericity *)
        (* cparam <- tmEval cbv (custom_param mdecl) ;;
        _ <- tmMkInductive true (mind_body_to_entry cparam) ;;
        tmPrintb print_cparam (snd kname ^ "_param1") ;; *)
        tmPrintb print_cparam 0;;
      let pdecl:= preprocess_parameters kname pos_block mdecl E in
      (* 3. Get the pos_block body under scrutiny *)
      match nth_error pdecl.(pmb_ind_bodies) pos_block with
      | Some indb =>
        (* 4. Compute type *)
        named_ty_rec <- tmEval all (gen_rec_type mdecl pdecl U E indb) ;;
        tmPrintb (print_type) named_ty_rec ;;
        (* 5. Compute term *)
        (* named_tm_rec <- tmEval all (gen_rec_term pdecl U E) ;;
        tmPrintb (print_term && (negb post)) named_tm_rec ;; *)
        (* Return *)
        tmReturn (tRel 0, named_ty_rec)
        (* tmReturn (debruijn_tm_rec, debruijn_ty_rec) *)
      | None    => tmFail "Error"
          end
    | _ => tmPrint hd ;; tmFail " is not an inductive"
    end.



      (* Get the mdecl definition and preprocess it *)

      (* lnat <- tmEval cbv (debug_nuparams mdecl) ;; *)
      (* tmPrintb print_nuparams mdecl ;; *)





  Inductive mode :=
  | Debug    : mode
  | TestType : mode
  | TestTerm : mode
  | TestBoth : mode.



  Definition gen_rec_mode_options {A} (m : mode)
      (s : A) : TemplateMonad unit :=
    t <- gen_rec_options s ;;
    let tm_rec := fst t in
    let ty_rec := snd t in
    match m with
    | Debug => tmMsg ""
    | TestType =>  x <- (tmUnquote ty_rec) ;;
                    ker_ty_rec <- (tmEval hnf x.(my_projT2)) ;;
                    tmPrint ker_ty_rec
    | TestTerm =>  x <- (tmUnquote tm_rec) ;;
                    ker_tm_rec <- (tmEval hnf x.(my_projT2)) ;;
                    tmPrint ker_tm_rec
    | TestBoth  => tmFail "bugs at the moment"
                  (* x <- (tmUnquote ty_rec) ;;
                  ker_ty_rec <- (tmEval hnf x.(my_projT2)) ;;
                  ker_tm_rec <- tmUnquoteTyped ker_ty_rec tm_rec ;;
                  tmPrint ker_tm_rec ;;
                  tmPrint ker_ty_rec ;;    *)
    end.

  Definition print_rec_options (q : qualid) :=
    if print_cparam then printInductive q else tmMsg "";;
    if print_type   then printConstantType (q ^ "_ind") true else tmMsg "";;
    if print_term   then printConstantBody (q ^ "_ind") true else tmMsg "".

End TestFunctions.

(* Debug preprocessing *)
(* Definition print_rec := print_rec_options true false false.
Definition gen_rec {A} : A -> _ := gen_rec_mode_options false true false Debug. *)

(* Debug Types  *)
(* Definition print_rec := print_rec_options false true false.
Definition gen_rec {A} : A -> _ := gen_rec_mode_options true false true Debug. *)
(* Debug Terms  *)
(* Definition print_rec := print_rec_options false false true.
Definition gen_rec E {A} : A -> _ := gen_rec_mode_options false false false true false E Debug. *)

(* Test Types   *)
Definition print_rec := print_rec_options false false false.
Definition gen_rec {A} : A -> _ := gen_rec_mode_options false false false false TestType.
(* Test Terms  *)
(* Definition print_rec := print_rec_options false false false.
Definition gen_rec E {A} : A -> _ := gen_rec_mode_options false false false false false E TestTerm. *)

