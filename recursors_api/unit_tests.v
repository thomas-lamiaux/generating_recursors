From RecAPI Require Export api_debruijn.
From RecAPI Require Import commons.
From RecAPI Require Import generate_rec_type.
From RecAPI Require Import generate_rec_term.

From MetaCoq.Utils Require Export utils.
From MetaCoq.Template Require Export All.
From RecAPI Require Import preprocess_uparams.
From RecAPI Require Export preprocess_strpos_uparams.

Import MCMonadNotation.


(* Definition preprocess_uparams : kername -> mutual_inductive_body -> global_env -> nat :=
  fun _ mdecl _ => mdecl.(ind_npars).

Definition debug_preprocess_uparams : kername -> mutual_inductive_body -> global_env -> list (list nat) :=
  fun _ _ _ => [].

Definition preprocess_strpos : kername -> mutual_inductive_body -> global_env -> list bool :=
  fun _ mdecl _ => repeat true mdecl.(ind_npars). *)


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

Definition GetKname : qualid -> TemplateMonad kername :=
  fun q => gref <- tmLocate1 q ;;
  match gref with
  | IndRef x => tmReturn x.(inductive_mind)
  | ConstRef kname => tmReturn kname
  | _ => tmFail (String.append "Error getting kername of " q)
  end.

(* Given an inductive type => returns kname, medecl, kname_param1, kname_param1_term  *)
Definition get_paramE {A} (s : A) : TemplateMonad unit :=
  ' (E, tm) <- tmQuoteRec s ;;
  etm <- tmEval hnf tm ;;
  let ' (hd, iargs) := decompose_app etm in
  match hd with
  | tInd (mkInd kname ind_pos) _ =>
    mdecl <- tmQuoteInductive kname ;;
    let nb_uparams := preprocess_uparams kname mdecl E in
    let strpos := preprocess_strpos kname mdecl E in
    let q := snd kname in
    kname_pkname <- GetKname (q ^ "_param1") ;;
    kname_tkname <- GetKname (q ^ "_param1_term") ;;
      tmDefinition ("kmp_" ^ q)
      (mk_one_env_param kname nb_uparams strpos kname_pkname kname_tkname) ;;
      ret tt
  | _ => tmFail "Not an inductive"
  end.


Definition tmPrintb {A} (b : bool) (a : A) : TemplateMonad unit :=
  if b then a' <- tmEval cbv a ;; tmPrint a' else tmMsg "".

Definition tmPrintbInd (b : bool) (s : qualid) : TemplateMonad unit :=
  if b then printInductive s else tmMsg "".


Section TestFunctions.
  Context (print_nuparams print_strpos print_cparam print_type print_term : bool).
  Context (Ep : env_param).

Definition U := mk_output_univ (tSort sProp) (relev_sort (tSort sProp)).


  Definition gen_rec_options {A} (s : A) : TemplateMonad (term * term) :=
    (* 1. Get env and term *)
    x <- tmQuoteRec s ;;
    let ' (E, tm) := x in
    etm <- tmEval hnf tm ;;
    let ' (hd, iargs) := decompose_app etm in
    (* 2. Check and get the mdecl *)
    match hd with
    | tInd (mkInd kname pos_indb) _ =>
      mdecl <- tmQuoteInductive kname ;;
      (* 2.1 Compute Uniform Parameters *)
      let nb_uparams := preprocess_uparams kname mdecl E in
      tmPrintb print_nuparams (debug_preprocess_uparams kname mdecl E) ;;
      (* 2.2 Compute Strictly Positive Uniform Parameters *)
      strpos_uparams <- tmEval cbv (preprocess_strpos kname mdecl E) ;;
      tmPrintb print_strpos (preprocess_strpos kname mdecl E) ;;
      (* 2.3 Compute Custom Parametricity *)
      tmPrintb print_cparam 0;;
      (* 4. Compute type *)
      named_ty_rec <- tmEval all (gen_rec_type kname mdecl nb_uparams U E Ep pos_indb) ;;
      tmPrintb print_type named_ty_rec ;;
      (* 5. Compute term *)
      named_tm_rec <- tmEval all (gen_rec_term kname mdecl nb_uparams U E Ep pos_indb) ;;
      (* named_tm_rec <- tmEval all (tRel 0) ;; *)
      tmPrintb print_term named_tm_rec ;;
      (* Return *)
      tmReturn (named_ty_rec, named_tm_rec)
    | _ => tmPrint hd ;; tmFail " is not an inductive"
    end.




  Inductive mode :=
  | Debug    : mode
  | TestType : mode
  | TestTerm : mode
  | TestBoth : mode.



  Definition gen_rec_mode_options {A} (m : mode)
      (s : A) : TemplateMonad unit :=
    t <- gen_rec_options s ;;
    let ty_rec := fst t in
    let tm_rec := snd t in
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
Definition gen_rec {A} Ep : A -> _ := gen_rec_mode_options false false false true false Ep Debug. *)
(* Debug Terms  *)
Definition print_rec := print_rec_options false false true.
Definition gen_rec E {A} : A -> _ := gen_rec_mode_options false false false false true E Debug.

(* Test Types   *)
(* Definition print_rec := print_rec_options false false false.
Definition gen_rec {A} Ep : A -> _ := gen_rec_mode_options false false false false false Ep TestType. *)
(* Test Terms  *)
(* Definition print_rec := print_rec_options false false true.
Definition gen_rec E {A} : A -> _ := gen_rec_mode_options false false false false false E TestTerm. *)

