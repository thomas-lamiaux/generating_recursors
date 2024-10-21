From RecAPI Require Export api_debruijn.
From RecAPI Require Import commons.
From RecAPI Require Import generate_rec_type.
From RecAPI Require Import generate_rec_term.

From MetaCoq.Utils Require Export utils.
From MetaCoq.Template Require Export All.
From MetaCoq.Template Require Import Pretty.

From RecAPI Require Import preprocess_uparams.
From RecAPI Require Export preprocess_strpos_uparams.
From RecAPI Require Export generate_custom_param.


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

Definition getInd (q : qualid) : TemplateMonad mutual_inductive_body :=
  kn <- tmLocate1 q ;;
  match kn with
  | IndRef ind => tmQuoteInductive ind.(inductive_mind)
  | _ => tmFail ("[" ^ q ^ "] is not an inductive")
  end.

Definition getCst (q : qualid) b : TemplateMonad constant_body :=
  kn <- tmLocate1 q ;;
  match kn with
  | ConstRef kn => tmQuoteConstant kn b
  | _ => tmFail ("[" ^ q ^ "] is not a constant")
  end.

Definition getCstBody (q : qualid) b : TemplateMonad (option term) :=
  x <- (getCst q b) ;;
  tmEval all x.(cst_body).

Definition getCstType (q : qualid) b : TemplateMonad term :=
x <- (getCst q b) ;;
tmEval all x.(cst_type).


Definition printMdecl (q : qualid): TemplateMonad unit :=
  getInd q >>= tmPrint.

Definition printMentry (q : qualid): TemplateMonad unit :=
  mdecl <- getInd q ;;
  mentry <- tmEval cbv (mind_body_to_entry mdecl) ;;
  tmPrint mentry.

Definition pp_printMdecl (q : qualid): TemplateMonad unit :=
  mdecl <- getInd q ;;
  str <- tmEval cbv (print_mib empty_global_env false false mdecl) ;;
  tmMsg str.

Definition printCstBody (q : qualid) b : TemplateMonad unit :=
  getCstBody q b >>= tmPrint.

Definition printCstType (q : qualid) b : TemplateMonad unit :=
  getCstBody q b >>= tmPrint.

Definition empty_global_env_ext : global_env_ext :=
  (empty_global_env, Monomorphic_ctx).

Definition pp_printCstBody (q : qualid) b : TemplateMonad unit :=
  db <- getCstBody q b ;;
  match db with
  | Some db => tmEval all (print_term empty_global_env_ext [] false db) >>= tmMsg
  | None => tmPrint "None"
  end.

Definition pp_printCstType (q : qualid) b : TemplateMonad unit :=
  ty <- getCstType q b ;;
  str <- tmEval all (print_term empty_global_env_ext [] false ty) ;;
  tmMsg str.


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

(* Definition tmPrintbInd (b : bool) (s : qualid) : TemplateMonad unit :=
  if b then printInductive s else tmMsg "". *)


Section TestFunctions.
  Context (print_nuparams print_strpos print_cparam print_type print_term : bool).
  Context (Ep : env_param).

Definition U := mk_output_univ (tSort sProp) (relev_sort (tSort sProp)).


  Definition gen_rec_options {A} (s : A) : TemplateMonad (kername * mutual_inductive_entry * term * term) :=
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
      mentry <- tmEval all (custom_param kname mdecl nb_uparams strpos_uparams) ;;
      (if print_cparam then tmPrint mentry else tmMsg "") ;;
      (* 4. Compute type *)
      named_ty_rec <- tmEval all (gen_rec_type kname mdecl nb_uparams U E Ep pos_indb) ;;
      tmPrintb print_type named_ty_rec ;;
      (* 5. Compute term *)
      named_tm_rec <- tmEval all (gen_rec_term kname mdecl nb_uparams U E Ep pos_indb) ;;
      (* named_tm_rec <- tmEval all (tRel 0) ;; *)
      tmPrintb print_term named_tm_rec ;;
      (* Return *)
      tmReturn (kname, mentry, named_ty_rec, named_tm_rec)
    | _ => tmPrint hd ;; tmFail " is not an inductive"
    end.




  Inductive mode :=
  | Debug      : mode
  | TestType   : mode
  | TestTerm   : mode
  | TestCParam : mode.


  Definition gen_rec_mode_options {A} (m : mode)
      (s : A) : TemplateMonad unit :=
    ' (kname, mentry, ty_rec, tm_rec) <- gen_rec_options s ;;
    (* let ty_rec := fst t in
    let tm_rec := snd t in *)
    match m with
    | Debug => tmMsg ""
    | TestType =>  x <- (tmUnquote ty_rec) ;;
                    ker_ty_rec <- (tmEval hnf x.(my_projT2)) ;;
                    tmPrint ker_ty_rec
    | TestTerm =>  x <- (tmUnquote tm_rec) ;;
                    ker_tm_rec <- (tmEval hnf x.(my_projT2)) ;;
                    tmPrint ker_tm_rec
    | TestCParam => tmMkInductive false mentry ;;
                    pp_printMdecl ((snd kname) ^ "_cparam")
    end.

  Definition print_rec_options (m : mode) (q : qualid) :=
    match m with
    | Debug => if print_cparam then printMentry (q ^ "_param1") else tmMsg "";;
               if print_type   then printCstType (q ^ "_ind") true else tmMsg "";;
               if print_term   then printCstBody (q ^ "_ind") true else tmMsg ""
    | TestType => pp_printCstType (q ^ "_ind") true
    | TestTerm => pp_printCstBody (q ^ "_ind") true
    | TestCParam => pp_printMdecl (q ^ "_param1")
    end.

End TestFunctions.

(* Debug Custom Param *)
(* Definition print_rec := print_rec_options true false false Debug.
Definition gen_rec {A} Ep : A -> _ := gen_rec_mode_options false false true false false Ep Debug. *)
(* Debug Types  *)
(* Definition print_rec := print_rec_options false true false.
Definition gen_rec {A} Ep : A -> _ := gen_rec_mode_options false false false true false Ep Debug. *)
(* Debug Terms  *)
(* Definition print_rec := print_rec_options false false true.
Definition gen_rec E {A} : A -> _ := gen_rec_mode_options false false false false true E Debug. *)


(* Test Custom Param *)
Definition print_rec := print_rec_options true false false TestCParam.
Definition gen_rec {A} Ep : A -> _ := gen_rec_mode_options false false false false false Ep TestCParam.
(* Test Types   *)
(* Definition print_rec := print_rec_options true false false Debug.
Definition gen_rec {A} Ep : A -> _ := gen_rec_mode_options false false false false false Ep TestType. *)
(* Test Terms  *)
(* Definition print_rec := print_rec_options false false true.
Definition gen_rec E {A} : A -> _ := gen_rec_mode_options false false false false false E TestTerm. *)

