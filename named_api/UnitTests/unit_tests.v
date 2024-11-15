From NamedAPI Require Export api_debruijn.

From MetaCoq.Utils Require Export utils.
From MetaCoq.Template Require Export All.
From MetaCoq.Template Require Import Pretty.

(* Preprocessing *)
From NamedAPI Require Import uniform_parameters.
From NamedAPI Require Import strictly_positive_uniform_parameters.

(* Generation of Recursors *)
From NamedAPI Require Import recursors.

(* Generation of Functoriality *)
From NamedAPI Require Import functoriality.
(* From NamedAPI Require Import recursor_term. *)

(* Generation of Parametricity *)
From NamedAPI Require Import custom_parametricity.
From NamedAPI Require Import fundamental_theorem.


Import MCMonadNotation.


(* Definition preprocess_uparams : kername -> mutual_inductive_body -> global_env -> nat :=
  fun _ mdecl _ => 0.

Definition debug_preprocess_uparams : kername -> mutual_inductive_body -> global_env -> list (list nat) :=
  fun _ _ _ => []. *)

(* Definition preprocess_strpos : kername -> mutual_inductive_body -> global_env -> list bool :=
  fun _ mdecl _ => repeat true mdecl.(ind_npars). *)

(* Definition error_mentry : mutual_inductive_entry :=
  Build_mutual_inductive_entry None Finite [] [] (Monomorphic_entry ContextSet.empty) false None None. *)


(* ############################
   ###  Printing functions  ###
   ############################ *)

Definition getKername (q : qualid) : TemplateMonad kername :=
  kn <- tmLocate1 q ;;
  match kn with
  | IndRef (mkInd kname _) => tmReturn kname
  | _ => tmFail ("[" ^ q ^ "] is not an inductive")
  end.

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
  getCstType q b >>= tmPrint.

Definition empty_global_env_ext : global_env_ext :=
  (empty_global_env, Monomorphic_ctx).

Definition pp_printCstBody (q : qualid) b : TemplateMonad unit :=
  db <- getCstBody q b ;;
  match db with
  | Some db => tmEval cbv (print_term empty_global_env_ext [] false db) >>= tmMsg
  | None => tmPrint "None"
  end.

Definition pp_printCstType (q : qualid) b : TemplateMonad unit :=
  ty <- getCstType q b ;;
  str <- tmEval cbv (print_term empty_global_env_ext [] false ty) ;;
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

(* Given an inductive type => returns kname, medecl, kname_param1, kname_param1_term *)
Definition get_paramEp {A} (s : A) Ep : TemplateMonad unit :=
  ' (E, tm) <- tmQuoteRec s ;;
  etm <- tmEval hnf tm ;;
  let ' (hd, iargs) := decompose_app etm in
  match hd with
  | tInd (mkInd kname ind_pos) _ =>
    mdecl <- tmQuoteInductive kname ;;
    nb_uparams <- tmEval cbv (preprocess_uparams kname mdecl E) ;;
    strpos <- tmEval cbv (preprocess_strpos kname mdecl nb_uparams E Ep) ;;
    let q := snd kname in
    cparam_kname <- GetKname (q ^ "_param1") ;;
    cparam_kname <- tmEval cbv cparam_kname;;
    fdt_kname <- GetKname (q ^ "_param1_term") ;;
    fdt_kname <- tmEval cbv fdt_kname;;
    func_kname <- GetKname (q ^ "_func") ;;
    func_kname <- tmEval cbv func_kname;;
      tmDefinition ("kmp_" ^ q)
      (mk_one_param_env kname nb_uparams strpos cparam_kname fdt_kname func_kname) ;;
      ret tt
  | _ => tmFail "Not an inductive"
  end.


Definition tmPrintb {A} (b : bool) (a : A) : TemplateMonad unit :=
  if b then a' <- tmEval lazy a ;; tmPrint a' else tmMsg "".

  Inductive TestMode :=
  | TestRecType  : TestMode
  | TestRecTerm  : TestMode
  | TestFuncType : TestMode
  | TestFuncTerm : TestMode
  | TestCParam   : TestMode
  | StopTests    : TestMode.

Section TestFunctions.
  Context (debug_uparams debug_strpos : bool).
  Context (m : TestMode).
  Context (debug_rec_type debug_rec_term : bool).
  Context (debug_func_type debug_func_term : bool).
  Context (debug_cparam debug_fth_ty debug_fth_tm : bool).
  Context (Ep : param_env).

Definition U := mk_output_univ (tSort sProp) (relev_sort (tSort sProp)).

Definition UnquoteAndPrint (x : term) : TemplateMonad unit :=
  p <- (tmUnquote x) ;;
  y <- (tmEval hnf p.(my_projT2)) ;;
  tmPrint y.

  #[using="All"]
  Definition generate_options {A} (s : A) : TemplateMonad unit :=
    (* 1. Get env and term *)
    x <- tmQuoteRec s ;;
    let ' (E, tm) := x in
    etm <- tmEval hnf tm ;;
    let ' (hd, iargs) := decompose_app etm in
    (* 2. Check and get the mdecl *)
    match hd with
    | tInd (mkInd kname pos_indb) _ =>
      mdecl <- tmQuoteInductive kname ;;
      (* 2.1 Compute uniform parameters *)
      nb_uparams <- tmEval cbv (preprocess_uparams kname mdecl E) ;;
      if debug_uparams
      then tmPrint nb_uparams ;;
           debug_uparam <- tmEval cbv (debug_preprocess_uparams kname mdecl E) ;;
           tmPrint debug_uparams
      (* 2.2 Compute Strictly Positive Uniform Parameters *)
      else strpos_uparams <- tmEval cbv (preprocess_strpos kname mdecl nb_uparams E Ep) ;;
      if debug_strpos
      then tmPrint strpos_uparams ;;
           debug_strpos <- tmEval cbv (debug_preprocess_strpos kname mdecl nb_uparams E Ep) ;;
           tmPrint debug_strpos
      (* 2.3 Check Rec Type || Rec Term || Custom Param *)
      else match m with
      | TestRecType =>
          ty_rec <- tmEval cbv (gen_rec_type kname mdecl nb_uparams U E Ep pos_indb) ;;
          if debug_rec_type then tmPrint ty_rec else UnquoteAndPrint ty_rec
      | TestRecTerm =>
          tm_rec <- tmEval cbv (gen_rec_term kname mdecl nb_uparams U E Ep pos_indb) ;;
          if debug_rec_term then tmPrint tm_rec else UnquoteAndPrint tm_rec
      | TestFuncType =>
          ty_func <- tmEval cbv (gen_functoriality_type kname mdecl nb_uparams strpos_uparams pos_indb) ;;
          if debug_func_type then tmPrint ty_func else UnquoteAndPrint ty_func
      | TestFuncTerm =>
          tm_func <- tmEval cbv (gen_functoriality_term kname mdecl nb_uparams strpos_uparams E Ep pos_indb) ;;
          if debug_func_term then tmPrint tm_func else UnquoteAndPrint tm_func
      | TestCParam =>
          (* Test Generation Custom Parametricty *)
          tmPrint "Custom Parametricty:" ;;
          mentry <- tmEval all (custom_param kname mdecl nb_uparams strpos_uparams E Ep) ;;
          if debug_cparam then tmPrint mentry else
          tmMkInductive false mentry ;;
          pp_printMdecl ((snd kname) ^ "_cparam") ;;
          knamep <- getKername ((snd kname) ^ "_cparam") ;;
          tmMsg "" ;;
          (* Test Generation Fundamental Theorem's Type *)
          tmPrint "Fundamental Theorem's Type:" ;;
          fth_ty <- tmEval cbv (fundamental_theorem_type kname mdecl nb_uparams strpos_uparams knamep pos_indb) ;;
          if debug_fth_ty then tmPrint fth_ty else UnquoteAndPrint fth_ty ;;
          tmMsg "" ;;
          (* Test Generation Fundamental Theorem *)
          tmPrint "Proof of the Fundamental Theorem:" ;;
           fth_tm <- tmEval cbv (fundamental_theorem_term kname mdecl nb_uparams strpos_uparams knamep E Ep pos_indb) ;;
          if debug_fth_tm then tmPrint fth_tm else UnquoteAndPrint fth_tm
      | _ => tmMsg ""
      end
    | _ => tmFail " is not an inductive"
    end.


  Definition print_rec_options (m : TestMode) (q : qualid) :=
    match m with
    | TestRecType => if debug_rec_type then printCstType (q ^ "_ind") true else pp_printCstType (q ^ "_ind") true
    | TestRecTerm => if debug_rec_term then printCstBody (q ^ "_ind") true else pp_printCstBody (q ^ "_ind") true
    | TestCParam  => if debug_cparam then printMentry  (q ^ "_param1") else pp_printMdecl (q ^ "_param1")
    | _ => tmMsg ""
    end.

End TestFunctions.




  (* DEBUG FUNCTIONS *)
(* -------------------------------------------------------------------------- *)

    (* ### Debug Preprocessing ### *)

(* Definition print_rec := print_rec_options false false false StopTests.
Definition generate {A} Ep : A -> _ := generate_options true false StopTests
                                        false false false false false false false Ep. *)

(* Definition print_rec := print_rec_options false false false StopTests.
Definition generate {A} Ep : A -> _ := generate_options false true StopTests
                                        false false false false false false false Ep. *)

    (* ### Debug Recursor ### *)

(* Definition print_rec := print_rec_options true false false TestRecType.
Definition generate {A} Ep : A -> _ := generate_options false false TestRecType
                                        true false false false false false false Ep. *)

(* Definition print_rec := print_rec_options false true false TestRecTerm.
Definition generate {A} Ep : A -> _ := generate_options false false TestRecTerm
                                        false true false false false false false Ep. *)

    (* ### Debug Functoriality *)

(* Definition print_rec := print_rec_options false false false TestFuncType.
Definition generate {A} Ep : A -> _ := generate_options false false TestFuncType
                                        false false true false false false false Ep. *)

(* Definition print_rec := print_rec_options false false false TestFuncTerm.
Definition generate {A} Ep : A -> _ := generate_options false false TestFuncTerm
                                        false false false true false false false Ep. *)

    (* ### Debug Custom Param ### *)

(* Definition print_rec := print_rec_options false false true TestCParam.
Definition generate {A} Ep : A -> _ := generate_options false false TestCParam
                                        false false false false true false false Ep. *)




  (* TEST FUNCTIONS *)
(* -------------------------------------------------------------------------- *)

    (* ### Test Recursors  ### *)

(* Definition print_rec := print_rec_options false false false TestRecType.
Definition generate {A} Ep : A -> _ := generate_options false false TestRecType
                                        false false false false false false false Ep. *)

Definition print_rec := print_rec_options false false false TestRecTerm.
Definition generate {A} Ep : A -> _ := generate_options false false TestRecTerm
                                        false false false false false false false Ep.

    (* ### Test Functoriality  ### *)

(* Definition print_rec := print_rec_options false false false TestFuncType.
Definition generate {A} Ep : A -> _ := generate_options false false TestFuncType
                                        false false false false false false false Ep. *)

(* Definition print_rec := print_rec_options false false false TestFuncTerm.
Definition generate {A} Ep : A -> _ := generate_options false false TestFuncTerm
                                        false false false false false false false Ep. *)

    (* ### Test Custom Param ### *)

(* Definition print_rec := print_rec_options true false false TestCParam.
Definition generate {A} Ep : A -> _ := generate_options false false TestCParam
                                        false false false false false true false Ep. *)

(* Definition print_rec := print_rec_options true false false TestCParam.
Definition generate {A} Ep : A -> _ := generate_options false false TestCParam
                                        false false false false false false true Ep. *)

(* Definition print_rec := print_rec_options true false false TestCParam.
Definition generate {A} Ep : A -> _ := generate_options false false TestCParam
                                        false false false false false false false Ep. *)