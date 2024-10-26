From RecAPI Require Export api_debruijn.

From MetaCoq.Utils Require Export utils.
From MetaCoq.Template Require Export All.
From MetaCoq.Template Require Import Pretty.

From RecAPI Require Import uniform_parameters.
From RecAPI Require Import strictly_positive_uniform_parameters.
(* From RecAPI Require Import recursor_type.
From RecAPI Require Import recursor_term. *)
(* From RecAPI Require Import custom_parametricity.
From RecAPI Require Import fundamental_theorem_type.
From RecAPI Require Import fundamental_theorem_term. *)


Import MCMonadNotation.


(* Definition preprocess_uparams : kername -> mutual_inductive_body -> global_env -> nat :=
  fun _ mdecl _ => 0.

Definition debug_preprocess_uparams : kername -> mutual_inductive_body -> global_env -> list (list nat) :=
  fun _ _ _ => []. *)

(* Definition preprocess_strpos : kername -> mutual_inductive_body -> global_env -> list bool :=
  fun _ mdecl _ => repeat true mdecl.(ind_npars). *)

Definition error_mentry : mutual_inductive_entry :=
  Build_mutual_inductive_entry None Finite [] [] (Monomorphic_entry ContextSet.empty) false None None.


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

(* Given an inductive type => returns kname, medecl, kname_param1, kname_param1_term  *)
Definition get_paramE {A} (s : A) : TemplateMonad unit :=
  ' (E, tm) <- tmQuoteRec s ;;
  etm <- tmEval hnf tm ;;
  let ' (hd, iargs) := decompose_app etm in
  match hd with
  | tInd (mkInd kname ind_pos) _ =>
    mdecl <- tmQuoteInductive kname ;;
    nb_uparams <- tmEval cbv (preprocess_uparams kname mdecl E) ;;
    (* let nb_uparams := mdecl.(ind_npars) in *)
    strpos <- tmEval cbv (preprocess_strpos kname mdecl nb_uparams E []) ;;
    let q := snd kname in
    kname_pkname <- GetKname (q ^ "_param1") ;;
    kname_pkname <- tmEval cbv kname_pkname;;
    kname_tkname <- GetKname (q ^ "_param1_term") ;;
    kname_tkname <- tmEval cbv kname_tkname;;
      tmDefinition ("kmp_" ^ q)
      (mk_one_param_env kname nb_uparams strpos kname_pkname kname_tkname) ;;
      ret tt
  | _ => tmFail "Not an inductive"
  end.


Definition tmPrintb {A} (b : bool) (a : A) : TemplateMonad unit :=
  if b then a' <- tmEval cbv a ;; tmPrint a' else tmMsg "".


Section TestFunctions.
  Context (debug_nuparams debug_strpos : bool).
  Context (debug_cparam debug_fth_ty debug_fth_tm : bool).
  Context (debug_type debug_term : bool).
  Context (Ep : param_env).

Definition U := mk_output_univ (tSort sProp) (relev_sort (tSort sProp)).


  Definition gen_rec_options {A} (s : A) : TemplateMonad _ :=
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
      tmPrintb debug_nuparams nb_uparams ;;
      tmPrintb debug_nuparams (debug_preprocess_uparams kname mdecl E) ;;
      (* 2.2 Compute Strictly Positive Uniform Parameters *)
      strpos_uparams <- tmEval cbv (preprocess_strpos kname mdecl nb_uparams E Ep) ;;
      tmPrintb debug_strpos strpos_uparams ;;
      tmPrintb debug_strpos (debug_preprocess_strpos kname mdecl nb_uparams E Ep) ;;
      (* 2.3 Compute Custom Parametricity *)
      (* mentry <- tmEval all (custom_param kname mdecl nb_uparams strpos_uparams E Ep) ;; *)
      (* (if debug_cparam then tmPrint error_mentry else tmMsg "") ;; *)
      (* 4. Compute type *)
      (* let nb_uparams := 0 in
      named_ty_rec <- tmEval cbv (gen_rec_type kname mdecl nb_uparams U E Ep pos_indb) ;;
      tmPrintb debug_type named_ty_rec ;; *)
      (* 5. Compute term *)
      (* named_tm_rec <- tmEval cbv (gen_rec_term kname mdecl nb_uparams U E Ep pos_indb) ;; *)
      (* named_tm_rec <- tmEval all (tRel 0) ;; *)
      (* tmPrintb debug_term named_tm_rec ;; *)
      (* Return *)
      (* tmReturn (named_ty_rec, named_tm_rec) *)
      tmReturn (tRel 0, tRel 0)
      (* tmReturn (E, kname, mdecl, pos_indb, nb_uparams, strpos_uparams, error_mentry, named_ty_rec, named_tm_rec) *)
    | _ => tmPrint hd ;; tmFail " is not an inductive"
    end.




  Inductive mode :=
  | Debug      : mode
  | TestType   : mode
  | TestTerm   : mode
  | TestCParam : mode.

  #[using="All"]
  Definition gen_rec_mode_options {A} (m : mode)
      (s : A) : TemplateMonad unit :=
    (* ' (E, kname, mdecl, pos_indb, nb_uparams, strpos_uparams, mentry, ty_rec, tm_rec) <- gen_rec_options s ;; *)
    ' (ty_rec, tm_rec) <- gen_rec_options s ;;
    match m with
    | Debug => tmMsg ""
    | _ => tmMsg ""
    (**
    | TestType =>  x <- (tmUnquote ty_rec) ;;
                    ker_ty_rec <- (tmEval hnf x.(my_projT2)) ;;
                    tmPrint ker_ty_rec
    | TestTerm =>  x <- (tmUnquote tm_rec) ;;
                    ker_tm_rec <- (tmEval hnf x.(my_projT2)) ;;
                    tmPrint ker_tm_rec
    | TestCParam =>
         tmMkInductive false mentry ;;
        let qp := (snd kname) ^ "_cparam" in
        pp_printMdecl qp ;;
        knamep <- getKername qp ;;
        fth_ty <- tmEval cbv (fundamental_theorem_ty kname mdecl nb_uparams
                                strpos_uparams knamep pos_indb) ;;
        (if debug_fth_ty then tmPrint fth_ty else
          x <- (tmUnquote fth_ty) ;; ker_ty_rec <- (tmEval hnf x.(my_projT2)) ;;
          tmPrint ker_ty_rec) ;;
        fth_tm <- tmEval cbv (fundamental_theorem_term kname mdecl nb_uparams
          strpos_uparams knamep U E Ep pos_indb) ;;
        (if debug_fth_tm then tmPrint fth_tm else
        x <- (tmUnquote fth_tm) ;; ker_tm_rec <- (tmEval hnf x.(my_projT2)) ;;
        tmPrint ker_tm_rec) *)
    end.

  Definition print_rec_options (m : mode) (q : qualid) :=
    match m with
    | Debug =>
               if debug_cparam then printMentry (q ^ "_param1") else tmMsg "";;
               if debug_type   then printCstType (q ^ "_ind") true else tmMsg "";;
               if debug_term   then printCstBody (q ^ "_ind") true else tmMsg ""
    | TestType => pp_printCstType (q ^ "_ind") true
    | TestTerm => pp_printCstBody (q ^ "_ind") true
    | TestCParam => pp_printMdecl (q ^ "_param1")
    end.

End TestFunctions.




  (* DEBUG FUNCTIONS *)
(* -------------------------------------------------------------------------- *)

(* ### Debug Uniform Parameters ### *)
(* Definition print_rec := print_rec_options false false false Debug.
Definition gen_rec {A} Ep : A -> _ := gen_rec_mode_options true false false false false false false Ep Debug. *)

(* ### Debug Strictly Positive Uniform Parameters ### *)
Definition print_rec := print_rec_options false false false Debug.
Definition gen_rec {A} Ep : A -> _ := gen_rec_mode_options false true false false false false false Ep Debug.

(* ### Debug Recursor's Types ### *)
(* Definition print_rec := print_rec_options false false false Debug.
Definition gen_rec {A} Ep : A -> _ := gen_rec_mode_options false false false false false true false Ep Debug. *)

(* ### Debug Recursor's Terms ### *)
(* Definition print_rec := print_rec_options false false true Debug.
Definition gen_rec E {A} : A -> _ := gen_rec_mode_options true true false false false false true E Debug. *)

(* ### Debug Custom Param ### *)
(* Definition print_rec := print_rec_options true false false Debug.
Definition gen_rec {A} Ep : A -> _ := gen_rec_mode_options false false false false true false false Ep TestCParam. *)




  (* TEST FUNCTIONS *)
(* -------------------------------------------------------------------------- *)

(* ### Test Recursor's Types  ### *)
(* Definition print_rec := print_rec_options true false false TestType.
Definition gen_rec {A} Ep : A -> _ := gen_rec_mode_options false false false false false false false Ep TestType. *)

(* ### Test Recursor's Terms ### *)
(* Definition print_rec := print_rec_options false false false TestTerm.
Definition gen_rec E {A} : A -> _ := gen_rec_mode_options false false false false false false false E TestTerm. *)

(* ### Test Custom Param ### *)
(* Definition print_rec := print_rec_options true false false TestCParam.
Definition gen_rec {A} Ep : A -> _ := gen_rec_mode_options false false false false false false false Ep TestCParam. *)
