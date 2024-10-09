From Coq Require Export List.
Export ListNotations.

From MetaCoq.Utils Require Export utils.
From MetaCoq.Template Require Export All.


(* Aux Functions *)
Definition error_scope_term := tVar "ERROR_SCOPE".

Definition isSome {A} : option A -> bool :=
  fun x => match x with Some _ => true | _ => false end.


Definition fold_right_i {A B} : (nat -> B -> A -> A) -> A -> list B -> A :=
  fun f a =>
  let fix aux n l : A :=
    match l with
    | [] => a
    | b :: l => f n b (aux (S n) l)
  end in
  aux 0.

Definition fold_left_i {A B} : (nat -> A -> B -> A) -> list B -> A -> A :=
  fun f =>
  let fix aux n l a0 : A :=
    match l with
    | [] => a0
    | b :: l => aux (S n) l (f n a0 b)
  end in
  aux 0.

(*

This interface is inspired from work by Weituo DAI, and Yannick Forester

#############################
###      Constrains       ###
#############################

1. Be able to refer to variables indirectly by names
2. Keep track of the old variables for weakening
3. Be able to replace variables by term on the fly


#############################
###   Backend interface   ###
#############################


(* 0. Datastructre and General Purposed Functions *)
- info_decl : Type
- info : Type
- init_info : info

- fold_right_ie : {A} (nat -> A -> info -> (info -> term) -> term)
    (list A) -> info -> (info -> term) -> term
- fold_left_ie : {A} (nat -> A -> info -> (info -> term) -> term)
    (list A) -> info -> (info -> term) -> term
- add_idecl : info_decl -> info -> info
- add_pdecl : info_pdecl -> info -> info

(* 1. Access Var *)
- get_term      : ident -> info -> list term
- geti_term     : ident -> nat -> info -> term
- get_term_rev  : ident -> info -> list term
- geti_term_rev : ident -> nat -> info -> term

- get_type      : ident -> info -> list term
- geti_type     : ident -> nat -> info -> term
- get_type_rev  : ident -> info -> list term
- geti_type_rev : ident -> nat -> info -> term

- get_typing_context : info -> context

- get_pdecl : kername -> info -> info_pdecl

(* 2. Check var *)
Definition isVar_ident : ident -> nat -> info -> bool
Definition isVar_pos : ident -> nat -> nat -> info -> bool


(* 3. Weakening *)
- weaken : info -> term -> term
- weaken_decl : info -> context_decl -> context_decl
- weaken_context : info -> context -> context

(* 4. Add variables *)
- init_info : info
- add_fresh_var : option ident -> context_decl -> info -> info
- add_old_var : option ident -> context_decl -> info -> info
- add_replace_var : option ident -> term -> info -> info
- add_unscoped_var : option ident -> context_decl -> term -> info -> info

- ++ context version

(* 5. Notations *)
- x <- f ;; for binding
- let* x y z <- f ;;   n-ary binding

(* 6. Debug *)
- Print_info : info -> list term
*)


(* 0. Datastructre and General Purposed Functions *)
Record info_decl : Type := mk_idecl
  { info_name    : option ident ;
    info_old     : bool ;
    info_replace : bool ;
    info_scope   : bool ;
    info_def     : context_decl ;
}.

Record info_pdecl : Type := mk_pdecl
{ info_kname       : kername ;
  info_uparams     : context ;
  info_nb_uparams  : nat ;
  info_nuparams    : context ;
  info_nb_nuparams : nat ;
  info_mdecl       : mutual_inductive_body ;
}.

Record info : Type := mk_info
{ info_context : list info_decl;
  info_ind : list info_pdecl ;
}.


Definition init_info : info := mk_info [] [].

Definition error_scope_idecl : info_decl :=
  mk_idecl (Some "ERROR SCOPE") false false true
    (mkdecl (mkBindAnn (nNamed "ERROR") Relevant) (Some error_scope_term) error_scope_term).

Axiom ERROR : forall A, A.
Arguments ERROR {_}.

Definition error_scope_pdecl : info_pdecl := ERROR.

(* 0. General Purposed  *)
Definition fold_right_ie {A B} (tp : nat -> A -> info -> (info -> B) -> B)
  (l:list A) (e:info) (t : info -> B) : B :=
  let fix aux l e n t : B :=
    match l with
    | [] => t e
    | a :: l => tp n a e (fun e => aux l e (S n) t)
  end in
  aux l e 0 t.

Definition fold_left_ie {A B} (tp : nat -> A -> info -> (info -> B) -> B)
  (l:list A) (e:info) (t : info -> B) : B :=
  let fix aux l e n t : B :=
    match l with
    | [] => t e
    | a :: l => aux l e (S n) (fun e => tp n a e t)
  end in
  aux l e 0 t.

Definition add_idecl : info_decl -> info -> info :=
  fun idecl e => mk_info (idecl :: e.(info_context)) e.(info_ind).

Definition add_pdecl : info_pdecl -> info -> info :=
  fun pdecl e => mk_info e.(info_context) (pdecl :: e.(info_ind)).


(* 1. Get terms and types *)

(* 1.1 Get terms selectively *)
Definition get_term_idecl : nat -> info_decl -> term :=
  fun pos_idecl idecl =>
  match idecl.(info_def).(decl_body) with
  | Some tm => if idecl.(info_replace)
                then (if idecl.(info_scope) then lift0 (S pos_idecl) tm  else lift0 pos_idecl tm)
               else tRel pos_idecl
  | None => tRel pos_idecl
  end.

Definition get_type_idecl : nat -> info_decl -> term :=
  fun pos_idecl idecl => lift0 (S pos_idecl) idecl.(info_def).(decl_type).

Definition get_info : (nat -> info_decl -> term) -> (info_decl -> bool) ->  info -> list term :=
  fun f p e =>
  let fix aux i e :=
  match e with
  | [] => []
  | idecl :: e =>
    let next := (if idecl.(info_scope) then aux (S i) e else aux i e) in
    if p idecl then f i idecl :: next else next
  end in
  aux 0 e.(info_context).

Definition get_term_info : (info_decl -> bool) -> info -> list term :=
  get_info get_term_idecl.

Definition get_type_info : (info_decl -> bool) -> info -> list term :=
  get_info get_type_idecl.


(* 1.2 filter predicate *)
Definition filter_name : ident -> info_decl -> bool :=
  fun i idecl => eq_option eqb idecl.(info_name) (Some i).


(* 1.3 Get terms *)
Definition get_term : ident -> info -> list term :=
  fun i e => rev (get_term_info (filter_name i) e).

Definition geti_term : ident -> nat -> info -> term :=
  fun i n e => nth n (get_term i e) error_scope_term.

Definition get_term_rev : ident -> info -> list term :=
  fun i e => get_term_info (filter_name i) e.

Definition geti_term_rev : ident -> nat -> info -> term :=
  fun i n e => nth n (get_term_rev i e) error_scope_term.


(* 1.4 Acces types *)
Definition get_type : ident -> info -> list term :=
  fun i e => rev (get_type_info (filter_name i) e).

Definition geti_type : ident -> nat -> info -> term :=
  fun i n e => nth n (get_type i e) error_scope_term.

Definition get_type_rev : ident -> info -> list term :=
  fun i e => get_type_info (filter_name i) e.

Definition geti_type_rev : ident -> nat -> info -> term :=
  fun i n e => nth n (get_type_rev i e) error_scope_term.

  (* Works ? *)
Definition get_typing_context : info -> context :=
  fun e => map info_def e.(info_context).

Definition get_aname : ident -> info -> list aname :=
  fun s e => map (fun x =>x.(info_def).(decl_name)) (filter (filter_name s) e.(info_context)).

(* 1.5 Access inductive type *)
Definition get_pdecl : kername -> info -> info_pdecl :=
  fun kname info =>
    match find (fun pdecl => eqb pdecl.(info_kname) kname) info.(info_ind) with
    | Some pdecl => pdecl
    | None => error_scope_pdecl
    end.

Definition get_uparams : kername -> info -> context :=
  fun kname e => (get_pdecl kname e).(info_uparams).

Definition get_nb_uparams : kername -> info -> nat :=
  fun kname e => (get_pdecl kname e).(info_nb_uparams).

Definition get_nuparams : kername -> info -> context :=
  fun kname e => (get_pdecl kname e).(info_nuparams).

Definition get_nb_nuparams : kername -> info -> nat :=
  fun kname e => (get_pdecl kname e).(info_nb_nuparams).

Definition get_params : kername -> info -> context :=
  fun kname e => (get_pdecl kname e).(info_mdecl).(ind_params).

Definition get_nb_params : kername -> info -> nat :=
  fun kname e => (get_pdecl kname e).(info_mdecl).(ind_npars).

Definition get_mdecl : kername -> info -> mutual_inductive_body :=
  fun kname e => (get_pdecl kname e).(info_mdecl).

Definition get_ind_bodies : kername -> info -> list one_inductive_body :=
  fun kname e => (get_pdecl kname e).(info_mdecl).(ind_bodies).

Definition get_indb : kername -> nat -> info -> one_inductive_body :=
  fun kname pos_indb e => nth pos_indb (get_ind_bodies kname e) ERROR.

Definition get_relevance : kername -> nat -> info -> relevance :=
  fun kname pos_indb e => (get_indb kname pos_indb e).(ind_relevance).

Definition get_ctor : kername -> nat -> nat -> info -> constructor_body :=
  fun kname pos_indb pos_ctor e => nth pos_ctor (get_indb kname pos_indb e).(ind_ctors) ERROR.


(* 2. Check var *)
Definition get_ident : nat -> info -> option ident :=
fun n e => (nth n e.(info_context) error_scope_idecl).(info_name).

(* Check the ident of the var at pos_var in the current scope *)
Definition check_var_ident : ident -> nat -> info -> bool :=
  fun i pos_var e => eqb (get_ident pos_var e) (Some i).

(* Check that the var register in pos_in_ident as the position pos_var in the current scope *)
Definition check_var_pos : ident -> nat -> nat -> info -> bool :=
  fun i pos_in_ident pos_var e =>
  match geti_term i pos_in_ident e with
  | tRel m => eqb m pos_var
  | _ => false
  end.



(* 3. Weakening and Lets *)
Definition get_subst : info -> list term :=
  get_term_info info_old.

Definition weaken : info -> term -> term :=
  fun e => subst0 (get_subst e).

Definition weaken_decl : info -> context_decl -> context_decl :=
  fun e cdecl =>
  let ' (mkdecl an db ty) := cdecl in
  mkdecl an (option_map (weaken e) db) (weaken e ty).


(* 4. Add variables *)
Definition add_old_var : option ident -> context_decl -> info -> info :=
  fun x decl e => add_idecl (mk_idecl x true false true (weaken_decl e decl)) e.

Definition add_old_context : option ident -> context -> info -> info :=
  fun x cxt e => fold_right (fun cdecl e => add_old_var x cdecl e) e cxt.

Definition add_fresh_var : option ident -> context_decl -> info -> info :=
  fun x decl e => add_idecl (mk_idecl x false false true decl) e.

Definition add_fresh_context : option ident -> context -> info -> info :=
  fun x cxt e => fold_right (fun cdecl e => add_fresh_var x cdecl e) e cxt.

Definition add_replace_var : option ident -> context_decl -> term -> info -> info :=
  fun x cxt tm e => let ' mkdecl an _ ty := weaken_decl e cxt in
                    add_idecl (mk_idecl x true true true (mkdecl an (Some tm) ty)) e.

Definition add_unscoped_var : option ident -> context_decl -> term -> info -> info :=
  fun x cxt tm e => let ' mkdecl an _ ty := weaken_decl e cxt in
                    add_idecl (mk_idecl x false true false (mkdecl an (Some tm) ty)) e.



(* Warning needs list of same length *)
(* terms are in reversed order *)
Definition add_replace_context : option ident -> context -> list term -> info -> info :=
  fun x cxt ltm e =>
  fold_right (fun ' (cdecl, tm) e => add_replace_var x cdecl tm e)
  e (combine cxt (rev ltm)).

Definition weaken_context : info -> context -> context :=
  fun e cxt =>
  fold_right_ie (
    fun i cdecl e t =>
    let cdecl' := weaken_decl e cdecl in
    let e' := add_old_var None cdecl e in
    cdecl' :: (t e'))
  cxt e (fun _ => []).


Definition add_mdecl_aux : kername -> nat -> mutual_inductive_body -> info_pdecl  :=
  fun kname nb_uparams mdecl =>
  let rev_params := rev mdecl.(ind_params) in
  mk_pdecl kname
          (rev (firstn nb_uparams rev_params)) nb_uparams
          (rev (skipn nb_uparams rev_params)) (mdecl.(ind_npars) - nb_uparams)
          mdecl.

Definition add_mdecl : kername -> nat -> mutual_inductive_body -> info -> info  :=
  fun kname nb_uparams mdecl e => add_pdecl (add_mdecl_aux kname nb_uparams mdecl) e.


(* 5. Notations *)
Notation "e ↑" := (weaken e) (at level 10).

Notation " x '<-' c1 ';;' c2" := ( c1 (fun x => c2))
  (at level 100, c1 at next level, right associativity).

Notation "let* x .. z '<-' c1 ';;' c2" := (c1 (fun x => .. (fun z => c2) ..))
(at level 100, x binder, z binder, c1 at next level, right associativity).

(* 6. Debug function *)
Notation "x ^^ y" := (String.append x y) (left associativity, at level 50).

Definition Print_info_decl : info_decl -> string :=
  fun ' (mk_idecl name old replace scope (mkdecl an db ty)) =>
       ("info_name := "    ^^ string_of_option (fun x => x) name ^^ " ; "
    ^^ "info_old := "      ^^ string_of_bool old ^^ " ; "
    ^^ "info_replace := "  ^^ string_of_bool replace ^^ " ; "
    ^^ "info_scope :=  "   ^^ string_of_bool scope ^^ " ; "
    ^^ "info_decl_type := " ^^ string_of_term ty ^^ " ; "
    ^^ "info_decl_body := " ^^ string_of_option (string_of_term) db).

Definition Print_info (e : info) : list term :=
  map (fun idecl => tVar (Print_info_decl idecl)) (rev e.(info_context)).




(* ########################################################################## *)
(* ########################################################################## *)
(* ########################################################################## *)

(*
#############################
###  Frontend interface   ###
#############################


(* 1. Keep Binders & 2. Add Binders *)
- kp_tLetIn  : aname -> term -> term -> option ident -> info -> (info -> term) -> term
- kp_binder  : (aname -> term -> term -> term) -> aname -> term ->
                option ident -> info -> (info -> term) -> term
- kp_tProd   : aname -> term -> option ident -> info -> (info -> term) -> term
- kp_tLambda : aname -> term -> option ident -> info -> (info -> term) -> term
- it_kp_binder : ...
- closure_params, closure_uparams, closure_nuparams,

- mk versions: mk_tLetIn, mk_binder, mk_tProd, mk_tLambda, it_mk_binder
- closure_indices

- mk_tFix / mk_tCase

(* 3. Inductive Types *)
- kname_to_ident : ident -> kername -> ident
- replace_ind : kername -> mutual_inductive_body -> info -> info
- split_params : nat -> mutual_inductive_body -> context * context
- make_ind : nat -> info -> term
- make_cst : nat -> nat -> info -> term

(* 4. Reduction *)
- reduce_except_lets : info -> term -> term
- reduce_full : info -> term -> term


(* 5. Decide Interface *)
- check_args_by_arg : (term -> info -> A) -> context -> info -> A
- check_ctors_by_arg : (term -> info -> A) -> list context -> info -> A
- debug_check_args_by_arg {A} : global_env -> (term -> info -> A) -> context -> info -> list A
- debug_check_ctors_by_arg {A} : global_env -> (term -> info -> A) -> list context -> info -> list (list A)
- get_args : mutual_inductive_body -> list context
*)

Definition get_indices : kername -> nat -> info -> context :=
  fun kname pos_indb e => weaken_context e (get_indb kname pos_indb e).(ind_indices).

Definition get_ctor_indices : kername -> nat -> nat -> info -> list term :=
  fun kname pos_indb pos_ctor e => map (e ↑) (get_ctor kname pos_indb pos_ctor e).(cstr_indices).


(* 1. & 2. Keep and Add Binders *)
Definition kp_tLetIn : aname -> term -> term -> option ident -> info -> (info -> term) -> term :=
  fun an db t1 x e t2 =>
    let db' := e ↑ db in
    let t1' := e ↑ t1 in
    let e := add_old_var None (mkdecl an (Some db) t1) e in
    tLetIn an db' t1' (t2 e).

Definition mk_tLetIn : aname -> term -> term -> option ident -> info -> (info -> term) -> term :=
  fun an db t1 x e t2 =>
    let e := add_fresh_var x (mkdecl an (Some db) t1) e in
    tLetIn an db t1 (t2 e).

Section Binder.

  Context (binder : aname -> term -> term -> term).

  Definition kp_binder : aname -> term -> option ident -> info -> (info -> term) -> term :=
    fun an t1 x e t2 =>
      let t1' := e ↑ t1 in
      let e  := add_old_var x (mkdecl an None t1) e in
      binder an t1' (t2 e).

  Definition it_kp_binder : context -> option ident -> info -> (info -> term) -> term :=
  fun cxt x =>
    fold_left_ie
    (fun _ cdecl e t =>
      let '(mkdecl an db ty) := cdecl in
      match db with
      | None => kp_binder an ty x e t
      | Some db => kp_tLetIn an db ty None e t
      end)
    cxt.

  (* new functions *)
  Definition closure_uparams : kername -> info -> (info -> term) -> term :=
    fun kname e t => it_kp_binder (get_uparams kname e) (Some "uparams") e t.

  Definition closure_nuparams : kername -> info -> (info -> term) -> term :=
    fun kname e t => it_kp_binder (get_nuparams kname e) (Some "nuparams") e t.

  Definition closure_params : kername -> info -> (info -> term) -> term :=
  fun kname e t => it_kp_binder (get_params kname e) (Some "params") e t.


  Definition mk_binder : aname -> term -> option ident -> info -> (info -> term) -> term :=
    fun an t1 x e t2 =>
      let e := add_fresh_var x (mkdecl an None t1) e in
      binder an t1 (t2 e).

  Definition it_mk_binder : context -> option ident -> info -> (info -> term) -> term :=
    fun cxt x =>
    fold_left_ie
    (fun _ cdecl e t =>
      let '(mkdecl an db ty) := cdecl in
      match db with
      | None => mk_binder an ty x e t
      | Some db => mk_tLetIn an db ty None e t
      end)
    cxt.

  Definition closure_binder {A} (s : ident) (l : list A)
    (naming : nat -> A -> aname) (typing : nat -> A -> info -> term) :
    info -> (info -> term) -> term :=
    fold_right_ie
      (fun n a e t => mk_binder (naming n a) (typing n a e) (Some s) e t)
      l.

  Definition closure_indices : kername -> nat -> info -> (info -> term) -> term :=
    fun kname pos_indb e t => it_mk_binder (get_indices kname pos_indb e) (Some "indices") e t.

End Binder.

Definition kp_tProd := kp_binder tProd.
Definition kp_tLambda := kp_binder tLambda.

Definition it_kp_tProd := it_kp_binder tProd.
Definition it_kp_tLambda := it_kp_binder tLambda.

Definition mk_tProd := mk_binder tProd.
Definition mk_tLambda := mk_binder tLambda.

Definition it_mk_tProd := it_mk_binder tProd.
Definition it_mk_tLambda := it_mk_binder tLambda.


Definition make_ind' : kername -> nat -> list term -> info -> term :=
  fun kname pos_indb indices e =>
  mkApps (tInd (mkInd kname pos_indb) [])
          (  get_term "uparams"  e
          ++ get_term "nuparams" e
          ++ indices).

Section MkBranch.
Context (pos_indb : nat).
Context (indb : one_inductive_body).

  Definition relev_ind_sort := indb.(ind_relevance).
  Definition indices := indb.(ind_indices).

  Section mk_tFix.
    Context (ind_bodies : list one_inductive_body).
    Context (fan   : nat -> one_inductive_body -> info -> aname).
    Context (fty   : nat -> one_inductive_body -> info -> term).
    Context (frarg : nat -> one_inductive_body -> info -> nat).

    Definition mk_tFix : nat -> option ident -> info -> (nat -> one_inductive_body -> info -> term) -> term :=
      fun focus x e tmc =>
      let cxt := rev (mapi (fun pos_indb indb => mkdecl (fan pos_indb indb e) None (fty pos_indb indb e)) ind_bodies) in
      let e_Fix := add_fresh_context x cxt e in
      tFix (mapi (fun pos_indb indb => mkdef _ (fan pos_indb indb e) (fty pos_indb indb e)
                      (tmc pos_indb indb e_Fix) (frarg pos_indb indb e)) ind_bodies) focus.

  End mk_tFix.

  Section mk_tCase.
    Context (mk_case_info : nat -> one_inductive_body -> info -> case_info).
    Context (mk_case_pred : nat -> one_inductive_body -> info -> term).

    Definition mk_tCase : kername -> term -> info -> (nat -> constructor_body -> info -> branch term) -> term :=
      fun kname tm_match e branch =>
      let e_Pred := add_fresh_context (Some "fresh_indices") (weaken_context e indb.(ind_indices)) e in
      let ind_decl := (mkdecl (mkBindAnn nAnon indb.(ind_relevance)) None
                            (make_ind' kname pos_indb (get_term "fresh_indices" e_Pred) e_Pred)) in
      let e_Pred := add_fresh_var (Some "fresh_VarMatch") ind_decl e_Pred in
      let pred := mk_predicate [] ((get_term "uparams" e ++ get_term "nuparams" e))
                                  (get_aname "fresh_VarMatch" e_Pred ++ get_aname "fresh_indices" e_Pred)
                                  (mk_case_pred pos_indb indb e_Pred) in
      tCase (mk_case_info pos_indb indb e) pred tm_match
      (mapi (fun pos_ctor ctor => branch pos_ctor ctor e) indb.(ind_ctors)).

  End mk_tCase.

End MkBranch.





(* 3. Inductive Types *)
Section ReplaceInd.

  Context (kname : kername).
  Context (mdecl : mutual_inductive_body).

Definition ind_to_cxt : context :=
  map (fun indb => mkdecl (mkBindAnn nAnon indb.(ind_relevance)) None indb.(ind_type))
  (rev mdecl.(ind_bodies)).

Definition ind_to_terms : list term :=
  mapi (fun i _ => (tInd (mkInd kname i) [])) mdecl.(ind_bodies).

Definition kname_to_ident : ident -> kername -> ident :=
  fun x kname => String.append x (String.append "_" (snd kname)).

Definition kname_to_opt : ident -> kername -> option ident :=
  fun x kname => Some (kname_to_ident x kname).

Definition replace_ind : info -> info :=
  add_replace_context (kname_to_opt "Ind" kname) ind_to_cxt ind_to_terms.

(* Builds: Ind A1 ... An B0 ... Bm i1 ... il *)
Definition make_ind : nat -> info -> term :=
  fun pos_indb e =>
  mkApps (tInd (mkInd kname pos_indb) [])
          (  get_term "uparams"  e
          ++ get_term "nuparams" e
          ++ get_term "indices"  e).

(* Builds: Cst A1 ... An B0 ... Bm *)
Definition make_cst : nat -> nat -> info -> term :=
  fun pos_indb pos_ctor e =>
  mkApps (tConstruct (mkInd kname pos_indb) pos_ctor [])
          (get_term "uparams" e ++ get_term "nuparams" e).

End ReplaceInd.


(* 4. Reduction *)
From MetaCoq Require Import Template.Checker.
Import RedFlags.

Definition noiota_flags := mk true true false true true true.

Definition reduce_except_lets :  global_env -> info -> term -> term :=
  fun E e t =>
  match reduce_opt noiota_flags empty_global_env (get_typing_context e) 5000 t with
  | Some t => t
  | None => tVar "ERREUR REDUCTION"
  end.

Definition reduce_lets : info -> term -> term :=
  fun e t => expand_lets (get_typing_context e) t.

Definition reduce_full : global_env -> info -> term -> term :=
  fun E e t =>
  match reduce_opt default E (get_typing_context e) 5000 t with
  | Some t => t
  | None => tVar "ERREUR REDUCTION"
  end.



(* ########################################################################## *)
(* ########################################################################## *)
(* ########################################################################## *)

(*
#############################
###    Decide interface   ###
#############################

*)

Section CheckArg.

  Context {A : Type}.
  Context (bop : A -> A -> A).
  Context (default : A).
  Context (E : global_env).
  Context (kname : kername).

Definition check_args_by_arg : (term -> info -> A) -> context -> info -> A :=
  fun check_arg args e =>
  fold_left_ie
    ( fun i arg e t =>
        let rty := reduce_full E e (e ↑ arg.(decl_type)) in
        let e' := add_old_var (Some "args") arg e in
        match arg.(decl_body) with
        | None => bop (check_arg rty e) (t e')
        | Some _ => t e'
        end
  )
  args e (fun _ => default).

Definition check_ctors_by_arg : (term -> info -> A) -> list context -> info -> A :=
  fun check_arg lcxt e =>
  fold_left bop (map (fun cxt => check_args_by_arg check_arg cxt e) lcxt) default.

End CheckArg.

Definition debug_check_args_by_arg {A} : global_env -> (term -> info -> A) -> context -> info -> list A :=
  fun E check_arg cxt e =>
  check_args_by_arg (@app A) [] E (fun x e => [check_arg x e]) cxt e.

Definition debug_check_ctors_by_arg {A} : global_env -> (term -> info -> A) -> list context -> info -> list (list A) :=
  fun E check_arg lcxt e => map (fun cxt => debug_check_args_by_arg E check_arg cxt e) lcxt.

Definition get_args : mutual_inductive_body -> list context :=
  fun mdecl => map cstr_args (concat (map ind_ctors mdecl.(ind_bodies))).