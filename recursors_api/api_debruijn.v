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

Definition rmapi {A B} : (nat -> A -> B) -> list A -> list B :=
  fun f l => fold_left_i (fun i t a => f i a :: t) l [].

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


(* 0. General Purposed  *)
- fold_right_ie : {A} (nat -> A -> info -> (info -> term) -> term)
    (list A) -> info -> (info -> term) -> term
- fold_left_ie : {A} (nat -> A -> info -> (info -> term) -> term)
    (list A) -> info -> (info -> term) -> term

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


(* 2. Check var *)
Definition isVar_ident : ident -> nat -> info -> bool
Definition isVar_pos : ident -> nat -> nat -> info -> bool


(* 3. Weakening *)
- weaken : info -> term -> term

(* 4. Add variables *)
- init_info : info
- add_fresh_var : option ident -> context_decl -> info -> info
- add_old_var : option ident -> context_decl -> info -> info
- add_replace_var : option ident -> term -> info -> info

*)


(* Data Structure *)
Record info_decl : Type := mk_idecl
  { info_name    : option ident ;
    info_old     : bool ;
    info_replace : bool ;
    info_def     : context_decl ;
}.

Definition info : Type := list info_decl.

Definition init_info : info := [].

Definition error_scope_idecl : info_decl :=
  mk_idecl (Some "ERROR SCOPE") false false
    (mkdecl (mkBindAnn (nNamed "ERROR") Relevant) (Some error_scope_term) error_scope_term).


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


(* 1. Get terms and types *)

(* 1.1 Get terms selectively *)
Definition get_term_idecl : nat -> info_decl -> term :=
  fun pos_idecl idecl =>
  match idecl.(info_def).(decl_body) with
  | Some tm => if idecl.(info_replace) then lift0 (S pos_idecl) tm else tRel pos_idecl
  | None => tRel pos_idecl
  end.

Definition get_type_idecl : nat -> info_decl -> term :=
  fun pos_idecl idecl => lift0 (S pos_idecl) idecl.(info_def).(decl_type).

Definition get_info : (nat -> info_decl -> term) -> (info_decl -> bool) ->  info -> list term :=
  fun f p e => fold_right_i (fun i idecl next => if p idecl then f i idecl :: next else next) [] e.

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

Definition get_typing_context : info -> context :=
  fun e => map info_def e.



(* 2. Check var *)
Definition get_ident : nat -> info -> option ident :=
fun n e => (nth n e error_scope_idecl).(info_name).

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
  fun x decl e => mk_idecl x true false (weaken_decl e decl) :: e.

Definition add_old_context : option ident -> context -> info -> info :=
  fun x cxt e => fold_right (fun cdecl e => add_old_var x cdecl e) e cxt.

Definition add_fresh_var : option ident -> context_decl -> info -> info :=
  fun x decl e => mk_idecl x false false decl :: e.

Definition add_fresh_context : option ident -> context -> info -> info :=
  fun x cxt e => fold_right(fun cdecl e => add_fresh_var x cdecl e) e cxt.

Definition add_replace_var : option ident -> context_decl -> term -> info -> info :=
  fun x cxt tm e => let ' mkdecl an _ ty := weaken_decl e cxt in
                  mk_idecl x true true (mkdecl an (Some tm) ty) :: e.

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


(* 5. Notations *)
Notation "e ↑" := (weaken e) (at level 10).

Notation " x '<-' c1 ';;' c2" := ( c1 (fun x => c2))
  (at level 100, c1 at next level, right associativity).





(* ########################################################################## *)
(* ########################################################################## *)
(* ########################################################################## *)

(*
#############################
###  Frontend interface   ###
#############################


(* 1. Keep Binders *)
- kp_tLetIn  : aname -> term -> term -> option ident -> info -> (info -> term) -> term
- kp_binder  : (aname -> term -> term -> term) -> aname -> term ->
                option ident -> info -> (info -> term) -> term
- kp_tProd   : aname -> term -> option ident -> info -> (info -> term) -> term
- kp_tLambda : aname -> term -> option ident -> info -> (info -> term) -> term
- Iterate version that deals with LetIn
- closure_params, closure_uparams, closure_nuparams, closure_indices

(* 2. Add Binders *)
- mk_tLetIn  : aname -> term -> term -> option ident -> info -> (info -> term) -> term
- mk_binder  : (aname -> term -> term -> term) -> aname -> term ->
                option ident -> info -> (info -> term) -> term
- mk_tProd   : aname -> term -> option ident -> info -> (info -> term) -> term
- mk_tLambda : aname -> term -> option ident -> info -> (info -> term) -> term
- Iterate version that deals with LetIn
-  closure_binder {A} (s : ident) (l : list A) (naming : nat -> A -> aname)
    (typing : nat -> A -> info -> term) : info -> (info -> term) -> term :=

(* 3. Inductive Types *)
- replace_ind : kername -> mutual_inductive_body -> info -> info

(* 4. Reduction *)
- reduce_except_lets : info -> term -> term
- reduce_full : info -> term -> term
*)






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

  Definition closure_params   := fun cxt => it_kp_binder cxt (Some "params").
  Definition closure_uparams  := fun cxt => it_kp_binder cxt (Some "uparams").
  Definition closure_nuparams := fun cxt => it_kp_binder cxt (Some "nuparams").
  Definition closure_indices  := fun cxt => it_kp_binder cxt (Some "indices").


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

End Binder.

Definition kp_tProd := kp_binder tProd.
Definition kp_tLambda := kp_binder tLambda.

Definition it_kp_tProd := it_kp_binder tProd.
Definition it_kp_tLambda := it_kp_binder tLambda.

Definition mk_tProd := mk_binder tProd.
Definition mk_tLambda := mk_binder tLambda.

Definition it_mk_tProd := it_mk_binder tProd.
Definition it_mk_tLambda := it_mk_binder tLambda.



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


Definition split_params : nat -> mutual_inductive_body -> context * context  :=
  fun nb_uparams mdecl =>
  let rev_params := rev mdecl.(ind_params) in
  (rev (firstn nb_uparams rev_params), rev (skipn nb_uparams rev_params)).

(* Builds: Ind A1 ... An B0 ... Bm i1 ... il *)
Definition make_ind : nat -> info -> term :=
  fun pos_block e =>
  mkApps (tInd (mkInd kname pos_block) [])
          (  get_term "uparams"  e
          ++ get_term "nuparams" e
          ++ get_term "indices"  e).

(* Builds: Cst A1 ... An B0 ... Bm *)
Definition make_cst : nat -> nat -> info -> term :=
  fun pos_block pos_ctor e =>
  mkApps (tConstruct (mkInd kname pos_block) pos_ctor [])
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

Definition check_args_by_arg : (kername -> term -> info -> A) -> context -> info -> A :=
  fun check_arg args e =>
  fold_left_ie
    ( fun i arg e t =>
        let rty := reduce_full E e (e ↑ arg.(decl_type)) in
        let e' := add_old_var (Some "args") arg e in
        match arg.(decl_body) with
        | None => bop (check_arg kname rty e) (t e')
        | Some _ => t e'
        end
  )
  args e (fun _ => default).

Definition check_ctors_by_arg : (kername -> term -> info -> A) -> list context -> info -> A :=
  fun check_arg lcxt e =>
  fold_left bop (map (fun cxt => check_args_by_arg check_arg cxt e) lcxt) default.

End CheckArg.

Definition debug_check_args_by_arg {A} : global_env -> kername -> (kername -> term -> info -> A) -> context -> info -> list A :=
  fun E kname check_arg cxt e =>
  check_args_by_arg (@app A) [] E kname (fun kname x e => [check_arg kname x e]) cxt e.

Definition debug_check_ctors_by_arg {A} : global_env -> kername -> (kername -> term -> info -> A) -> list context -> info -> list (list A) :=
  fun E kname check_arg lcxt e => map (fun cxt => debug_check_args_by_arg E kname check_arg cxt e) lcxt.

Definition get_args : mutual_inductive_body -> list context :=
  fun mdecl => map cstr_args (concat (map ind_ctors mdecl.(ind_bodies))).