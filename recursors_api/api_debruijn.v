From Coq Require Export List.
Export ListNotations.

From MetaCoq.Utils Require Export utils.
From MetaCoq.Template Require Export All.


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

(* 1. Access Var *)
- get  : ident -> info -> list term
- geti : ident -> nat -> info -> term

(* 2. Add variables *)
- init_info : info
- add_fresh_var : option ident -> context_decl -> info -> info
- add_old_var : option ident -> context_decl -> info -> info
- add_replace_var : option ident -> term -> info -> info
- isVar : ident -> nat -> info -> bool

(* 3. Weakening *)
- weaken : info -> term -> term

*)




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



(* Data Structure *)
Record info_decl : Type := mk_idecl
  { info_name : option ident ;
    info_old : bool ;
    info_new : (term * term) + context_decl ;
}.

Definition info : Type := list info_decl.

(* 0. Get terms and types *)
Definition get_term_idecl : nat -> info_decl -> term :=
  fun pos_idecl idecl =>
  match idecl.(info_new) with
  | inl (tm, _) => lift0 (S pos_idecl) tm
  | inr _ => tRel pos_idecl
  end.

Definition get_type_idecl : nat -> info_decl -> term :=
  fun pos_idecl idecl =>
  match idecl.(info_new) with
  | inl (_, ty) => lift0 (S pos_idecl) ty
  | inr (mkdecl _ _ ty) => lift0 (S pos_idecl) ty
  end.

Definition get_info : (nat -> info_decl -> term) -> (info_decl -> bool) ->  info -> list term :=
  fun f p e => fold_right_i (fun i idecl next => if p idecl then f i idecl :: next else next) [] e.

Definition get_term_info : (info_decl -> bool) ->  info -> list term :=
  get_info get_term_idecl.

Definition get_type_info : (info_decl -> bool) ->  info -> list term :=
  get_info get_type_idecl.


(* 1. Access terms and types *)
Definition filter_name : ident -> info_decl -> bool :=
  fun i idecl => eq_option eqb idecl.(info_name) (Some i).

Definition get_term : ident -> info -> list term :=
  fun i e => rev (get_term_info (filter_name i) e).

Definition geti_term : ident -> nat -> info -> term :=
  fun i n e => nth n (get_term i e) error_scope_term.

Definition get_term_rev : ident -> info -> list term :=
  fun i e => get_term_info (filter_name i) e.

Definition geti_term_rev : ident -> nat -> info -> term :=
  fun i n e => nth n (get_term_rev i e) error_scope_term.

Definition get_type : ident -> info -> list term :=
  fun i e => rev (get_type_info (filter_name i) e).

Definition geti_type : ident -> nat -> info -> term :=
  fun i n e => nth n (get_type i e) error_scope_term.

Definition get_type_rev : ident -> info -> list term :=
  fun i e => get_type_info (filter_name i) e.

Definition geti_type_rev : ident -> nat -> info -> term :=
  fun i n e => nth n (get_type_rev i e) error_scope_term.

Fixpoint get_typing_context (e : info) : context :=
  match e with
  | [] => []
  | (mk_idecl _ _ (inr cdecl)) :: l => cdecl :: get_typing_context l
  | _ :: l => get_typing_context l
  end.


(* 2. Add variables *)
Definition init_info : info := [].

Definition error_scope_idecl : info_decl :=
  mk_idecl (Some "ERROR SCOPE") false (inl (error_scope_term, error_scope_term)).

Definition add_old_var : option ident -> context_decl -> info -> info :=
  fun x decl e => mk_idecl x true (inr decl) :: e.

Definition add_fresh_var : option ident -> context_decl -> info -> info :=
  fun x decl e => mk_idecl x false (inr decl) :: e.

Definition add_replace_var : option ident -> term -> term -> info -> info :=
  fun x tm ty e => mk_idecl x true (inl (tm, ty)) :: e.

Definition isVar : ident -> nat -> info -> bool :=
  fun i n e => eqb (nth n e error_scope_idecl).(info_name) (Some i).


(* 3. Weakening and Lets *)
Definition get_subst : info -> list term :=
  get_term_info info_old.

Definition weaken : info -> term -> term :=
  fun e => subst0 (get_subst e).


(* 4. Notations *)
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


(* 1. General Purposed  *)
- fold_right_ie : {A} (nat -> A -> info -> (info -> term) -> term)
    (list A) -> info -> (info -> term) -> term
- fold_left_ie : {A} (nat -> A -> info -> (info -> term) -> term)
    (list A) -> info -> (info -> term) -> term

(* 2. Keep Binders *)
- kp_binder  : (aname -> term -> term -> term) -> aname -> term ->
                option ident -> info -> (info -> term) -> term
- kp_tProd   : aname -> term -> option ident -> info -> (info -> term) -> term
- kp_tLambda : aname -> term -> option ident -> info -> (info -> term) -> term
- kp_tLetIn  : aname -> term -> term -> option ident -> info -> (info -> term) -> term

=> Iterate version that deals with LetIn

(* 3. Add Binders *)
- mk_binder  : (aname -> term -> term -> term) -> aname -> term ->
                option ident -> info -> (info -> term) -> term
- mk_tProd   : aname -> term -> option ident -> info -> (info -> term) -> term
- mk_tLambda : aname -> term -> option ident -> info -> (info -> term) -> term
- mk_tLetIn  : aname -> term -> term -> option ident -> info -> (info -> term) -> term

(* 4. Inductive Types *)
- replace_ind : kername -> mutual_inductive_body -> info -> info

(* 5. Reduction *)
- reduce_except_lets : info -> term -> term
- reduce_full : info -> term -> term
*)


(* 1. General Purposed  *)
Definition fold_right_ie {A} (tp : nat -> A -> info -> (info -> term) -> term)
  (l:list A) (e:info) (t : info -> term) : term :=
  let fix aux l e n t : term :=
    match l with
    | [] => t e
    | a :: l => tp n a e (fun e => aux l e (S n) t)
  end in
  aux l e 0 t.

Definition fold_left_ie {A} (tp : nat -> A -> info -> (info -> term) -> term)
  (l:list A) (e:info) (t : info -> term) : term :=
  let fix aux l e n t : term :=
    match l with
    | [] => t e
    | a :: l => aux l e (S n) (fun e => tp n a e t)
  end in
  aux l e 0 t.



(* 2. & 3. Keep and Add Binders *)

Definition kp_tLetIn : aname -> term -> term -> option ident -> info -> (info -> term) -> term :=
  fun an db t1 x e t2 =>
    let db := e ↑ db in
    let t1 := e ↑ t1 in
    let e := add_old_var None (mkdecl an (Some db) t1) e in
    tLetIn an db t1 (t2 e).

Definition mk_tLetIn : aname -> term -> term -> option ident -> info -> (info -> term) -> term :=
  fun an db t1 x e t2 =>
    let e := add_fresh_var x (mkdecl an (Some db) t1) e in
    tLetIn an db t1 (t2 e).

Section Binder.

  Context (binder : aname -> term -> term -> term).

  Definition kp_binder : aname -> term -> option ident -> info -> (info -> term) -> term :=
    fun an t1 x e t2 =>
      let t1 := e ↑ t1 in
      let e  := add_old_var x (mkdecl an None t1) e in
      binder an t1 (t2 e).

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

End Binder.

Definition kp_tProd := kp_binder tProd.
Definition kp_tLambda := kp_binder tLambda.

Definition it_kp_tProd := it_kp_binder tProd.
Definition it_kp_tLambda := it_kp_binder tLambda.

Definition mk_tProd := mk_binder tProd.
Definition mk_tLambda := mk_binder tLambda.

Definition it_mk_tProd := it_mk_binder tProd.
Definition it_mk_tLambda := it_mk_binder tLambda.



(* 4. Inductive Types *)
Definition replace_ind : kername -> mutual_inductive_body -> info -> info :=
  fun kname mdecl e =>
  let nb_block := length mdecl.(ind_bodies) in
  fold_left_i (fun i e indb => add_replace_var (Some "Inds")
                  (tInd (mkInd kname i) []) indb.(ind_type) e)
  mdecl.(ind_bodies) e.

(* 5. Reduction *)
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