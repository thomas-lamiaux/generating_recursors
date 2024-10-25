From RecAPI Require Import core.
From RecAPI Require Import debug_functions.

(* Get and check functions for the context

1. Access the context by ident
-----------------------------------------------------------------
- get_term   : ident -> state -> term
- geti_term  : list ident -> nat -> state -> term
- getij_term : list (list ident) -> nat -> nat -> state -> term
- get_terms  : list ident -> state -> list term
-----------------------------------------------------------------
- get_type   : ident -> state -> term
- geti_type  : list ident -> nat -> state -> term
- getij_type : list (list ident) -> nat -> nat -> state -> term
- get_types  : list ident -> state -> list term
-----------------------------------------------------------------
- get_aname   : ident -> state -> aname
- geti_aname  : list ident -> nat -> state -> aname
- getij_aname : list (list ident) -> nat -> nat -> state -> aname
- get_anames  : list ident -> state -> list aname
-----------------------------------------------------------------
- check_pos : ident -> nat -> state -> bool

2. Others
-----------------------------------------------------------------
- get_typing_context : state -> context
- reduce_lets : state -> term -> term
- reduce_except_lets :  global_env -> state -> term -> term
- reduce_full : global_env -> state -> term -> term

*)

Definition ERROR_SCOPE : ident -> state -> state_decl :=
  fun id s => mk_idecl "ERROR"
              (mkdecl (mkBindAnn (nNamed ("ERROR SCOPE " ^ id)) Relevant) (Some (state_to_term s)) (state_to_term s)).

(* 1.0 Local functions geting term and type with shifted *)
#[local] Definition get_idecl : ident -> state -> (nat * state_decl) :=
  fun id s =>
  let fix aux n s' :=
  match s' with
  | [] => (404, ERROR_SCOPE id s)
  | idecl :: s' => if eqb id idecl.(state_name) then (n, idecl) else aux (S n) s'
  end in
  aux 0 s.(state_context).

Section Get.

  Context {X : Type}.
  Context (f : nat -> state_decl -> X).

  #[local] Definition get_id1: list ident -> nat -> ident :=
    fun ids pos1 => nth pos1 ids (failwith "error get one of them").

  #[local] Definition get_id2 : list (list ident) -> nat -> nat -> ident :=
  fun idss pos1 pos2 =>
  nth pos2 (nth pos1 idss (failwith "error get2 pos1")) (failwith "error get2 pos2").

  #[local] Definition get_X : ident -> state -> X :=
    fun id s => let ' (pos_var, idecl) := get_idecl id s in f pos_var idecl.

  #[local] Definition geti_X : list ident -> nat -> state -> X :=
      fun ids pos_id s => get_X (get_id1 ids pos_id) s.

  #[local] Definition getij_X : list (list ident) -> nat -> nat -> state -> X :=
  fun ids pos_id1 pos_id2 s => get_X (get_id2 ids pos_id1 pos_id2) s.

  #[local] Definition get_Xs : list ident -> state -> list X :=
  fun l s => map (fun x => get_X x s) l.

End Get.

(* 1.1 Get terms *)
#[local] Definition get_idecl_term : nat -> state_decl -> term :=
  fun shift ' (mk_idecl _ (mkdecl _ bd _)) =>
  match bd with
  | Some tm => lift0 (S shift) tm
  | None => tRel shift
  end.

Definition get_term := get_X get_idecl_term.
Definition geti_term := geti_X get_idecl_term.
Definition getij_term := getij_X get_idecl_term.
Definition get_terms := get_Xs get_idecl_term.

(* 1.2 Get types *)
#[local] Definition get_idecl_type : nat -> state_decl -> term :=
  fun shift ' (mk_idecl _ (mkdecl _ _ ty)) => lift0 (S shift) ty.

Definition get_type   := get_X   get_idecl_type.
Definition geti_type  := geti_X  get_idecl_type.
Definition getij_type := getij_X get_idecl_type.
Definition get_types  := get_Xs  get_idecl_type.

(* 1.3 Get aname *)
#[local] Definition get_idecl_aname : nat -> state_decl -> aname :=
  fun _ sdecl => sdecl.(state_def).(decl_name).

Definition get_aname   := get_X   get_idecl_aname.
Definition geti_aname  := geti_X  get_idecl_aname.
Definition getij_aname := getij_X get_idecl_aname.
Definition get_anames  := get_Xs  get_idecl_aname.

(* 1.4 Check *)
Definition check_pos: ident -> nat -> state -> bool :=
  fun id read_pos s => let ' (pos_cxt, _) := get_idecl id s in eqb pos_cxt read_pos.



(* 2. Others *)
Definition get_typing_context : state -> context :=
  fun s => map state_def s.(state_context).

From MetaCoq Require Import Template.Checker.
Import RedFlags.

#[local] Definition noiota_flags := mk true true false true true true.

Definition reduce_lets : state -> term -> term :=
  fun s t => expand_lets (get_typing_context s) t.

Definition reduce_except_lets :  global_env -> state -> term -> term :=
  fun E s t =>
  match reduce_opt noiota_flags empty_global_env (get_typing_context s) 5000 t with
  | Some t => t
  | None => tVar "ERREUR REDUCTION"
  end.

Definition reduce_full : global_env -> state -> term -> term :=
  fun E s t =>
  match reduce_opt default E (get_typing_context s) 5000 t with
  | Some t => t
  | None => tVar "ERREUR REDUCTION"
  end.