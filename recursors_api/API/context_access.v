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

2. Access the context by the position
-----------------------------------------------------------------
getp_name  : nat -> state -> ident
getp_aname : nat -> state -> aname
getp_body  : nat -> state -> option term
getp_type  : nat -> state -> term
check_id   : nat -> ident -> state -> bool
check_ids  : nat -> list ident -> state -> bool

3. Others
-----------------------------------------------------------------
- get_typing_context : state -> context
- reduce_lets : state -> term -> term
- reduce_except_lets :  global_env -> state -> term -> term
- reduce_full : global_env -> state -> term -> term

*)

#[local] Definition ERROR_GET_SDECL : ident -> state -> state_decl :=
  fun id s => let ERR_MSG := "ERROR_GET_SDECL:" ^ id in
              mk_sdecl ERR_MSG
              (mkdecl (mkBindAnn (nNamed ERR_MSG) Relevant)
              (Some (state_to_term s)) (state_to_term s)).

(* 1.0 Local functions geting term and type with shifted *)
#[local] Definition get_sdecl : ident -> state -> (nat * state_decl) :=
  fun id s =>
  let fix aux n s' :=
  match s' with
  | [] => (0, ERROR_GET_SDECL id s)
  | sdecl :: s' => if eqb id sdecl.(state_name) then (n, sdecl) else aux (S n) s'
  end in
  aux 0 s.(state_context).

Section Get.

  Context {X : Type}.
  Context (f : nat -> state_decl -> X).

  Definition concat_strings : list string -> string :=
    fun l => fold_right (fun s t => s ^ " " ^ t) "" l.

  #[local] Definition get_id1: list ident -> nat -> ident :=
    fun ids pos1 => nth pos1 ids ("ERROR GET_ID1: " ^ (concat_strings ids)).

  #[local] Definition get_id2 : list (list ident) -> nat -> nat -> ident :=
  fun idss pos1 pos2 =>
  let ids := nth pos1 idss ["ERROR GET_ID2: nth pos1"] in
  nth pos2 ids "ERROR GET_ID2: nth pos2".

  #[local] Definition get_X : ident -> state -> X :=
    fun id s => let ' (pos_var, sdecl) := get_sdecl id s in f pos_var sdecl.

  #[local] Definition geti_X : list ident -> nat -> state -> X :=
      fun ids pos_id s => get_X (get_id1 ids pos_id) s.

  #[local] Definition getij_X : list (list ident) -> nat -> nat -> state -> X :=
  fun ids pos_id1 pos_id2 s => get_X (get_id2 ids pos_id1 pos_id2) s.

  #[local] Definition get_Xs : list ident -> state -> list X :=
  fun l s => map (fun x => get_X x s) l.

End Get.

(* 1.1 Get terms *)
#[local] Definition get_sdecl_term : nat -> state_decl -> term :=
  fun shift ' (mk_sdecl _ (mkdecl _ bd _)) =>
  match bd with
  | Some tm => lift0 (S shift) tm
  | None => tRel shift
  end.

Definition get_term := get_X get_sdecl_term.
Definition geti_term := geti_X get_sdecl_term.
Definition getij_term := getij_X get_sdecl_term.
Definition get_terms := get_Xs get_sdecl_term.

(* 1.2 Get types *)
#[local] Definition get_sdecl_type : nat -> state_decl -> term :=
  fun shift ' (mk_sdecl _ (mkdecl _ _ ty)) => lift0 (S shift) ty.

Definition get_type   := get_X   get_sdecl_type.
Definition geti_type  := geti_X  get_sdecl_type.
Definition getij_type := getij_X get_sdecl_type.
Definition get_types  := get_Xs  get_sdecl_type.

(* 1.3 Get aname *)
#[local] Definition get_sdecl_aname : nat -> state_decl -> aname :=
  fun _ sdecl => sdecl.(state_def).(decl_name).

Definition get_aname   := get_X   get_sdecl_aname.
Definition geti_aname  := geti_X  get_sdecl_aname.
Definition getij_aname := getij_X get_sdecl_aname.
Definition get_anames  := get_Xs  get_sdecl_aname.

(* 1.4 Check *)
Definition check_pos: ident -> nat -> state -> bool :=
  fun id read_pos s => let ' (pos_cxt, _) := get_sdecl id s in eqb pos_cxt read_pos.



(* 2. Access by position *)
#[local] Definition ERROR_GETP_SDECL : nat -> state -> state_decl :=
  fun pos s => mk_sdecl "ERROR GET SDECL"
              (mkdecl (mkBindAnn (nNamed ("ERROR_GET_SDECL: " ^ string_of_nat pos)) Relevant)
              (Some (tVar "ERROR GET SDECL")) (tVar "ERROR GET SDECL")).

#[local] Definition getp_sdecl : nat -> state -> state_decl :=
  fun pos s => nth pos s.(state_context) (ERROR_GETP_SDECL pos s).

Definition getp_name : nat -> state -> ident :=
  fun pos s => (getp_sdecl pos s).(state_name).

Definition getp_aname : nat -> state -> aname :=
  fun pos s => (getp_sdecl pos s).(state_def).(decl_name).

Definition getp_body : nat -> state -> option term :=
  fun pos s => (getp_sdecl pos s).(state_def).(decl_body).

Definition getp_type : nat -> state -> term :=
  fun pos s => (getp_sdecl pos s).(state_def).(decl_type).

Definition check_id : nat -> ident -> state -> bool :=
  fun pos id s => eqb (state_name (getp_sdecl pos s)) id.

Definition check_ids : nat -> list ident -> state -> bool :=
  fun pos ids s => fold_right (fun id t => (check_id pos id s) || t) false ids.



(* 3. Others *)
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