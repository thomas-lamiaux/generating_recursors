
(* Plan:
--------------------------------
1. core
2. fold_functions
--------------------------------
3. Access the inductive type
4. Add inductive types to states
--------------------------------
5. Acces the context
6. Add terms to states
--------------------------------
7. interface to create terms
8. interface to decide properties

*)



(* 1. Core  *)
From RecAPI Require Export core.
(*
- state : Type
- init_state : state
- add_pdecl : state_pdecl -> state -> state
- weaken : state -> term -> term
- weaken_decl : state -> context_decl -> context_decl
- weaken_context : state -> context -> context
- state_to_terms : state -> term
*)



(* 2. General Purposed Fold Functions *)
From RecAPI Require Export fold_functions.
(*
- fold_right_state : {A B X state} : (nat -> A -> state -> (X -> state -> B) -> B)
  -> list A -> state -> (list X -> state -> B) -> B
- fold_left_state : {A B X state} : (nat -> A -> state -> (X -> state -> B) -> B)
  -> list A -> state -> (list X -> state -> B) -> B
- fold_right_state_opt {A B X state} : (tp : nat -> A -> state -> (list X -> state -> B) -> B)
  -> list A -> state -> (list X -> state -> B) : B
- fold_left_state_opt {A B X state} : (tp : nat -> A -> state -> (list X -> state -> B) -> B)
  -> list A -> state -> (list X -> state -> B) : B

=> 2 / 3 / 4 variants
*)



(* 3. Access the inductive type *)
From RecAPI Require Export inductive_access.
(*
- get_pdecl : kername -> state -> state_pdecl
- get_uparams     : kername -> state -> context
- get_nb_uparams  : kername -> state -> nat
- get_nuparams    : kername -> state -> context
- get_nb_nuparams : kername -> state -> nat
- get_params      : kername -> state -> context
- get_nb_params   : kername -> state -> nat
- get_mdecl       : kername -> state -> mutual_inductive_body
- get_ind_bodies  : kername -> state -> list one_inductive_body
- get_all_args     : kername -> state -> list context
- get_indb        : kername -> nat  -> state -> one_inductive_body
- get_relevance   : kername -> nat  -> state -> relevance
- get_ctor        : kername -> nat  -> nat  -> state -> constructor_body
- get_indices      : kername -> nat -> state -> context
- get_ctor_indices : kername -> nat -> nat   -> state -> list term
*)



(* 4. Add inductive types to state *)
From RecAPI Require Export inductive_store.
(*
- add_mdecl : kername -> nat -> mutual_inductive_body -> state -> state
*)



(* 5. Acces the context *)
From RecAPI Require Export context_access.
(*
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



(* 6. Add terms to state *)
From RecAPI Require Export context_store.
(*
- fresh_ident : option ident -> state -> ident
- add_old_var   {X}     : option ident -> context_decl -> state -> (ident -> state -> X) -> X
- add_old_context {X}   : option ident -> context -> state -> (list ident -> state -> X) -> X :=
- add_fresh_var {X}     : option ident -> context_decl -> state -> (ident -> state -> X) -> X
- add_fresh_context {X} : option ident -> context -> state -> (list ident -> state -> X) -> X
- subst_old_var {X}     : term -> state -> (state -> X) -> X
- subst_old_vars {X}    : list term -> state -> (state -> X) -> X
- save_term {X}         : option ident -> context_decl -> state -> (ident ->  state -> X) -> X

- notation: "let* x .. z '<-' c1 'in' c2"
*)



(* 7. Interface to create terms *)
From RecAPI Require Export creating_terms.
(*

  1. Functions for building inductive types
-----------------------------------------------------------------
- replace_ind {X} : kername -> state -> (state -> X) -> X
- make_ind : kername -> nat -> list ident -> list ident -> list ident -> state -> term
- make_cst : kername -> nat -> nat -> list ident -> list ident -> state -> term

  2. Keep and Make Let in
-----------------------------------------------------------------
- kp_tLetIn : aname -> term -> term -> state -> (ident -> state -> term) -> term
- mk_tLetIn : aname -> term -> term -> state -> (ident -> state -> term) -> term

  3. Keep and Make Binary binder(s)
--------------------------------------------------------------------------------
Context (binder : aname -> term -> term -> term)

- kp_binder : aname -> term -> option ident -> state -> (ident -> state -> term) -> term
- it_kp_binder : context -> option ident -> state -> (list ident -> state -> term) -> term
- closure_uparams : kername -> state -> (list ident -> state -> term) -> term
- closure_nuparams : kername -> state -> (list ident -> state -> term) -> term
- closure_params : kername -> state -> (list ident -> state -> term) -> term

- mk_binder : aname -> term -> option ident -> state -> (ident -> state -> term) -> term
- it_mk_binder : context -> option ident -> state -> (list ident -> state -> term) -> term
- closure_indices : kername -> nat -> state -> (list ident -> state -> term) -> term
- closure_binder {A} : option ident -> list A -> (naming : nat -> A -> aname) ->
    (typing : nat -> A -> state -> term) -> state -> (list ident -> state -> term) -> term

- kp_tProd / kp_tLambda / mk_tProd / mk_tLambda

  4. Make Fixpoint
--------------------------------------------------------------------------------
Context (ind_bodies : list one_inductive_body)
        (fan   : nat -> one_inductive_body -> state -> aname
        (fty   : nat -> one_inductive_body -> state -> term
        (frarg : nat -> one_inductive_body -> state -> nat

- mk_tFix : nat -> state -> (list ident -> nat -> one_inductive_body -> state -> term) -> term

  5. Make Match
-----------------------------------------------------------------
Context (kname : kername) (pos_indb : nat) (indb : one_inductive_body)
        (id_uparams id_nuparams : list ident)
        (mk_case_pred : list ident -> ident -> nat -> one_inductive_body -> state -> term).

- mk_tCase : term -> state -> (nat -> constructor_body -> state -> branch term) -> term

*)


(* 8. Interface to decide properties *)
From RecAPI Require Export decide.
(*
Context {A : Type} (bop : A -> A -> A) (default : A)
        (E : global_env) (kname : kername)

- check_args_by_arg : (term -> state -> A) -> context -> state -> A
- check_ctors_by_arg : (term -> state -> A) -> list context -> state -> A
- debug_check_args_by_arg {A} : global_env -> (term -> state -> A) -> context -> state -> list A
- debug_check_ctors_by_arg {A} : global_env -> (term -> state -> A) -> list context -> state -> list (list A)

*)


(*
#############################
###    Info for Nesting   ###
#############################

*)

Record one_env_param : Type := mk_one_env_param
 { ep_kname : kername ;
   ep_nb_uparams : nat ;
   ep_strpos_uparams : list bool ;
   ep_pkname : kername ;
   ep_tkname : kername;
}.

Definition env_param := list one_env_param.

Record output_univ : Type := mk_output_univ
  { out_univ  : term;
    out_relev : relevance
  }.

Definition relev_sort (U : term) : relevance :=
  match U with
  | tSort sSProp => Irrelevant
  | _ => Relevant
  end.
