From RecAPI Require Import core.

(* Access the inductive type
- get_pdecl        : kername -> state -> state_pdecl
- get_uparams      : kername -> state -> context
- get_nb_uparams   : kername -> state -> nat
- get_nuparams     : kername -> state -> context
- get_nb_nuparams  : kername -> state -> nat
- get_params       : kername -> state -> context
- get_nb_params    : kername -> state -> nat
- get_mdecl        : kername -> state -> mutual_inductive_body
- get_ind_bodies   : kername -> state -> list one_inductive_body
- get_all_args     : kername -> state -> list context
- get_indb         : kername -> nat -> state -> one_inductive_body
- get_relevance    : kername -> nat -> state -> relevance
- get_ctor         : kername -> nat -> nat   -> state -> constructor_body
- get_indices      : kername -> nat -> state -> context
- get_ctor_indices : kername -> nat -> nat   -> state -> list term
*)

Definition get_pdecl : kername -> state -> state_pdecl :=
  fun kname s =>
    match find (fun pdecl => eqb pdecl.(state_kname) kname) s.(state_ind) with
    | Some pdecl => pdecl
    | None => failwith "get_pdecl"
    end.

Definition get_uparams : kername -> state -> context :=
  fun kname s => (get_pdecl kname s).(state_uparams).

Definition get_nb_uparams : kername -> state -> nat :=
  fun kname s => (get_pdecl kname s).(state_nb_uparams).

Definition get_nuparams : kername -> state -> context :=
  fun kname s => (get_pdecl kname s).(state_nuparams).

Definition get_nb_nuparams : kername -> state -> nat :=
  fun kname s => (get_pdecl kname s).(state_nb_nuparams).

Definition get_params : kername -> state -> context :=
  fun kname s => (get_pdecl kname s).(state_mdecl).(ind_params).

Definition get_nb_params : kername -> state -> nat :=
  fun kname s => (get_pdecl kname s).(state_mdecl).(ind_npars).

Definition get_mdecl : kername -> state -> mutual_inductive_body :=
  fun kname s => (get_pdecl kname s).(state_mdecl).

Definition get_ind_bodies : kername -> state -> list one_inductive_body :=
  fun kname s => (get_pdecl kname s).(state_mdecl).(ind_bodies).

Definition get_all_args : kername -> state -> list context :=
  fun kname s => map cstr_args (concat (map ind_ctors (get_mdecl kname s).(ind_bodies))).

Definition get_indb : kername -> nat -> state -> one_inductive_body :=
  fun kname pos_indb s => nth pos_indb (get_ind_bodies kname s) (failwith "get_indb").

Definition get_relevance : kername -> nat -> state -> relevance :=
  fun kname pos_indb s => (get_indb kname pos_indb s).(ind_relevance).

Definition get_ctor : kername -> nat -> nat -> state -> constructor_body :=
  fun kname pos_indb pos_ctor s => nth pos_ctor (get_indb kname pos_indb s).(ind_ctors) (failwith "get_ctor").

Definition get_indices : kername -> nat -> state -> context :=
  fun kname pos_indb s => weaken_context s (get_indb kname pos_indb s).(ind_indices).

Definition get_ctor_indices : kername -> nat -> nat -> state -> list term :=
  fun kname pos_indb pos_ctor s => map (weaken s) (get_ctor kname pos_indb pos_ctor s).(cstr_indices).