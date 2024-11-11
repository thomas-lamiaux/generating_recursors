From NamedAPI Require Import core.
From NamedAPI Require Import fold_functions.
From NamedAPI Require Import context_access.
From NamedAPI Require Import context_store.

(* Interface to decide properties
Context {A : Type} (bop : A -> A -> A) (default : A)
Context (E : global_env) (kname : kername)

- check_args_by_arg : (term -> state -> A) -> context -> state -> A
- check_ctors_by_arg : (term -> state -> A) -> list context -> state -> A
- debug_check_args_by_arg {A} : global_env -> (term -> state -> A) -> context -> state -> list A
- debug_check_ctors_by_arg {A} : global_env -> (term -> state -> A) -> list context -> state -> list (list A)
*)

Definition add_inds {X} : mutual_inductive_body -> state -> (state -> keys -> X) -> X :=
  fun mdecl s cc =>
  let cxt := mapi (fun i indb => mkdecl (mkBindAnn nAnon indb.(ind_relevance)) None indb.(ind_type)) (rev mdecl.(ind_bodies)) in
  let* s _ key_inds _ := add_old_context s (Some "ind") cxt in
  cc s key_inds.


Section CheckArg.

  Context {A : Type}.
  Context (bop : A -> A -> A).
  Context (default : A).
  Context (E : global_env).
  Context (kname : kername).

Definition check_args_by_arg : state -> (state -> term -> A) -> context -> A :=
  fun s check_arg args =>
  fold_left_state
    ( fun i ' (mkdecl an z ty) s cc =>
        match z with
        | None => let* s key_arg := add_old_var s (Some "arg") an ty in
                  let rty := reduce_full E s (get_type s key_arg) in
                  bop (check_arg s rty) (cc s key_arg)
        | Some db => let* s key_let := add_old_letin s (Some "letin") an db ty in
                     cc s key_let
        end
  )
  args s (fun _ _ => default).

Definition check_ctors_by_arg : state -> (state -> term -> A) -> list context -> A :=
  fun s check_arg lcxt =>
  fold_left bop (map (fun cxt => check_args_by_arg s check_arg cxt) lcxt) default.

End CheckArg.

Definition debug_check_args_by_arg {A} : global_env -> state -> (state -> term -> A) -> context -> list A :=
  fun E s check_arg cxt =>
  check_args_by_arg (@app A) [] E s (fun x s => [check_arg x s]) cxt.

Definition debug_check_ctors_by_arg {A} : global_env -> state -> (state -> term -> A) -> list context -> list (list A) :=
  fun E s check_arg lcxt => map (fun cxt => debug_check_args_by_arg E s check_arg cxt) lcxt.
