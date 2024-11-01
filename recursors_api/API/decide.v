From RecAPI Require Import core.
From RecAPI Require Import fold_functions.
From RecAPI Require Import context_access.
From RecAPI Require Import context_store.

(* Interface to decide properties
Context {A : Type} (bop : A -> A -> A) (default : A)
Context (E : global_env) (kname : kername)

- check_args_by_arg : (term -> state -> A) -> context -> state -> A
- check_ctors_by_arg : (term -> state -> A) -> list context -> state -> A
- debug_check_args_by_arg {A} : global_env -> (term -> state -> A) -> context -> state -> list A
- debug_check_ctors_by_arg {A} : global_env -> (term -> state -> A) -> list context -> state -> list (list A)
*)

Definition add_inds {X} : mutual_inductive_body -> state -> (list ident -> state -> X) -> X :=
  fun mdecl s t =>
  let cxt := mapi (fun i indb => mkdecl (mkBindAnn nAnon indb.(ind_relevance)) None indb.(ind_type)) (rev mdecl.(ind_bodies)) in
  let* _ id_inds _ := add_old_context (Some "ind") cxt s in
  t id_inds.


Section CheckArg.

  Context {A : Type}.
  Context (bop : A -> A -> A).
  Context (default : A).
  Context (E : global_env).
  Context (kname : kername).

Definition check_args_by_arg : (term -> state -> A) -> context -> state -> A :=
  fun check_arg args s =>
  fold_left_state
    ( fun i arg s t =>
        let* id_arg s := add_old_var (Some "arg") arg s in
        let rty := reduce_full E s (get_type id_arg s) in
        match arg.(decl_body) with
        | None => bop (check_arg rty s) (t id_arg s)
        | Some _ => t id_arg s
        end
  )
  args s (fun _ _ => default).

Definition check_ctors_by_arg : (term -> state -> A) -> list context -> state -> A :=
  fun check_arg lcxt s =>
  fold_left bop (map (fun cxt => check_args_by_arg check_arg cxt s) lcxt) default.

End CheckArg.

Definition debug_check_args_by_arg {A} : global_env -> (term -> state -> A) -> context -> state -> list A :=
  fun E check_arg cxt s =>
  check_args_by_arg (@app A) [] E (fun x s => [check_arg x s]) cxt s.

Definition debug_check_ctors_by_arg {A} : global_env -> (term -> state -> A) -> list context -> state -> list (list A) :=
  fun E check_arg lcxt s => map (fun cxt => debug_check_args_by_arg E check_arg cxt s) lcxt.
