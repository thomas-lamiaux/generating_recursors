From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import All.

Require Import preliminary.

Definition make_raname (s : ident) := mkBindAnn (nNamed s) Relevant.

(* Functions to create names *)
Definition make_name (s : ident) (n : nat) :=
  String.append s (string_of_nat n).

Definition make_name0 (s : ident) (n : nat) : ident :=
  match n with
  | 0 => s
  | S n => make_name s n
  end.

Definition make_name_bin (s : ident) (n m : nat) :=
  String.append s (String.append (string_of_nat n) (string_of_nat m)).

Definition name_param pos := make_name "A" pos.
Definition name_indice pos := make_name "i" pos.
Definition name_arg pos := make_name "x" pos.
Definition name_pred pos := make_name0 "P" pos.

Definition aname_param pos := mkBindAnn (nNamed (name_param pos)) Relevant.
Definition aname_indice pos := mkBindAnn (nNamed (name_indice pos)) Relevant.
Definition aname_arg pos := mkBindAnn (nNamed (name_arg pos)) Relevant.
Definition aname_pred pos := mkBindAnn (nNamed (name_pred pos)) Relevant.

Definition tVar_param pos : term := tVar (name_param pos).
Definition tVar_indice pos : term := tVar (name_indice pos).
Definition tVar_arg pos : term := tVar (name_arg pos).
Definition tVar_pred pos : term := tVar (name_pred pos).

(* Computes the list [tVar "A1", ..., tVar "Ak"] where A1, ... Ak are the parameters *)
Definition gen_list_param (params : context) : list term :=
  map (fun param => tVar (get_ident param.(decl_name)))
      (rev params). (*Pamaters need to be inversed as context are inversed *)

Definition gen_list {A B C} (naming : nat -> A -> B) (f : B -> C) l : list C :=
  mapi (fun i a => f (naming i a)) l.

(* Computes the list [tVar "i0", ..., tVar "ik"] representing indices *)
Definition gen_list_indices (indices : context) : list term :=
  mapi (fun i _ => tVar_indice i) indices.

(* Computes the list [tVar "x0", ..., tVar "xk"] representing arguments *)
Definition gen_list_args (args : context) : list term :=
  mapi (fun i _ => tVar_arg i) args.