From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.

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

Definition get_ident (x : aname) : ident :=
  match x.(binder_name) with
  | nNamed s => s
  | _ => "Error"
  end.


(* Naming scheme *)
Definition naming_pred    pos := make_name0 "P" pos.
Definition naming_uparam   pos := make_name0 "A" pos.
Definition naming_nuparam  pos := make_name0 "B" pos.
Definition naming_indice  pos := make_name "i" pos.
Definition naming_indice' pos := make_name "j" pos.
Definition naming_arg     pos := make_name "x" pos.

(* aname scheme *)
Definition aname_pred    pos := mkBindAnn (nNamed (naming_pred pos)) Relevant.
Definition aname_uparam  pos (an : context_decl) := mkBindAnn (nNamed (naming_uparam pos)) Relevant.
Definition aname_nuparam pos (an : context_decl) := mkBindAnn (nNamed (naming_nuparam pos)) Relevant.
Definition aname_indice  pos (an : context_decl) := mkBindAnn (nNamed (naming_indice pos))  an.(decl_name).(binder_relevance).
Definition aname_indice' pos (an : context_decl) := mkBindAnn (nNamed (naming_indice' pos)) an.(decl_name).(binder_relevance).
Definition aname_arg     pos (an : context_decl) := mkBindAnn (nNamed (naming_arg pos))     an.(decl_name).(binder_relevance).