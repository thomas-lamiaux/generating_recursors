From RecAPI Require Import core.
From RecAPI Require Import fold_functions.


(* Add terms to state
- fresh_ident : option ident -> state -> ident
- add_old_var {X}       : option ident -> context_decl -> state -> (ident -> state -> X) -> X
- add_old_context {X}   : option ident -> context -> state -> (list ident -> state -> X) -> X :=
- add_fresh_var {X}     : option ident -> context_decl -> state -> (ident -> state -> X) -> X
- add_fresh_context {X} : option ident -> context -> state -> (list ident -> state -> X) -> X
- subst_old_var {X}     : term -> state -> (state -> X) -> X
- subst_old_vars {X}    : list term -> state -> (state -> X) -> X
- save_term {X}         : option ident -> context_decl -> state -> (ident ->  state -> X) -> X
- notation: "let* x .. z '<-' c1 'in' c2"

*)


#[local] Definition fresh_ident_aux : option ident -> nat -> ident :=
  fun x k => match x with
  | Some s => s ^ (string_of_nat k)
  | None   => "Var" ^ (string_of_nat k)
  end.

Definition fresh_ident : option ident -> state -> ident :=
  fun x s => fresh_ident_aux x (length s.(state_context)).

#[local] Definition lift1 : list term -> list term :=
    map (lift0 1).

(* Add a previously existing var to the current context *)
Definition add_old_var {X} : option ident -> context_decl -> state -> (ident -> state -> X) -> X :=
  fun x cdecl s t =>
    let id := fresh_ident x s in
    let updated_cdecl := weaken_decl s cdecl in
    let s := mk_state (mk_idecl id false updated_cdecl :: s.(state_context))
                ((tRel 0) :: lift1 s.(state_subst)) s.(state_ind) in
    t id s.

Definition add_old_context {X} : option ident -> context -> state -> (list ident -> state -> X) -> X :=
  fun x cxt s t => fold_right_state (fun _ cdecl s t => add_old_var x cdecl s t) cxt s t.

(* Add a fresh var to the current context *)
Definition add_fresh_var {X} : option ident -> context_decl -> state -> (ident -> state -> X) -> X :=
  fun x cdecl s t =>
  let id := fresh_ident x s in
  let s := mk_state (mk_idecl id false cdecl :: s.(state_context))
            (lift1 s.(state_subst)) s.(state_ind) in
  t id s.

(* Add a fresh context to the current context *)
Definition add_fresh_context {X} : option ident -> context -> state -> (list ident -> state -> X) -> X :=
  fun x cxt s t => fold_right_state (fun _ cdecl s t => add_fresh_var x cdecl s t) cxt s t.

(* Remove a previously existing var by substituting it *)
Definition subst_old_var {X} : term -> state -> (state -> X) -> X :=
  fun tm ' (mk_state cxt subst inds) t => t (mk_state cxt (tm :: subst) inds).

(* Remove n previously existing var by substituting them *)
Definition subst_old_vars {X} : list term -> state -> (state -> X) -> X :=
  fun ltm ' (mk_state cxt subst inds) t => t (mk_state cxt (rev ltm ++ subst) inds).

(* Save a term to state that is not part of the context *)
Definition save_term {X} : option ident -> context_decl -> state -> (ident ->  state -> X) -> X:=
  fun x cdecl s t =>
    let id := fresh_ident x s in
    let s := mk_state (mk_idecl id true cdecl :: s.(state_context))
                      s.(state_subst) s.(state_ind) in
    t id s.

Notation "let* x .. z '<-' c1 'in' c2" := (c1 (fun x => .. (fun z => c2) ..))
(at level 100, x binder, z binder, c1 at next level, right associativity).

