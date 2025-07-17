From TypingSafeAPI Require Import core.
From TypingSafeAPI Require Import fold_functions.
(* From TypingSafeAPI Require Import inductive_access. *)
(* From TypingSafeAPI Require Import context_access. *)
From TypingSafeAPI Require Import context_access.

(* Interface to create terms

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

*)


(* Definition fold_right_state {A B X state} (n : nat) (s : state) (l : list A)
  (tp : state -> nat -> A -> (state -> iter_T n X B) -> B) (t : state -> iter_T n (list X) B) : B :=
  let fix aux (s : state) (pos : nat) (ids : Vector.t (list X) n) (l : list A) {struct l} : B :=
    match l with
    | [] => iter_X (Vector.map (@List.rev _) ids) (t s)
    | a :: l => tp s pos a (fun s => X_iter (fun x => aux s (S pos) (Vector.map2 (@List.cons _) x ids) l))
    end
  in
  aux s 0 (Vector.const [] n) l. *)


Definition fold_right_state {A B X state} (s : state) (l : list A)
  (tp : state -> nat -> A -> (state -> X -> B) -> B) (t : state -> list X -> B) : B :=
  let fix aux (s : state) (pos : nat) (ids : list X) (l : list A) {struct l} : B :=
    match l with
    | [] => t s (List.rev ids)
    | a :: l => tp s pos a (fun s id => aux s (S pos) (id ::ids) l)
    end
  in
  aux s 0 [] l.

Definition fold_left_state {A B X state} (s : state) (l : list A)
  (tp : state -> nat -> A -> (state -> X -> B) -> B) (t : state -> list X -> B) : B :=
    fold_right_state s (List.rev l) tp t.

Definition fresh_keys : state -> nat -> keys :=
  fun s length => List.rev (seq #|s.(state_new_context)| length).



(* 1. Keep Vars and Binders *)
Definition kp_cdecl {X} : state -> context_decl -> (state -> key -> X) -> X :=
fun s cdecl cc =>
  let s' := add_old_cdecl s cdecl in
  cc s' (fresh_key s).

Definition kp_context {X} : state -> context -> (state -> list key -> X) -> X :=
fun s cdecl cc =>
  let s' := add_old_context s cdecl in
  cc s' (fresh_keys s #|cdecl|).

Definition mk_cdecl {X} : state -> context_decl -> (state -> key -> X) -> X :=
fun s cdecl cc =>
  let s' := add_old_cdecl s cdecl in
  cc s' (fresh_key s).

Definition mk_context {X} : state -> context -> (state -> list key -> X) -> X :=
fun s cdecl cc =>
  let s' := add_fresh_context s cdecl in
  cc s' (fresh_keys s #|cdecl|).


(* 2. Make Vars and Binders *)
Definition kp_binder binder : state -> aname -> term -> (state -> key -> term) -> term :=
  fun s an A cc =>
  let A' := subst0 s.(state_subst) A in
  let* s' key_bind := kp_cdecl s (vass an A) in
  binder an A' (cc s' key_bind).

Definition kp_tProd := kp_binder tProd.
Definition kp_tLambda := kp_binder tLambda.

Definition mk_binder binder : state -> aname -> term -> (state -> key -> term) -> term :=
  fun s an A cc =>
    let* s key_bind := mk_cdecl s (vass an A) in
    binder an A (cc s key_bind).

Definition mk_tProd := mk_binder tProd.
Definition mk_tLambda := mk_binder tLambda.


Definition closure_context : state -> context -> (state -> list key -> term) -> term :=
  fun s Δ cc =>
    let s' := add_old_context s Δ in
    let key_context := fresh_keys s #|Δ| in
    it_mkProd_or_LetIn (subst_context s.(state_subst) 0 Δ) (cc s' key_context).
    (* fold_left_state s Δ (fun s _ ' (mkdecl an bd A) cc =>
      match bd with
        | Some bd => todo
        | None    => let* s key_var := fbinder s an A in
                    cc s key_var
        end
    ) cc. *)

(* Definition kp_tProd_or_LetIn := closure_context kp_tProd. *)
(* Definition mk_tProd_or_LetIn := closure_context mk_tProd. *)


(* 3. Inductive Terms *)
(* Builds: Ind A1 ... An B0 ... Bm i1 ... il *)
Definition make_ind : state -> kername -> nat -> keys -> keys -> keys -> term :=
  fun s kname pos_indb key_uparams key_nuparams key_indices =>
  mkApps (tInd (mkInd kname pos_indb) [])
          (  get_terms s key_uparams
          ++ get_terms s key_nuparams
          ++ get_terms s key_indices  ).

Arguments make_ind _ _ pos_indb key_uparams key_nuparams key_indices.

Definition make_indt : state -> kername -> nat -> keys -> list term -> list term -> term :=
  fun s kname pos_indb key_uparams nuparams indices =>
  mkApps (tInd (mkInd kname pos_indb) [])
          (get_terms s key_uparams ++ nuparams ++ indices).

Arguments make_indt s kname pos_indb key_uparams nuparams indices.

(* Builds: Cst A1 ... An B0 ... Bm *)
Definition make_cst : state -> kername -> nat -> nat -> keys -> keys -> term :=
  fun s kname pos_indb pos_ctor key_uparams key_nuparams =>
  mkApps (tConstruct (mkInd kname pos_indb) pos_ctor [])
          (get_terms s key_uparams ++ get_terms s key_nuparams).

Arguments make_cst _ pos_indb pos_ctor _ key_uparams key_nuparams.