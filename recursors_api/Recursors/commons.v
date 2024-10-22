From RecAPI Require Import api_debruijn.


(* 2. Naming *)
From MetaCoq Require Import MCString.

Open Scope bs_scope.

Definition make_name : ident -> nat -> ident :=
  fun s n => (s ++ (string_of_nat n)).

Definition make_name0 : ident -> nat -> ident :=
  fun s n => match n with
  | 0 => s
  | S n => make_name s n
  end.

Definition make_name_bin : ident -> nat -> nat -> ident :=
  fun s n m => s ++ (string_of_nat n) ++ (string_of_nat m).

Definition naming_pred : nat -> ident :=
  fun pos => make_name0 "P" pos.


(* 3. To make terms *)

(* Builds: P_i B0 ... Bm i1 ... il *)
Section Pred.

  Context (id_preds : list ident).
  Context (pos_indb : nat).
  Context (id_nuparams id_indices : list ident).

  Definition make_pred : list term -> list term -> state -> term :=
    fun nuparams indices s =>
    mkApps (get_one_of_term id_preds pos_indb s) (nuparams ++ indices).

  Definition make_predn : list term -> state -> term :=
    fun indices s =>
      make_pred (get_term id_nuparams s) indices s.

  (* Builds: P_i B0 ... Bm i1 ... il *)
  Definition make_predni : state -> term :=
    fun s => make_pred (get_term id_nuparams s) (get_term id_indices s) s.

End Pred.