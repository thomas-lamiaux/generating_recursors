From NamedAPI Require Import api_debruijn.

Definition naming_pred : nat -> ident :=
  fun pos => make_name0 "P" pos.


(* 3. To make terms *)

(* Builds: P_i B0 ... Bm i1 ... il *)
Section Pred.

  Context (s : state).
  Context (key_preds : keys).
  Context (pos_indb : nat).

  Definition make_pred : list term -> list term -> term :=
    fun nuparams indices =>
    mkApps (geti_term s key_preds pos_indb) (nuparams ++ indices).

  Context (key_nuparams : keys).

  Definition make_predn : list term -> term :=
    fun indices => make_pred (get_terms s key_nuparams) indices.

  Context (key_indices : keys).

  (* Builds: P_i B0 ... Bm i1 ... il *)
  Definition make_predni : term :=
    make_pred (get_terms s key_nuparams) (get_terms s key_indices).

End Pred.