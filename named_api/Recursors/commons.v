From NamedAPI Require Import api_debruijn.

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
    mkApps (geti_term id_preds pos_indb s) (nuparams ++ indices).

  Definition make_predn : list term -> state -> term :=
    fun indices s =>
      make_pred (get_terms id_nuparams s) indices s.

  (* Builds: P_i B0 ... Bm i1 ... il *)
  Definition make_predni : state -> term :=
    fun s => make_pred (get_terms id_nuparams s) (get_terms id_indices s) s.

End Pred.