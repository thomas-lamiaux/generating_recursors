From MetaCoq.Utils Require Import utils.
From MetaCoq.Utils Require Import MCString.
From MetaCoq.Template Require Import All.

Require Import preliminary.
Require Import commons.

Section GenRecTerm.

  Context (kname  : kername).
  Context (pos_block : nat).
  Context (mdecl  : mutual_inductive_body).

  Definition params := mdecl.(ind_params).
  Definition nb_params := #|params|.


  (* Definition *)

  Definition gen_Fix (l : list (def term)) : term :=
    tFix l 1.

  Definition gen_rec_term :=
    let lProp := (tSort sProp) in
    (* let mdecl := preprocessing_mind kname mdecl in *)
     closure_param tLambda mdecl
    (closure_pred  tLambda kname mdecl lProp
    (closure_ctors tLambda kname mdecl
    (tRel 0))).

End GenRecTerm.