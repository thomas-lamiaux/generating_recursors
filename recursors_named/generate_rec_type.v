From MetaCoq.Utils Require Import utils.
From MetaCoq.Utils Require Import MCString.
From MetaCoq.Template Require Import All.

Require Import preliminary.
Require Import generate_types.


Section GenRecType.

  Context (kname  : kername).
  Context (pos_block : nat).
  Context (mdecl  : mutual_inductive_body).

  (* Generation Type of the Recursor *)
  Definition gen_rec_type (indb : one_inductive_body) : term :=
    let lProp := (tSort sProp) in
    (* let mdecl := preprocessing_mind kname mdecl in *)
     closure_param tProd mdecl
    (closure_pred  tProd kname mdecl lProp
    (closure_ctors tProd kname mdecl
    (return_type kname mdecl pos_block indb.(ind_indices)))).

End GenRecType.