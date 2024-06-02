From MetaCoq.Utils Require Import utils.
From MetaCoq.Utils Require Import MCString.
From MetaCoq.Template Require Import All.

Require Import commons.
Require Import generate_types.


Section GenRecType.

  Context (kname  : kername).
  Context (mdecl  : mutual_inductive_body).
  Context (U : term).
  Context (pos_block : nat).
  Context (E : list (kername * mutual_inductive_body * kername * kername)).


  Definition params := mdecl.(ind_params).

  (* Generation Type of the Recursor *)
  Definition gen_rec_type (indb : one_inductive_body) : term :=
     closure_params tProd params
    (closure_type_preds kname mdecl U tProd
    (closure_type_ctors kname mdecl U E tProd
    (make_return_type kname mdecl pos_block (relev_sort (tSort indb.(ind_sort))) indb.(ind_indices)))).

End GenRecType.