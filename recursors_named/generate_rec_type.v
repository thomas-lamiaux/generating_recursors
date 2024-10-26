From MetaCoq.Utils Require Import utils.
From MetaCoq.Utils Require Import MCString.
From MetaCoq.Template Require Import All.

From RecNamed Require Import commons.
From RecNamed Require Import generate_types.


Section GenRecType.

  Context (pdecl  : preprocess_mutual_inductive_body).
  Context (U : output_univ).
  Context (E : param_env).

  (* Generation Type of the Recursor *)
  Definition gen_rec_type (idecl : one_inductive_body) : term :=
     closure_uparams  tProd pdecl.(pmb_uparams)
    (closure_type_preds pdecl U tProd
    (closure_type_ctors pdecl U E tProd
    (make_return_type pdecl pdecl.(pmb_pos_idecl)
      idecl.(ind_relevance) idecl.(ind_indices)))).

End GenRecType.