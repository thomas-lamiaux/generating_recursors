From MetaCoq.Utils Require Import utils.
From MetaCoq.Utils Require Import MCString.
From MetaCoq.Template Require Import All.

From MetaCoq Require Import BasePrelude.

Search infolocal.


Require Import commons.
Require Import generate_types.



Section GenRecType.

  Context (mdecl : mutual_inductive_body).
  Context (pdecl : preprocess_mutual_inductive_body).
  Context (U : output_univ).
  Context (E : env_param).


  (* Generation Type of the Recursor *)
  Definition gen_rec_type (idecl : one_inductive_body) : term :=
    let e := make_initial_info pdecl.(pmb_kname) mdecl in
    e <- closure_uparams tProd pdecl.(pmb_uparams) e ;;
    e <- closure_preds pdecl U tProd e ;;
    e <- closure_ctors pdecl U tProd e ;;
    make_return_type pdecl pdecl.(pmb_pos_idecl) idecl e.

End GenRecType.