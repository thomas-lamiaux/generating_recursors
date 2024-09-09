From RecAPI Require Import api_debruijn.
From RecAPI Require Import commons.
From RecAPI Require Import generate_types.



Section GenRecType.

  Context (mdecl : mutual_inductive_body).
  Context (pdecl : preprocess_mutual_inductive_body).
  Context (U : output_univ).
  (* Context (E : env_param). *)


  (* Generation Type of the Recursor *)
  Definition gen_rec_type (indb : one_inductive_body) : term :=
    let e := replace_ind pdecl.(pmb_kname) mdecl init_info in
    e <- closure_uparams tProd pdecl.(pmb_uparams) e ;;
    e <- closure_preds pdecl U tProd e ;;
    e <- closure_ctors pdecl U tProd e ;;
    make_return_type pdecl pdecl.(pmb_pos_indb) indb e.

End GenRecType.