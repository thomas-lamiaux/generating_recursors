From RecAPI Require Import api_debruijn.
From RecAPI Require Import commons.
From RecAPI Require Import generate_types.



Section GenRecType.

  Context (kname : kername).
  Context (mdecl : mutual_inductive_body).
  Context (nb_uparams : nat).
  Context (U : output_univ).
  Context (E : global_env).
  Context (Ep : env_param).


  (* Generation Type of the Recursor *)
  Definition gen_rec_type (pos_indb : nat) : term :=
    let e := add_mdecl kname nb_uparams mdecl init_info in
    let e := replace_ind kname mdecl e in
    let* e <- closure_uparams tProd kname e in
    let* e <- closure_preds kname U tProd e in
    let* e <- closure_ctors kname U E Ep tProd e in
    make_return_type kname pos_indb e.

End GenRecType.