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
    let ' (id_inds, e) := replace_ind kname e in
    let* id_uparams e <- closure_uparams tProd kname e in
    let* id_preds    e <- closure_preds   tProd kname U id_uparams e in
    let* id_ctors    e <- closure_ctors   tProd kname U E Ep id_uparams id_preds e in
    make_return_type kname pos_indb id_uparams id_preds e.

End GenRecType.