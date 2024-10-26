From RecAPI Require Import api_debruijn.
From RecAPI Require Import commons.
From RecAPI Require Import generate_types.



Section GenRecType.

  Context (kname : kername).
  Context (mdecl : mutual_inductive_body).
  Context (nb_uparams : nat).
  Context (U : output_univ).
  Context (E : global_env).
  Context (Ep : param_env).


  (* Generation Type of the Recursor *)
  Definition gen_rec_type (pos_indb : nat) : term :=
    let s := add_mdecl kname nb_uparams mdecl init_state in
    let* s <- replace_ind kname s in
    let* id_uparams  s <- closure_uparams tProd kname s in
    let* id_preds    s <- closure_preds   tProd kname U id_uparams s in
    let* id_ctors    s <- closure_ctors   tProd kname U E Ep id_uparams id_preds s in
    make_return_type kname pos_indb id_uparams id_preds s.

End GenRecType.