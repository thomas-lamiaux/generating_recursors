From MetaCoq.Utils Require Import utils.
From MetaCoq.Utils Require Import MCString.
From MetaCoq.Template Require Import All.

Require Import preliminary.
Require Import commons.


Section GenTypeRec.

  Context (kname  : kername).
  Context (pos_block : nat).
  Context (mdecl  : mutual_inductive_body).

  Definition params := mdecl.(ind_params).
  Definition nb_params := #|params|.

  (* Generation Output *)
  (* forall i0 : t0, ... il : tl,
     forall (x : Ind A0 ... An i0 ... il),
      P i0 ... il x *)
  Definition gen_output (indices : context) : term :=
    (* Closure indices : forall i0 : t0, ... il : tl,  *)
    fold_right_i
      (fun pos_index indice next_closure =>
        tProd (mkBindAnn (nNamed (make_name ["i"] pos_index)) Relevant)
              indice.(decl_type)
              next_closure)
      (* Definition of forall (x : Ind A0 ... An i0 ... il),  P i0 ... il x  *)
      ( tProd (mkBindAnn (nNamed "x") Relevant)
              (tApp (tInd (mkInd kname pos_block) [])
                    (gen_list_param params ++ gen_list_indices indices ))
              (tApp (tVar (make_pred "P" pos_block))
                    (gen_list_indices indices ++ [tVar "x"])))
      (* Indices *)
      (rev indices).

  (* Generation Type of the Recursor *)
  Definition gen_rec_type (indb : one_inductive_body) : term :=
    let lProp := (tSort sProp) in
    (* let mdecl := preprocessing_mind kname mdecl in *)
     closure_param tProd mdecl
    (closure_pred  tProd kname mdecl lProp
    (closure_ctors tProd kname mdecl
    (gen_output indb.(ind_indices)))).

End GenTypeRec.