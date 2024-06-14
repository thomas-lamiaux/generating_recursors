From MetaCoq.Utils Require Import utils.
From MetaCoq.Utils Require Import MCString.
From MetaCoq.Template Require Import All.

Require Import naming.
Require Import commons.
Require Import generate_rec_call.
Require Import generate_types.


Section GenRecTerm.

  Context (pdecl : preprocess_mutual_inductive_body).
  Context (U : output_univ).
  Context (E : env_param).

  Definition kname := pdecl.(pmb_kname).
  Definition uparams  := pdecl.(pmb_uparams).
  Definition nuparams := pdecl.(pmb_nuparams).

  (* 1. Generates the Fix branch associated to an inductive block  *)
  Section GenFixBlock.

    Context (pos_indb : nat).
    Context (indb : one_inductive_body).

    Definition relev_ind_sort := indb.(ind_relevance).
    Definition indices := indb.(ind_indices).

    Definition gen_prediate : predicate term :=
      mk_predicate
        []
        (   list_tVar naming_uparam uparams
         ++ list_tVar naming_nuparam nuparams)
        (    (mkBindAnn (nNamed "y") relev_ind_sort)
          :: (rev (mapi aname_indice' (rev indices))))
        (mkApps (tVar (naming_pred pos_indb))
              (list_tVar (make_name "j") indices ++ [tVar "y"])).

    Definition Fix_rec_call (pos_arg : nat) (arg_type : term) (next_closure : list term) : list term :=
      match rec_pred pdecl E arg_type with
      | Some (_, tmP) => (mkApps tmP [tVar (naming_arg pos_arg)]) :: next_closure
      | None => next_closure
      end.

    Definition gen_rec_tm (args : context) :=
      fold_right_i (fun pos_arg arg next_closure =>
      match arg.(decl_body) with
      | Some bd => next_closure
      | None =>
          tVar (naming_arg pos_arg) ::
          (Fix_rec_call pos_arg arg.(decl_type) next_closure)
      end)
      []
      args.

    Definition gen_branch (pos_ctor : nat) (ctor : constructor_body) : branch term :=
      let acxt := rev (mapi aname_arg (ctor.(cstr_args))) in
      let tm := mkApps (tVar (make_name_bin "f" pos_indb pos_ctor))
                       (gen_rec_tm (rev ctor.(cstr_args))) in
      mk_branch acxt tm.

    Definition gen_match : term :=
      tCase (mk_case_info (mkInd kname pos_indb) pdecl.(pmb_nb_uparams) U.(out_relev))
            gen_prediate
            (tVar "x")
            (mapi gen_branch indb.(ind_ctors)).

    Definition gen_Fix_block : def term :=
      mkdef _ (mkBindAnn (nNamed (make_name "F" pos_indb)) U.(out_relev))
              (make_return_type pdecl pos_indb relev_ind_sort indices)
              (closure_indices tLambda indices
              (tLambda (mkBindAnn (nNamed "x") relev_ind_sort)
                       (make_ind kname pos_indb uparams uparams indices)
                       gen_match))
              #|indices|.

  End GenFixBlock.

  Definition gen_Fix : term :=
    tFix (mapi gen_Fix_block pdecl.(pmb_ind_bodies)) pdecl.(pmb_pos_idecl).

  Definition gen_rec_term :=
     closure_uparams  tLambda uparams
    (closure_nuparams tLambda nuparams
    (closure_type_preds pdecl U tLambda
    (closure_type_ctors pdecl U E tLambda
     gen_Fix))).

End GenRecTerm.