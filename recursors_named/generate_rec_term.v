From MetaCoq.Utils Require Import utils.
From MetaCoq.Utils Require Import MCString.
From MetaCoq.Template Require Import All.

Require Import preliminary.
Require Import naming.
Require Import commons.
Require Import generate_types.

Section GenRecTerm.

  Context (kname  : kername).
  Context (mdecl  : mutual_inductive_body).
  Context (U : term).
  Context (pos_block : nat).
  Context (E : list (kername * mutual_inductive_body * kername)).

  Definition params := mdecl.(ind_params).
  Definition nb_params := #|params|.
  Definition relev_out_sort := relev_sort U.

(* Print BasicAst.context_decl. *)

  Section GenFixBlock.

    Context (pos_indb : nat).
    Context (indb : one_inductive_body).

    Definition relev_ind_sort := indb.(ind_relevance).
    Definition indices := indb.(ind_indices).

    Definition gen_prediate : predicate term :=
      mk_predicate
        []
        (list_tVar naming_param params)
        (    (mkBindAnn (nNamed "y") relev_ind_sort)
          :: (rev (mapi aname_indice' (rev indices))))
        (tApp (tVar (naming_pred pos_indb))
              (list_tVar (make_name "j") indices ++ [tVar "y"])).

    Definition Fix_rec_call (pos_arg : nat) (arg_type : term) (next_closure : list term) : list term :=
    match decide_rec_call kname nb_params arg_type with
    | Some (pos_indb', indices) => (tApp (tVar (make_name "F" pos_indb'))
                                         (indices ++ [tVar (naming_arg pos_arg)]))
                                   :: next_closure
    | None => next_closure
    end.

    Definition gen_rec_tm (args : context) :=
      fold_right_i (fun pos_arg arg next_closure =>
          tVar (naming_arg pos_arg) ::
          (Fix_rec_call pos_arg arg.(decl_type) next_closure))
      []
      args.

    Definition gen_branch (pos_ctor : nat) (ctor : constructor_body) : branch term :=
      let acxt := rev (mapi aname_arg (ctor.(cstr_args))) in
      let tm := tApp (tVar (make_name_bin "f" pos_indb pos_ctor))
                     (gen_rec_tm (rev ctor.(cstr_args)))          in
      mk_branch acxt tm.

    Definition gen_match : term :=
      tCase (mk_case_info (mkInd kname pos_indb) nb_params relev_out_sort)
            gen_prediate
            (tVar "x")
            (mapi gen_branch indb.(ind_ctors)).

    Definition gen_Fix_block : def term :=
      mkdef _ (mkBindAnn (nNamed (make_name "F" pos_indb)) relev_out_sort)
              (make_return_type kname mdecl pos_indb relev_ind_sort indices)
              (closure_indices tLambda indices
              (tLambda (mkBindAnn (nNamed "x") relev_ind_sort)
                      (make_ind kname params pos_indb indices)
                      gen_match))
              #|indices|.

  End GenFixBlock.

  Definition gen_Fix : term :=
    tFix (mapi gen_Fix_block mdecl.(ind_bodies)) pos_block.

  Definition gen_rec_term (indb : one_inductive_body) :=
     closure_params tLambda params
    (closure_type_preds kname mdecl U tLambda
    (closure_type_ctors kname mdecl U E tLambda
     gen_Fix)).

End GenRecTerm.