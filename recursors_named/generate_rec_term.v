From MetaCoq.Utils Require Import utils.
From MetaCoq.Utils Require Import MCString.
From MetaCoq.Template Require Import All.

From RecNamed Require Import naming.
From RecNamed Require Import commons.
From RecNamed Require Import generate_rec_call.
From RecNamed Require Import generate_types.


Section GenRecTerm.

  Context (pdecl : preprocess_mutual_inductive_body).
  Context (U : output_univ).
  Context (E : param_env).

  Definition kname := pdecl.(pmb_kname).
  Definition uparams  := pdecl.(pmb_uparams).
  Definition nuparams := pdecl.(pmb_nuparams).

  (* 1. Generates a branch of the Fix *)
  Section GenFixBlock.

    Context (pos_indb : nat).
    Context (indb : one_inductive_body).

    Definition relev_ind_sort := indb.(ind_relevance).
    Definition indices := indb.(ind_indices).

    (* 2. Generates the tCase *)

    (* 2.1 Generates case info: which ind, nb_params, relevance*)
    Definition gen_case_info :=
      {| ci_ind       := mkInd kname pos_indb ;
         ci_npar      := pdecl.(pmb_nb_uparams) + pdecl.(pmb_nb_nuparams);
         ci_relevance := U.(out_relev)
      |}.

    (* 2.2 Generates Predicate
    ??? / Parameters / return type, in our case (P y) *)
    Definition gen_prediate : predicate term :=
      {| puinst   := [];
         pparams  :=     list_tVar naming_uparam uparams
                     ++ list_tVar naming_nuparam nuparams;
         pcontext :=    (mkBindAnn (nNamed "y") relev_ind_sort)
                     :: (rev (mapi aname_indice' (rev indices)));
         preturn  := mkApps (make_predc pos_indb nuparams (list_tVar (make_name "j") indices))
                            [tVar "y"]
      |}.


    (* 2.3 Generates Branches *)
    (* Extract rec call *)
    Definition Fix_rec_call (pos_arg : nat) (arg_type : term) (next_closure : list term) : list term :=
      match rec_pred pdecl E arg_type with
      | Some (_, tmP) => (mkApps tmP [tVar (naming_arg pos_arg)]) :: next_closure
      | None => next_closure
      end.

    (* Custom fct for rec call *)
    Definition gen_rec_tm (args : context) :=
      fold_right_i (fun pos_arg arg next_closure =>
      match arg.(decl_body) with
      | Some bd => next_closure
      | None =>     tVar (naming_arg pos_arg)
                :: (Fix_rec_call pos_arg arg.(decl_type) next_closure)
      end)
      []
      args.

    (* Generates a branch of the case *)
    Definition gen_branch (pos_ctor : nat) (ctor : constructor_body) : branch term :=
      {| bcontext := rev (mapi aname_arg ctor.(cstr_args)) ;
         bbody    := mkApps (tVar (make_name_bin "f" pos_indb pos_ctor))
                            (   list_tVar naming_nuparam nuparams
                             ++ (gen_rec_tm (rev ctor.(cstr_args))))
      |}.


    (* 2.4 Generates the case: match x as e return P with ... end  *)
    (* case_info / predicates P / var induction / branches *)
    Definition gen_match : term :=
      tCase gen_case_info
            gen_prediate
            (tVar "x")
            (mapi gen_branch indb.(ind_ctors)).


    (* 2.5 Generates the branch of the Fix *)
    Definition gen_Fix_block : def term :=
      {| dname := mkBindAnn (nNamed (make_name "F" pos_indb)) U.(out_relev) ;
         dtype := make_return_type pdecl pos_indb relev_ind_sort indices ;
         dbody := (closure_nuparams tLambda nuparams
                  (closure_indices tLambda indices
                  (tLambda (mkBindAnn (nNamed "x") relev_ind_sort)
                           (make_ind kname pos_indb uparams nuparams indices)
                           gen_match))) ;
         rarg  := pdecl.(pmb_nb_nuparams) + #|indices|
      |}.

  End GenFixBlock.

  (* Generates the Fix *)
  Definition gen_Fix : term :=
    tFix (mapi gen_Fix_block pdecl.(pmb_ind_bodies)) pdecl.(pmb_pos_idecl).

  Definition gen_rec_term :=
     closure_uparams  tLambda uparams
    (closure_type_preds pdecl U tLambda
    (closure_type_ctors pdecl U E tLambda
     gen_Fix)).

End GenRecTerm.