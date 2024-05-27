From MetaCoq.Utils Require Import utils.
From MetaCoq.Utils Require Import MCString.
From MetaCoq.Template Require Import All.

Require Import namming.
Require Import commons.
Require Import generate_types.

Section GenRecTerm.

  Context (kname  : kername).
  Context (pos_block : nat).
  Context (mdecl  : mutual_inductive_body).

  Definition params := mdecl.(ind_params).
  Definition nb_params := #|params|.

(* Print BasicAst.context_decl. *)

  Section GenFixBlock.

    Context (pos_indb : nat).
    Context (indb : one_inductive_body).

    Definition indices := indb.(ind_indices).

    Definition gen_prediate : predicate term :=
      mk_predicate
        []
        (list_tVar naming_param params)
        (    (mkBindAnn (nNamed "y") Relevant)
          :: (rev (mapi (fun pos_arg _ => make_raname (make_name "j" pos_arg)) indices)))
        (tApp (tVar (naming_pred pos_indb))
              ((mapi (fun pos_arg _ => tVar (make_name "j" pos_arg)) indices) ++ [tVar "y"])).

    Definition gen_rec_call_tm (pos_arg : nat) (arg_type : term) : option term :=
      let '(hd, iargs) := decompose_app arg_type in
      match hd with
      | tInd {|inductive_mind := s; inductive_ind := pos_indb' |} _
          => if eq_constant kname s
            then Some (tApp (tVar (make_name "F" pos_indb'))
                            (skipn nb_params iargs ++
                             [tVar (naming_arg pos_arg)]))
            else None
      | _ => None
      end.

    Fixpoint gen_rec_term_aux (pos_arg : nat) (args : context) : list term :=
      match args with
      | [] => []
      | arg::l =>
          let nv := tVar (naming_arg pos_arg) in
          let rc := gen_rec_term_aux (S pos_arg) l in
          match gen_rec_call_tm pos_arg (arg.(decl_type)) with
                      | None => nv :: rc
                      | Some t => nv :: t :: rc
                      end
      end.

    Definition gen_branch (pos_ctor : nat) (ctor : constructor_body) : branch term :=
      let acxt := rev (mapi (fun pos_arg _ => aname_arg pos_arg)
                      (ctor.(cstr_args))) in
      let tm := tApp (tVar (make_name_bin "f" pos_indb pos_ctor))
                    (gen_rec_term_aux 0 (rev ctor.(cstr_args)))
      in
      mk_branch acxt tm.

    Definition gen_branches : list (branch term) :=
      mapi gen_branch indb.(ind_ctors).

    Definition gen_match : term :=
      tCase (mk_case_info (mkInd kname pos_indb) nb_params Relevant)
            gen_prediate
            (tVar "x")
            gen_branches.

    Definition gen_Fix_block : def term :=
      mkdef _ (mkBindAnn (nNamed (make_name "F" pos_indb)) Relevant)
              (make_return_type kname mdecl pos_indb indices)
              (closure_indices tLambda indices
              (tLambda (mkBindAnn (nNamed "x") Relevant)
                      (make_ind kname params pos_indb indices)
                      gen_match))
              #|indices|.

  End GenFixBlock.

  Definition gen_Fix : term :=
    tFix (mapi gen_Fix_block mdecl.(ind_bodies)) pos_block.

  Definition gen_rec_term (indb : one_inductive_body) :=
    let lProp := (tSort sProp) in
     closure_param tLambda params
    (closure_type_preds kname mdecl tLambda lProp
    (closure_type_ctors kname mdecl tLambda
     gen_Fix)).

End GenRecTerm.