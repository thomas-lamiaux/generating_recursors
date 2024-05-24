From MetaCoq.Utils Require Import utils.
From MetaCoq.Utils Require Import MCString.
From MetaCoq.Template Require Import All.

Require Import preliminary.
Require Import generate_types.

Section GenRecTerm.

  Context (kname  : kername).
  Context (pos_block : nat).
  Context (mdecl  : mutual_inductive_body).

  Definition params := mdecl.(ind_params).
  Definition nb_params := #|params|.

(* Print BasicAst.context_decl. *)


Definition gen_rec_call_tm (pos_arg : nat) (arg_type : term) : option term :=
  let '(hd, iargs) := decompose_app arg_type in
  match hd with
  | tInd {|inductive_mind := s; inductive_ind := pos_block |} _
      => if eq_constant kname s
        then Some (tApp (tVar (make_name0 "F" 0))
                         ( skipn nb_params iargs ++
                           [tVar (make_name "x" pos_arg)]))
        else None
  | _ => None
  end.

  Fixpoint gen_rec_term_aux (pos_arg : nat) (args : context) : list term :=
    match args with
    | [] => []
    | arg::l =>
        let nv := tVar (make_name "x" pos_arg) in
        let rc := gen_rec_term_aux (S pos_arg) l in
        match gen_rec_call_tm pos_arg (arg.(decl_type)) with
                    | None => nv :: rc
                    | Some t => nv :: t :: rc
                    end
    end.

  Definition gen_branch (pos_ctor : nat) (ctor : constructor_body) : branch term :=
    let acxt := mapi (fun pos_arg arg => mkBindAnn (nNamed (make_name "x" pos_arg)) Relevant)
                     ctor.(cstr_args) in
    let tm := tApp (tVar (make_name0 "f" pos_ctor))
                   (gen_rec_term_aux 0 (rev ctor.(cstr_args)))
    in
    mk_branch acxt tm.



  Definition gen_branches (indb : one_inductive_body) : list (branch term) :=
    mapi gen_branch indb.(ind_ctors).

  (* Definition *)
  Definition gen_match (indb : one_inductive_body) :=
    tCase (mk_case_info (mkInd kname 0) nb_params Relevant)
          (* ADD PARAMS in params of predicate *)
          (mk_predicate [] [] [(mkBindAnn (nNamed "y") Relevant)] (tApp (tVar "P") [tVar "y"]))
          (tVar "x")
          (gen_branches indb).

  Definition gen_Fix (indices : context) (next : term) : term :=
    tFix [mkdef _
                (mkBindAnn (nNamed "F") Relevant)
                (make_return_type kname mdecl 0 indices)
                (tLambda (mkBindAnn (nNamed "x") Relevant)
                         (tInd (mkInd kname 0) []) (* ADD PARAMS + INDICES *)
                         next)
                0
         ]
        0.

  Definition gen_output (indb : one_inductive_body) (indices : context) :=
    gen_Fix indices (gen_match indb).

  Definition gen_rec_term (indb : one_inductive_body) :=
    let lProp := (tSort sProp) in
    (* let mdecl := preprocessing_mind kname mdecl in *)
     closure_param tLambda mdecl.(ind_params)
    (closure_type_preds kname mdecl tLambda lProp
    (closure_type_ctors kname mdecl tLambda
    (gen_output indb indb.(ind_indices)))).

End GenRecTerm.