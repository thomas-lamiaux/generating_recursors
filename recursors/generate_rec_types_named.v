From MetaCoq.Utils Require Import utils.
From MetaCoq.Utils Require Import MCString.
From MetaCoq.Template Require Import All.
From MetaCoq.Common Require Import Universes.

Import MCMonadNotation.

Require Import named_to_debruijn.
Require Import preliminary.

(* Plan :
1. Convert DeBruijn mutual inductive type => fully named one
2. Generate the recursor
3. Convert the fully named recursor => DeBruijn one *)

(* To do :
- Add constructors
- Add indices in constructors
- Add nested                    *)

(* ############################
   ###         Lemma        ###
   ############################ *)

Definition AnonRel := {| binder_name := nAnon; binder_relevance := Relevant |}.

Fixpoint rel_list (shift : nat) (n : nat) : list term :=
  match n with
  | 0 => []
  | S n => (tRel (shift + n)) :: (rel_list (shift) n)
  end.

(* #################################
   ### DeBruinj Ind => Named Ind ###
   ################################# *)

(* Computes the list [tVar "A1", ..., tVar "Ak"]
   where A1, ... Ak are the parameters            *)
Definition gen_list_param (params : context) : list term :=
  map (fun param => tVar (get_ident param.(decl_name))) (rev params).

(* Replace the arguments for a constructor by tVar x1 ... tVar xn  *)
Fixpoint name_args_of_ctor_aux (name_cst : ident) (cxt : context) (pos_arg : nat)
  (l : list term) : context :=
  match cxt with
  | [] => []
  | decl::q =>
    (* let new_arg := tVar (make_name [name_cst; "_x"] pos_arg) in *)
    let new_arg := tVar (make_name ["x"] pos_arg) in
      {| decl_name := decl.(decl_name) ;
         decl_body := decl.(decl_body) ;
         decl_type := subst l 0 decl.(decl_type) |}
    :: (name_args_of_ctor_aux name_cst q (S pos_arg) (new_arg::l))
  end.

Definition name_args_of_ctor (name_cst : ident) (cxt : context) : context :=
  name_args_of_ctor_aux name_cst cxt 0 [].

(* Preprocess a mutual inductive types by modfiying indices and ctors :
   1. Replace (tRel i) representing inductive blocks by (tInd ...)
   2. Replace (tRel i) representing paramters by (tVar "Ai")
   3. Replace (tRel i) representing arguments of ctors by (tVar "Cst_xi") *)
Definition preprocessing_mind (kname : kername) (mdecl : mutual_inductive_body) : _ :=
  (* Shortcuts *)
  let nb_blocks := #|mdecl.(ind_bodies)| in
  let nb_params := mdecl.(ind_npars) in
  (* Replace [tRel (nb_blocks -1 + nb_params), ..., tRel (nb_params)] by tInd ... *)
  let Klist := inds kname [] mdecl.(ind_bodies) in
  let name_ind : context -> context := subst_context Klist nb_params in
  (* Replace [tRel (nb_params-1), ..., tRel (0)] by A0 ... Ak *)
  let namedParams := gen_list_param mdecl.(ind_params) in
  let name_param : context -> context := subst_context (rev namedParams) 0 in
  (* Preprocess ctors :
     1. name inductive types, 2. name parameters, 3. replace args  *)
  let process_ctor : constructor_body -> constructor_body :=
  fun ctor => let nargs1  := name_ind ctor.(cstr_args) in
              let nargs2  := name_param nargs1 in
              let nargs3  := name_args_of_ctor ctor.(cstr_name) (rev nargs2)
    (* let new_args := name_args_of_ctor ctor.(cstr_name)
    (rev (name_ind (name_param ctor.(cstr_args)))) *)
    in
    {| cstr_name    := ctor.(cstr_name) ;
       cstr_args    := nargs3 ;
       cstr_indices := ctor.(cstr_indices);
       cstr_type    := ctor.(cstr_type);
       cstr_arity   := ctor.(cstr_arity)
    |}
  in
  (* Preprocess inductive blocks :
     1. replace param in indices, 2. preprocess ctors *)
  let process_indb : one_inductive_body -> one_inductive_body :=
  fun indb =>
    {| ind_name      := indb.(ind_name) ;
       ind_indices   := name_param indb.(ind_indices) ; (* name param in indices*)
       ind_sort      := indb.(ind_sort) ;
       ind_type      := indb.(ind_type) ;
       ind_kelim     := indb.(ind_kelim) ;
       ind_ctors     := map process_ctor indb.(ind_ctors) ;
       ind_projs     := indb.(ind_projs) ;
       ind_relevance := indb.(ind_relevance) ;
    |}
  in
  modify_ind_bodies process_indb mdecl.

(* ############################
   ###      Generation      ###
   ############################ *)

(* 1. Closure by parameters *)
Definition gen_closure_param (params : context) (t : term) : term :=
  fold_right_i (fun i param t' => tProd param.(decl_name) (param.(decl_type)) t')
  t (rev params).

(* 2. Closure by predicates *)
(* Closure by indices is missing *)
Definition gen_closure_one_pred (name : kername) (pos_block : nat) (indb : one_inductive_body)
  (params : context) (U : term) (t : term) : term :=
  (* P : forall n1 ... nk, Ind A1 ... An n1 ... nk -> U *)
  tProd {| binder_name := nNamed (make_pred "P" pos_block) ; binder_relevance := Relevant |}
    (* Closure indices i1 ... ik, *)
    (fold_right_i
      (fun i indice t' => tProd {| binder_name := nNamed (make_name ["i"] i);
                          binder_relevance := Relevant |} indice.(decl_type) t')
      (* Definition of Ind A1 ... An n1 ... nk -> U  *)
      (tProd AnonRel
        (tApp (tInd {| inductive_mind := name; inductive_ind := pos_block |} [])
              (    gen_list_param params
                ++ make_list (fun i => tVar (make_name ["i"] i)) #|indb.(ind_indices)|))
        U)
      (rev indb.(ind_indices)))
  t.

Definition gen_closure_pred (name : kername) (mdecl : mutual_inductive_body)
  (U : term) (t : term) : term :=
  fold_right_i (fun i indb t => gen_closure_one_pred name i indb mdecl.(ind_params) U t)
  t mdecl.(ind_bodies).


(* 3. Closure constructors *)
(* To do :
   - deal with parameters
   - deal with indices     *)

Definition gen_rec_call (kname : kername)(pos_arg : nat)
  (arg_type : term) (t : term) : term :=
  let '(hd, iargs) := decompose_app arg_type in
  match hd with
  | tInd {|inductive_mind := s; inductive_ind := pos_block |} _
      => if eq_constant kname s
         then tProd AnonRel
                    (tApp (tVar (make_pred "P" pos_block))
                          [tVar (make_name ["x"] pos_arg)])
              t
         else t
  | _ => t
  end.

Definition gen_closure_one_ctor (params : context) (kname : kername) (pos_block : nat)
  (ctor : constructor_body) (pos_ctor : nat) (t : term) : term :=
  let ind := {|inductive_mind := kname; inductive_ind := pos_block |} in
  (* let namming_arg := fun i => make_name [ctor.(cstr_name); "_x"] i in *)
  let namming_arg := fun i => make_name ["x"] i in
  let tVar_arg := make_list (fun i => tVar (namming_arg i)) #|ctor.(cstr_args)| in
  tProd AnonRel
    (* Closure arguments *)
    (fold_right_i
      (fun i arg t' => tProd {| binder_name := nNamed (namming_arg i);
       binder_relevance := Relevant |} arg.(decl_type) (gen_rec_call kname i arg.(decl_type) t'))
      (tApp (tVar (make_pred "P" pos_block))
            [tApp (tConstruct ind pos_ctor [])
                  (gen_list_param params ++ tVar_arg)])
      ctor.(cstr_args))
    t.

Definition gen_closure_ctors (params : context) (kname : kername) (mdecl : mutual_inductive_body)
  (t : term) : term :=
  let all_ctors := gather_ctors mdecl in
  fold_right
    (fun ijctor t' => let '(pos_block, pos_ctor,ctor) := ijctor in
                      gen_closure_one_ctor params kname pos_block ctor pos_ctor t')
    t
    all_ctors.


(* 4. Output  *)
Definition gen_output (params : context) (indices : context) (kname : kername)
  (pos_block : nat) : term :=
  let tVar_indices := make_list (fun i => tVar (make_name ["i"] i)) #|indices| in
  (* Closure indices i0 ... ik *)
  fold_right_i
    (fun i indice t' => tProd {| binder_name := nNamed (make_name ["i"] i);
                        binder_relevance := Relevant |} indice.(decl_type) t')
    (* forall x : Ind A0 ... An i0 ... ik  *)
    (tProd {| binder_name := nNamed "x"; binder_relevance := Relevant |}
          (tApp (tInd {|inductive_mind := kname; inductive_ind := pos_block |} [])
                ( gen_list_param params ++ tVar_indices ))
          (tApp (tVar (make_pred "P" pos_block))
                (tVar_indices ++ [tVar "x"])))
    (rev indices).



(* Generation *)
Definition gen_rec_type (kname : kername) (pos_block : nat) (mdecl : mutual_inductive_body)
  (indb : one_inductive_body) : term :=
  let lProp := (tSort (Universe.of_levels (inl PropLevel.lProp))) in
  let mdecl := preprocessing_mind kname mdecl in
   gen_closure_param mdecl.(ind_params)
  (gen_closure_pred kname mdecl lProp
  (gen_closure_ctors mdecl.(ind_params) kname mdecl
  (gen_output mdecl.(ind_params) indb.(ind_indices) kname pos_block))).

