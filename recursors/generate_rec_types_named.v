From MetaCoq.Utils Require Import utils.
From MetaCoq.Utils Require Import MCString.
From MetaCoq.Template Require Import All.
From MetaCoq.Common Require Import Universes.

Import MCMonadNotation.

Require Import preliminary.
Require Import preprocess_debruijn_to_named.

(* Plan :
1. Convert DeBruijn mutual inductive type => fully named one
2. Generate the recursor
3. Convert the fully named recursor => DeBruijn one (done in test)*)

(* To do :
- Add indices in constructors
- Add nested                    *)

(* ############################
   ###      Generation      ###
   ############################ *)

(* 1. Closure by parameters *)
Definition gen_closure_param (params : context) (t : term) : term :=
  fold_right (fun param t' => tProd param.(decl_name) (param.(decl_type)) t')
  t (rev params).


(* 2. Closure by predicates *)

(* forall (P : forall i1 : t1 ... il : tl, Ind A1 ... An i1 ... il -> U), t  *)
Definition gen_closure_one_pred (name : kername) (pos_block : nat) (indb : one_inductive_body)
  (params : context) (U : term) (t : term) : term :=
  tProd {| binder_name := nNamed (make_pred "P" pos_block) ; binder_relevance := Relevant |}
    (* Closure indices : forall i1 : t1 ... il : tl,  *)
    (fold_right_i
      (fun i indice t' => tProd {| binder_name := nNamed (make_name ["i"] i);
                          binder_relevance := Relevant |} indice.(decl_type) t')
      (* Definition of Ind A1 ... An i1 ... il -> U  *)
      (tProd AnonRel
        (tApp (tInd {| inductive_mind := name; inductive_ind := pos_block |} [])
              (gen_list_param params ++ gen_list_indices indb.(ind_indices)))
        U)
      (rev indb.(ind_indices)))
  t.

Definition gen_closure_pred (name : kername) (mdecl : mutual_inductive_body)
  (U : term) (t : term) : term :=
  fold_right_i (fun i indb t => gen_closure_one_pred name i indb mdecl.(ind_params) U t)
  t mdecl.(ind_bodies).


(* 3. Closure constructors *)

(* Check if the type is one of the inductive block, if so adds a rec call *)
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

(* (forall x0 : t0, P x0, ..., xn : tn, P n, P (cst A0 ... Ak t0 ... tn) -> t *)
Definition gen_closure_one_ctor (params : context) (kname : kername) (pos_block : nat)
  (ctor : constructor_body) (pos_ctor : nat) (t : term) : term :=
  let ind := {|inductive_mind := kname; inductive_ind := pos_block |} in
  tProd AnonRel
    (* Closure args and rec call : forall x0 : t0, P x0, ..., xn : tn, P n,  *)
    (fold_right_i
      (fun i arg t' => tProd {| binder_name := nNamed (make_name ["x"] i);
       binder_relevance := Relevant |} arg.(decl_type) (gen_rec_call kname i arg.(decl_type) t'))
      (* Definition of P (cst A0 ... Ak x0 ... xn) *)
      (tApp (tVar (make_pred "P" pos_block))
            [tApp (tConstruct ind pos_ctor [])
                  (gen_list_param params ++ gen_list_args ctor.(cstr_args)  )])
      ctor.(cstr_args))
    t.

(* Compute the closure by all the ctors *)
Definition gen_closure_ctors (params : context) (kname : kername) (mdecl : mutual_inductive_body)
  (t : term) : term :=
  let all_ctors := gather_ctors mdecl in
  fold_right
    (fun ijctor t' => let '(pos_block, pos_ctor,ctor) := ijctor in
                      gen_closure_one_ctor params kname pos_block ctor pos_ctor t')
    t all_ctors.


(* 4. Output *)
(* forall i0 : t0, ... il : tl, forall (x : Ind A0 ... An i0 ... il),  P i0 ... il x *)
Definition gen_output (params : context) (indices : context) (kname : kername)
  (pos_block : nat) : term :=
  (* Closure indices : forall i0 : t0, ... il : tl,  *)
  fold_right_i
    (fun i indice t' => tProd {| binder_name := nNamed (make_name ["i"] i);
                        binder_relevance := Relevant |} indice.(decl_type) t')
    (* Definition of forall (x : Ind A0 ... An i0 ... il),  P i0 ... il x  *)
    (tProd {| binder_name := nNamed "x"; binder_relevance := Relevant |}
          (tApp (tInd {|inductive_mind := kname; inductive_ind := pos_block |} [])
                ( gen_list_param params ++ gen_list_indices indices ))
          (tApp (tVar (make_pred "P" pos_block))
                (gen_list_indices indices ++ [tVar "x"])))
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

