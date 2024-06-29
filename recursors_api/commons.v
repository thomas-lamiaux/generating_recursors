From MetaCoq.Template Require Import All.

(* Require Import naming. *)

Require Import List.
Import ListNotations.

From MetaCoq Require Import BasePrelude.

(* 1. Interface *)

(* Interface *)
Record preprocess_mutual_inductive_body : Type := mk_mdecl
  { (* The inductive type being considered *)
    pmb_kname     : kername ;
    pmb_pos_idecl : nat ;
    (* uniform parameters *)
    pmb_uparams    : context ;
    pmb_nb_uparams : nat ;
    (* non uniform parameters *)
    pmb_nuparams    : context;
    pmb_nb_nuparams : nat;
    (* rest inductive *)
    pmb_ind_bodies : list one_inductive_body;
  }.


(* Output Universe *)
Record output_univ : Type := mk_output_univ
  { out_univ  : term;
    out_relev : relevance
  }.


(* For parametricity *)
Record one_env_param : Type := mk_one_env_param
 { ep_kname : kername ;
   ep_body : mutual_inductive_body ;
   ep_pkname : kername ;
   ep_tkname : kername;
}.

Definition env_param := list one_env_param.


(* 2. Aux functions *)
Definition isSome {A} (x : option A) : bool :=
  match x with
  | None => false
  | Some _ => true
  end.

(* Definition fold_right_i {A B} (f : nat -> B -> A -> A) (a0 : A) (l : list B) : A :=
  let fix fold_right_i_aux f a0 l (i : nat) : A :=
    match l with
    | [] => a0
    | h :: q => f i h (fold_right_i_aux f a0 q (S i))
    end
  in fold_right_i_aux f a0 l 0. *)

Definition fold_right_ie {A} (tp:nat -> A -> infolocal -> (infolocal -> term) -> term)
  (l:list A) (e:infolocal)  (t : infolocal -> term) : term :=
  let fix aux l e n t : term :=
    match l with
    | [] => t e
    | a :: l => tp n a e (fun e => aux l e (S n) t)
  end in
  aux l e 0 t.


(* 3. Naming  *)
Definition make_name (s : ident) (n : nat) :=
  String.append s (string_of_nat n).

Definition make_name0 (s : ident) (n : nat) : ident :=
  match n with
  | 0 => s
  | S n => make_name s n
  end.

Definition make_name_bin (s : ident) (n m : nat) :=
  String.append s (String.append (string_of_nat n) (string_of_nat m)).

Definition get_ident (x : aname) : ident :=
  match x.(binder_name) with
  | nNamed s => s
  | _ => "Error"
  end.

Definition naming_pred    pos := make_name0 "P" pos.
(* Definition naming_uparam   pos := make_name0 "A" pos.
Definition naming_nuparam  pos := make_name0 "B" pos.
Definition naming_indice  pos := make_name "i" pos.
Definition naming_indice' pos := make_name "j" pos.
Definition naming_arg     pos := make_name "x" pos. *)



(* 4. To make terms *)
Section MakeTerms.

  Context (kname : kername).
  Context (pos_block : nat).
  Context (pos_ctor : nat).
  Context (e : infolocal).

  (* Builds: Ind A1 ... An B0 ... Bm i1 ... il *)
  Definition make_ind : term :=
    mkApps (tInd (mkInd kname pos_block) [])
            (  rels_of "uparams" e
            ++ rels_of "nuparams" e
            ++ rels_of "indices" e).

  (* Builds: P_i B0 ... Bm i1 ... il *)
  Definition make_pred nuparams indices : term :=
    mkApps (geti_info "preds" e (pos_block))
            (nuparams ++ indices).

  Definition make_predn indices : term :=
    make_pred (rels_of "nuparams" e) indices.

  (* Builds: P_i B0 ... Bm i1 ... il *)
  Definition make_predni : term :=
    make_pred (rels_of "nuparams" e) (rels_of "indices" e).

  (* Builds: Cst A1 ... An B0 ... Bm *)
  Definition make_cst : term :=
    mkApps (tConstruct (mkInd kname pos_block) pos_ctor [])
           (rels_of "uparams" e ++ rels_of "nuparams" e).

End MakeTerms.



(* 5. Different closure functions *)
Section ComputeClosure.

  Context (binder : aname -> term -> term -> term).

  Definition closure_params   (binder : aname -> term -> term -> term) := it_kptProd (Some "params").
  Definition closure_uparams  (binder : aname -> term -> term -> term) := it_kptProd (Some "uparams").
  Definition closure_nuparams (binder : aname -> term -> term -> term) := it_kptProd (Some "nuparams").
  Definition closure_indices  (binder : aname -> term -> term -> term) := it_kptProd (Some "indices").

  Definition iterate_binder {A} (s : string)
    (binder : aname -> term -> term -> term) (l : list A)
    (naming : nat -> A -> aname) (typing : nat -> A -> infolocal -> term)
     (e : infolocal) (next : infolocal -> term) : term :=
    fold_right_ie
      (fun n a e t => mktProd (Savelist s) (naming n a) e (typing n a e) t)
      l e next.

End ComputeClosure.