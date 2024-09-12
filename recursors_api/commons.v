From RecAPI Require Import api_debruijn.

(* Files contains
1. Programming interface
2. Namming fonctions
3. Make functions
4. Closure functions
*)


(* 1. Interface *)

(* Interface *)
Record preprocess_mutual_inductive_body : Type := mk_mdecl
  { (* The inductive type being considered *)
    pmb_kname     : kername ;
    pmb_pos_indb : nat ;
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

Definition relev_sort (U : term) : relevance :=
  match U with
  | tSort sSProp => Irrelevant
  | _ => Relevant
  end.



(* 2. Naming *)
From MetaCoq Require Import MCString.

Open Scope bs_scope.

Definition make_name : ident -> nat -> ident :=
  fun s n => (s ++ (string_of_nat n)).

Definition make_name0 : ident -> nat -> ident :=
  fun s n => match n with
  | 0 => s
  | S n => make_name s n
  end.

Definition make_name_bin : ident -> nat -> nat -> ident :=
  fun s n m => s ++ (string_of_nat n) ++ (string_of_nat m).

Definition get_ident : aname -> ident :=
  fun x => match x.(binder_name) with
  | nNamed s => s
  | _ => "ERROR"
  end.

Definition naming_pred : nat -> ident :=
  fun pos => make_name0 "P" pos.
(*
Definition naming_uparam  pos := make_name0 "A" pos.
Definition naming_nuparam pos := make_name0 "B" pos.
Definition naming_indice  pos := make_name "i" pos.
Definition naming_indice' pos := make_name "j" pos.
Definition naming_arg     pos := make_name "x" pos. *)



(* 3. To make terms *)
Section MakeTerms.

  Context (kname : kername).
  Context (pos_block : nat).
  Context (pos_ctor  : nat).

  (* Builds: Ind A1 ... An B0 ... Bm i1 ... il *)
  Definition make_ind : info -> term :=
    fun e => mkApps (tInd (mkInd kname pos_block) [])
                    (  get_term "uparams"  e
                    ++ get_term "nuparams" e
                    ++ get_term "indices"  e).

  (* Builds: P_i B0 ... Bm i1 ... il *)
  Definition make_pred : list term -> list term -> info -> term :=
    fun nuparams indices e =>
    mkApps (geti_term "preds" pos_block e) (nuparams ++ indices).

  Definition make_predn : list term -> info -> term :=
    fun indices e => make_pred (get_term "nuparams" e) indices e.

  (* Builds: P_i B0 ... Bm i1 ... il *)
  Definition make_predni : info -> term :=
    fun e => make_pred (get_term "nuparams" e) (get_term "indices" e) e.

  (* Builds: Cst A1 ... An B0 ... Bm *)
  Definition make_cst : info -> term :=
    fun e => mkApps (tConstruct (mkInd kname pos_block) pos_ctor [])
                    (get_term "uparams" e ++ get_term "nuparams" e).

End MakeTerms.

(* 4. Different closure functions *)
Section ComputeClosure.

  Context (binder : aname -> term -> term -> term).

  Definition closure_params   := fun cxt => it_kp_binder binder cxt (Some "params").
  Definition closure_uparams  := fun cxt => it_kp_binder binder cxt (Some "uparams").
  Definition closure_nuparams := fun cxt => it_kp_binder binder cxt (Some "nuparams").
  Definition closure_indices  := fun cxt => it_kp_binder binder cxt (Some "indices").

  Definition iterate_binder {A} (s : ident) (l : list A)
    (naming : nat -> A -> aname) (typing : nat -> A -> info -> term) :
    info -> (info -> term) -> term :=
    fold_right_ie
      (fun n a e t => mk_binder binder (naming n a) (typing n a e) (Some s) e t)
      l.

End ComputeClosure.
