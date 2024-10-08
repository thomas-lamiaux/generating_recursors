From RecAPI Require Import api_debruijn.

(* Files contains
1. Programming interface
2. Namming fonctions
3. Make functions
*)


(* 1. Interface *)

(* Output Universe *)
Record output_univ : Type := mk_output_univ
  { out_univ  : term;
    out_relev : relevance
  }.


(* For parametricity *)
Record one_env_param : Type := mk_one_env_param
 { ep_kname : kername ;
   ep_nb_uparams : nat ;
   ep_strpos_uparams : list bool ;
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

Definition naming_pred : nat -> ident :=
  fun pos => make_name0 "P" pos.


(* 3. To make terms *)

(* Builds: P_i B0 ... Bm i1 ... il *)
Definition make_pred : nat -> list term -> list term -> info -> term :=
  fun pos_block nuparams indices e =>
  mkApps (geti_term "preds" pos_block e) (nuparams ++ indices).

Definition make_predn : nat -> list term -> info -> term :=
  fun pos_block indices e => make_pred pos_block (get_term "nuparams" e) indices e.

(* Builds: P_i B0 ... Bm i1 ... il *)
Definition make_predni : nat -> info -> term :=
  fun pos_block e => make_pred pos_block (get_term "nuparams" e) (get_term "indices" e) e.