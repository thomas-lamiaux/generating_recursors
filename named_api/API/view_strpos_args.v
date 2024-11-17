From NamedAPI Require Import core.
From NamedAPI Require Import inductive_access inductive_store.
From NamedAPI Require Import context_access context_store.

Inductive strpos_arg :=
| ArgIsStrposParam : forall (pos_strpos_uparams : nat) (local :context), strpos_arg
| ArgIsInd     : forall (pos_indb : nat) (local :context)
                  (local_nuprams local_indices : list term), strpos_arg
| ArgIsNested  : forall (xp : one_param_env) (pos_indb : nat) (local :context)
                  (inst_uparams inst_nuparams_indices : list term), strpos_arg
| ArgIsFree : term -> strpos_arg.

Definition find_bool {A} (p : A -> bool) (l : list A) : nat * bool :=
let fix aux n l :=
  match l with
  | [] => (n, false)
  | h::t => if p h then (n, true) else aux (S n) t
  end in
  aux 0 l.

(* 2. Generates rec call for inductive *)
Unset Guard Checking.

Section MkRecCall.

Context (s : state).
Context (kname : kername).
Context (Ep : param_env).
Context (key_uparams : keys).

#[local] Fixpoint view_strpos_args_aux (local : context) (saved matched : term) {struct matched} : strpos_arg :=
  let (hd, iargs) := decompose_app matched in
  match hd with
  | tProd an A B     => if #|iargs| =? 0
                        then view_strpos_args_aux (local ,, vass an A) saved B
                        else ArgIsFree saved
  | tLetIn an db A B => if #|iargs| =? 0
                        then view_strpos_args_aux (local ,, vdef an db A) saved B
                        else ArgIsFree saved
  | tRel n =>
  | tInd (mkInd kname_indb pos_indb) _ =>
    (* If it is the inductive *)
    if eqb kname kname_indb
    then let local_nuparams_indices := skipn (get_nb_uparams s kname) iargs in
         let local_nuparams := firstn (get_nb_nuparams s kname) local_nuparams_indices in
         let local_indices  := skipn  (get_nb_nuparams s kname) local_nuparams_indices in
         ArgIsInd pos_indb local local_nuparams local_indices
    (* 2.2 If it is nested *)
    else if length iargs =? 0 then ArgIsFree saved
    else match find (fun x => eq_constant kname_indb x.(ep_kname)) Ep with
      | Some xp =>
        (* 2.2.1 get uparams and nuparams + indices *)
        let inst_uparams := firstn xp.(ep_nb_uparams) iargs in
        let inst_nuparams_indices := skipn xp.(ep_nb_uparams) iargs in
        ArgIsNested xp pos_indb local inst_uparams inst_nuparams_indices
      | None => ArgIsFree saved
      end
  (* 3. Otherwise *)
  | _ => ArgIsFree saved
  end.

#[using="All"]
Definition view_strpos_args (arg : term) : strpos_arg :=
  view_strpos_args_aux [] arg arg.


End MkRecCall.

