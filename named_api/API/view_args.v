From NamedAPI Require Import core.
From NamedAPI Require Import inductive_access inductive_store.
From NamedAPI Require Import context_access context_store.

Inductive VArg :=
| VArgIsInd     : forall (pos_indb : nat) (local :context)
                  (local_nuprams local_indices : list term), VArg
| VArgIsNested  : forall (xp : one_param_env) (pos_indb : nat) (local :context)
                  (inst_uparams inst_nuparams_indices : list term), VArg
| VArgIsFree    : forall (local : context) (hd : term), VArg.


Unset Guard Checking.

Section ViewVArgs.

Context (s : state).
Context (kname : kername).
Context (Ep : param_env).

#[local] Fixpoint view_vargs_aux (local : context) (matched : term) {struct matched} : VArg :=
  let (hd, iargs) := decompose_app matched in
  match hd with
  | tProd an A B     => if #|iargs| =? 0
                        then view_vargs_aux (local ,, vass an A) B
                        else VArgIsFree local matched
  | tLetIn an db A B => if #|iargs| =? 0
                        then view_vargs_aux (local ,, vdef an db A) B
                        else VArgIsFree local matched
  | tInd (mkInd kname_indb pos_indb) _ =>
    (* If it is the inductive *)
    if eqb kname kname_indb
    then let local_nuparams_indices := skipn (get_nb_uparams s kname) iargs in
         let local_nuparams := firstn (get_nb_nuparams s kname) local_nuparams_indices in
         let local_indices  := skipn  (get_nb_nuparams s kname) local_nuparams_indices in
         VArgIsInd pos_indb local local_nuparams local_indices
    (* 2.2 If it is nested *)
    else if length iargs =? 0 then VArgIsFree local matched
    else match find (fun x => eq_constant kname_indb x.(ep_kname)) Ep with
      | Some xp =>
        (* 2.2.1 get uparams and nuparams + indices *)
        let inst_uparams := firstn xp.(ep_nb_uparams) iargs in
        let inst_nuparams_indices := skipn xp.(ep_nb_uparams) iargs in
        VArgIsNested xp pos_indb local inst_uparams inst_nuparams_indices
      | None => VArgIsFree local matched
      end
  (* 3. Otherwise *)
  | _ => VArgIsFree local matched
  end.

#[using="All"]
Definition view_vargs (arg : term) : VArg := view_vargs_aux [] arg.




(* A view for strictly positive argguments *)
Inductive StrposArg :=
| StrposArgIsUparam : forall (pos_strpos_uparams : nat) (local :context), StrposArg
| StrposArgIsInd     : forall (pos_indb : nat) (local :context)
                  (local_nuprams local_indices : list term), StrposArg
| StrposArgIsNested  : forall (xp : one_param_env) (pos_indb : nat) (local :context)
                  (inst_uparams inst_nuparams_indices : list term), StrposArg
| StrposArgIsFree    : forall (local : context) (hd : term), StrposArg.

Definition find_bool {A} (p : A -> bool) (l : list A) : nat * bool :=
let fix aux n l :=
  match l with
  | [] => (n, false)
  | h::t => if p h then (n, true) else aux (S n) t
  end in
  aux 0 l.

Context (key_uparams : keys).

Definition view_strpos_args (matched : term) : StrposArg :=
  match view_vargs matched with
  | VArgIsInd pos_indb loc local_nuparams local_indices =>
      StrposArgIsInd pos_indb loc local_nuparams local_indices
  | VArgIsNested xp pos_indb loc local_uparams local_nuparams_indices =>
      StrposArgIsNested xp pos_indb loc local_uparams local_nuparams_indices
  | VArgIsFree loc m =>
      match m with
      | tRel n => match find_bool (fun k => check_pos s k n) key_uparams with
                  | (pos_strpos_uparams, true) => StrposArgIsUparam pos_strpos_uparams loc
                  | _ => StrposArgIsFree loc m
                  end
      | _ => StrposArgIsFree loc m
      end
  end.

End ViewVArgs.