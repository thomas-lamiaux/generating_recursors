From NamedAPI Require Import core.
From NamedAPI Require Import inductive_access inductive_store.
From NamedAPI Require Import context_access context_store.

Definition find_bool {A} (p : A -> bool) (l : list A) : nat * bool :=
let fix aux n l :=
  match l with
  | [] => (n, false)
  | h::t => if p h then (n, true) else aux (S n) t
  end in
  aux 0 l.



Unset Guard Checking.

Section ViewArgs.

Context (s : state).
Context (kname : kername).
Context (Ep : param_env).

(*

###############################
###    1. View Arguments    ###
###############################

*)

(* 1.1 View for arguments where inductive hasn't been subsituted *)
Inductive VArg :=
| VArgIsInd     : forall (pos_indb : nat) (local :context)
                  (local_nuprams local_indices : list term), VArg
| VArgIsNested  : forall (xp : one_param_env) (pos_indb : nat) (local :context)
                  (inst_uparams inst_nuparams_indices : list term), VArg
| VArgIsFree    : forall (local : context) (hd : term) (iargs : list term), VArg.


(* Set to [] is the inductive have been substituted for tInd *)
Context (key_inds : keys).


#[local] Fixpoint view_args_aux (local : context) (matched : term) {struct matched} : VArg :=
  let (hd, iargs) := decompose_app matched in
  match hd with
  | tProd an A B     => if #|iargs| =? 0
                        then view_args_aux (local ,, vass an A) B
                        else VArgIsFree local hd iargs
  | tLetIn an db A B => if #|iargs| =? 0
                        then view_args_aux (local ,, vdef an db A) B
                        else VArgIsFree local hd iargs
  (* If it is the inductive *)
  | tRel pos =>
      match find_bool (fun k => check_pos s k pos) key_inds with
        | (pos_strpos_uparams, true) =>
            let local_nuparams_indices := skipn (get_nb_uparams s kname) iargs in
            let local_nuparams := firstn (get_nb_nuparams s kname) local_nuparams_indices in
            let local_indices  := skipn  (get_nb_nuparams s kname) local_nuparams_indices in
            VArgIsInd pos local local_nuparams local_indices
        | _ => VArgIsFree local hd iargs
        end
  (* If it is nested *)
  | tInd (mkInd kname_indb pos_indb) _ =>
    (* If it is the inductive *)
    if eqb kname kname_indb
    then let local_nuparams_indices := skipn (get_nb_uparams s kname) iargs in
         let local_nuparams := firstn (get_nb_nuparams s kname) local_nuparams_indices in
         let local_indices  := skipn  (get_nb_nuparams s kname) local_nuparams_indices in
         VArgIsInd pos_indb local local_nuparams local_indices
    (* 2.2 If it is nested *)
    else if length iargs =? 0 then VArgIsFree local hd iargs
    else match find (fun x => eq_constant kname_indb x.(ep_kname)) Ep with
      | Some xp =>
        (* 2.2.1 get uparams and nuparams + indices *)
        let inst_uparams := firstn xp.(ep_nb_uparams) iargs in
        let inst_nuparams_indices := skipn xp.(ep_nb_uparams) iargs in
        VArgIsNested xp pos_indb local inst_uparams inst_nuparams_indices
      | None => VArgIsFree local hd iargs
      end
  (* 3. Otherwise *)
  | _ => VArgIsFree local hd iargs
  end.

#[using="All"]
Definition view_args (arg : term) : VArg := view_args_aux [] arg.


(*

DOES NOT WORK !!!

################################
### 2. View UPArg Arguments ###
################################

*)

(* A view for strictly positive argguments *)
Inductive UPArg :=
| UPArgIsUparam : forall (pos_strpos_uparams : nat) (local : context) (iargs : list term), UPArg
| UPArgIsInd     : forall (pos_indb : nat) (local :context)
                  (local_nuprams local_indices : list term), UPArg
| UPArgIsNested  : forall (xp : one_param_env) (pos_indb : nat) (local :context)
                  (inst_uparams inst_nuparams_indices : list term), UPArg
| UPArgIsFree    : forall (local : context) (hd : term) (iargs : list term) , UPArg.

Context (key_uparams : keys).

Definition view_uparams_args (matched : term) : UPArg :=
  match view_args matched with
  | VArgIsInd pos_indb loc local_nuparams local_indices =>
      UPArgIsInd pos_indb loc local_nuparams local_indices
  | VArgIsNested xp pos_indb loc local_uparams local_nuparams_indices =>
      UPArgIsNested xp pos_indb loc local_uparams local_nuparams_indices
  | VArgIsFree loc hd iargs =>
      match hd with
      | tRel pos => match find_bool (fun k => check_pos s k pos) key_uparams with
                  | (pos_uparams, true) => UPArgIsUparam pos_uparams loc iargs
                  | _ => UPArgIsFree loc hd iargs
                  end
      | _ => UPArgIsFree loc hd iargs
      end
  end.

End ViewArgs.