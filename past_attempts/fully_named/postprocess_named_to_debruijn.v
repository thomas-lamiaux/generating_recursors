From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.
From MetaRocq.Utils Require Import MCString.

From RecNamed Require Import commons.
From RecNamed Require Import naming.

(* Replace a tVar by the corresponding tRel k, respect binders *)
Fixpoint tVar_to_tRel (s : ident) (k : nat) (u : term) :=
  match u with
  | tVar s' => if String.eqb s s' then tRel k else tVar s'
  | tEvar ev args => tEvar ev (List.map (tVar_to_tRel s k) args)
  | tLambda na T M => tLambda na (tVar_to_tRel s k T) (tVar_to_tRel s (S k) M)
  | tApp u v => mkApps (tVar_to_tRel s k u) (List.map (tVar_to_tRel s k) v)
  | tProd na A B => tProd na (tVar_to_tRel s k A) (tVar_to_tRel s (S k) B)
  | tCast c kind ty => tCast (tVar_to_tRel s k c) kind (tVar_to_tRel s k ty)
  | tLetIn na b ty b' => tLetIn na (tVar_to_tRel s k b) (tVar_to_tRel s k ty) (tVar_to_tRel s (S k) b')
  | tCase ind p c brs =>
    let k' := List.length (pcontext p) + k in
    let p' := map_predicate id (tVar_to_tRel s k) (tVar_to_tRel s k') p in
    let brs' := map_branches_k (tVar_to_tRel s) k brs in
    tCase ind p' (tVar_to_tRel s k c) brs'
  | tProj p c => tProj p (tVar_to_tRel s k c)
  | tFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (tVar_to_tRel s k) (tVar_to_tRel s k')) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (tVar_to_tRel s k) (tVar_to_tRel s k')) mfix in
    tCoFix mfix' idx
  | x => x
  end.

(* Convert a named term made of forall into one made of debruijn indices *)

Definition ntb_binder (f : nat -> term -> term) (n : nat)
  (binder : aname -> term -> term -> term) (an : aname) (A B : term) : term :=
  match an.(binder_name) with
  | nNamed s =>
      binder an (f n A) (f n (tVar_to_tRel s 0 B))
  | _ => binder an (f n A) (f n B)
  end.

  Definition ntb_letin (f : nat -> term -> term) (n : nat) (an : aname) (A B C : term) : term :=
  match an.(binder_name) with
  | nNamed s =>
      tLetIn an (f n A) (f n B) (f n (tVar_to_tRel s 0 C))
  | _ => tLetIn an (f n A) (f n B) (f n C)
  end.

Definition ntb_aname_cxt (acxt : list aname) (t : term) : term :=
  fold_right_i (fun pos_na na t => tVar_to_tRel na (#|acxt| - 1 - pos_na) t) t
            (map get_ident acxt).

Fixpoint named_to_debruijn (fuel : nat) (u : term) :=
  match fuel with
  | 0 => u
  | S n =>
    match u with
    | tLambda an T M => ntb_binder named_to_debruijn n tLambda an T M
    | tApp u v => mkApps (named_to_debruijn n u) (List.map (named_to_debruijn n) v)
    | tProd an A B => ntb_binder named_to_debruijn n tProd an A B
    | tCase ind (mk_predicate u ppar pcxt prt) c brs =>
        let prt' := named_to_debruijn n (ntb_aname_cxt (rev pcxt) prt) in
        let c'   := named_to_debruijn n c in
        let brs' := map (fun br => match br with
                    | mk_branch acxt t =>
                        mk_branch acxt (named_to_debruijn n (ntb_aname_cxt (rev acxt) t))
                    end) brs in
        tCase ind (mk_predicate u ppar pcxt prt') c' brs'
    | tFix mfix idx =>
        let anameFix := map dname mfix in
        let de := map_def (named_to_debruijn n)
          (fun x => named_to_debruijn n (ntb_aname_cxt anameFix x)) in
        tFix (map de mfix) idx
    | tLetIn an b ty b' => ntb_letin named_to_debruijn n an b ty b'
    | _ => u
    end
  end.