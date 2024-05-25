From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import All.
From MetaCoq.Utils Require Import MCString.

Require Import preliminary.

From Coq Require Import List.
Import ListNotations.

(* Replace a tVar by the corresponding tRel k, respect binders *)
Fixpoint subst_tVar (s : ident) (k : nat) (u : term) :=
  match u with
  | tVar s' => if String.eqb s s' then tRel k else tVar s'
  | tEvar ev args => tEvar ev (List.map (subst_tVar s k) args)
  | tLambda na T M => tLambda na (subst_tVar s k T) (subst_tVar s (S k) M)
  | tApp u v => mkApps (subst_tVar s k u) (List.map (subst_tVar s k) v)
  | tProd na A B => tProd na (subst_tVar s k A) (subst_tVar s (S k) B)
  | tCast c kind ty => tCast (subst_tVar s k c) kind (subst_tVar s k ty)
  | tLetIn na b ty b' => tLetIn na (subst_tVar s k b) (subst_tVar s k ty) (subst_tVar s (S k) b')
  | tCase ind p c brs =>
    let k' := List.length (pcontext p) + k in
    let p' := map_predicate id (subst_tVar s k) (subst_tVar s k') p in
    let brs' := map_branches_k (subst_tVar s) k brs in
    tCase ind p' (subst_tVar s k c) brs'
  | tProj p c => tProj p (subst_tVar s k c)
  | tFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (subst_tVar s k) (subst_tVar s k')) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (subst_tVar s k) (subst_tVar s k')) mfix in
    tCoFix mfix' idx
  | x => x
  end.

(* Convert a named term made of forall into one made of debruijn indices *)

Definition ntb_binder (f : nat -> term -> term) (n : nat)
  (binder : aname -> term -> term -> term) (an : aname) (A B : term) : term :=
  match an.(binder_name) with
  | nNamed s =>
      binder an (f n A) (f n (subst_tVar s 0 B))
  | _ => binder an (f n A) (f n B)
  end.

Definition ntb_aname_cxt (acxt : list aname) (t : term) : term :=
  fold_right_i (fun pos_na na t => subst_tVar na (#|acxt| - 1 - pos_na) t) t
            (map get_ident acxt).

(* Definition acxt : list aname :=
  (mkBindAnn (nNamed "x0") Relevant) ::
  (mkBindAnn (nNamed "x1") Relevant) ::
  (mkBindAnn (nNamed "x2") Relevant) :: [].

(* Compute (map get_ident acxt). *)

Definition th : term :=
  tApp (tVar "f0") [tVar "x0"; tApp (tVar "F") [tVar "x0"];
                    tVar "x1";
                    tVar "x2";
                    tApp (tVar "F") [tVar "x2"]]. *)

(* Definition th3 : term :=
  tApp (tVar "f0") [tVar "x1"].

Compute (ntb_aname_cxt acxt th).
Compute (subst_tVar "x0" 0 th). *)

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
    | tFix ((mkdef dna dty db0 na)::[]) idx =>
        let dty' := named_to_debruijn n dty in
        let db0' := named_to_debruijn n (subst_tVar (get_ident dna) 0 db0) in
        tFix (((mkdef _ dna dty' db0' na)::[])) idx
    | _ => u
    end
  end.