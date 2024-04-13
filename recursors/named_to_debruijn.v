From MetaCoq.Template Require Import All.

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
Fixpoint named_to_debruijn (fuel : nat) (u : term) :=
  match fuel with
  | 0 => u
  | S n =>
    match u with
    | tProd na A B =>
      match na.(binder_name) with
      | nNamed s =>
          tProd na (named_to_debruijn n A)
                    (named_to_debruijn n (subst_tVar s 0 B))
      | _ => u
      end
    | _ => u
    end
  end.