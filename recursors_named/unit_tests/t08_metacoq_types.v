From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import All.

Require Import unit_tests.
Require Import nesting_param.

Inductive red1 (Σ : global_env) (Γ : context) : term -> term -> Type :=
(** Reductions *)
(** Beta *)
| red_beta na t b a l :
    red1 Σ Γ (tApp (tLambda na t b) (a :: l)) (mkApps (subst10 a b) l)

(** Let *)
| red_zeta na b t b' :
    red1 Σ Γ (tLetIn na b t b') (subst10 b b')

| red_rel i body :
    option_map decl_body (nth_error Γ i) = Some (Some body) ->
    red1 Σ Γ (tRel i) (lift0 (S i) body)

(** Case *)
| red_iota ci mdecl idecl cdecl c u args p brs br :
    nth_error brs c = Some br ->
    (* In the compact representation, reduction must fetch the
       global declaration of the constructor to gather the let-bindings
       in its argument context. Implementations can be more clever
       in the common case where no let-binding appears to avoid this. *)
    declared_constructor Σ (ci.(ci_ind), c) mdecl idecl cdecl ->
    let bctx := case_branch_context ci.(ci_ind) mdecl cdecl p br in
    #|args| = (ci.(ci_npar) + context_assumptions bctx)%nat ->
    red1 Σ Γ (tCase ci p (mkApps (tConstruct ci.(ci_ind) c u) args) brs)
         (iota_red ci.(ci_npar) args bctx br)

(** Fix unfolding, with guard *)
| red_fix mfix idx args narg fn :
    unfold_fix mfix idx = Some (narg, fn) ->
    is_constructor narg args = true ->
    red1 Σ Γ (tApp (tFix mfix idx) args) (mkApps fn args)

(** CoFix-case unfolding *)
| red_cofix_case ip p mfix idx args narg fn brs :
    unfold_cofix mfix idx = Some (narg, fn) ->
    red1 Σ Γ (tCase ip p (mkApps (tCoFix mfix idx) args) brs)
         (tCase ip p (mkApps fn args) brs)

(** CoFix-proj unfolding *)
| red_cofix_proj p mfix idx args narg fn :
    unfold_cofix mfix idx = Some (narg, fn) ->
    red1 Σ Γ (tProj p (mkApps (tCoFix mfix idx) args))
         (tProj p (mkApps fn args))

(** Constant unfolding *)
| red_delta c decl body (isdecl : declared_constant Σ c decl) u :
    decl.(cst_body) = Some body ->
    red1 Σ Γ (tConst c u) (subst_instance u body)

(** Proj *)
| red_proj p u args arg:
    nth_error args (p.(proj_npars) + p.(proj_arg)) = Some arg ->
    red1 Σ Γ (tProj p (mkApps (tConstruct p.(proj_ind) 0 u) args)) arg


| abs_red_l na M M' N : red1 Σ Γ M M' -> red1 Σ Γ (tLambda na M N) (tLambda na M' N)
| abs_red_r na M M' N : red1 Σ (Γ ,, vass na N) M M' -> red1 Σ Γ (tLambda na N M) (tLambda na N M')

| letin_red_def na b t b' r : red1 Σ Γ b r -> red1 Σ Γ (tLetIn na b t b') (tLetIn na r t b')
| letin_red_ty na b t b' r : red1 Σ Γ t r -> red1 Σ Γ (tLetIn na b t b') (tLetIn na b r b')
| letin_red_body na b t b' r : red1 Σ (Γ ,, vdef na b t) b' r -> red1 Σ Γ (tLetIn na b t b') (tLetIn na b t r)

| case_red_pred_param ind params params' puinst pcontext preturn c brs :
    OnOne2 (red1 Σ Γ) params params' ->
    red1 Σ Γ (tCase ind (mk_predicate puinst params pcontext preturn) c brs)
             (tCase ind (mk_predicate puinst params' pcontext preturn) c brs)

| case_red_pred_return ind mdecl idecl (isdecl : declared_inductive Σ ind.(ci_ind) mdecl idecl)
                       params puinst pcontext preturn preturn' c brs :
    let p := {| pparams := params; puinst := puinst; pcontext := pcontext; preturn := preturn |} in
    let p' := {| pparams := params; puinst := puinst; pcontext := pcontext; preturn := preturn' |} in
    red1 Σ (Γ ,,, case_predicate_context ind.(ci_ind) mdecl idecl p) preturn preturn' ->
    red1 Σ Γ (tCase ind p c brs)
             (tCase ind p' c brs)

| case_red_discr ind p c c' brs : red1 Σ Γ c c' -> red1 Σ Γ (tCase ind p c brs) (tCase ind p c' brs)

| case_red_brs ind mdecl idecl (isdecl : declared_inductive Σ ind.(ci_ind) mdecl idecl) p c brs brs' :
    OnOne2All (fun brctx br br' =>
      on_Trel_eq (red1 Σ (Γ ,,, brctx)) bbody bcontext br br')
      (case_branches_contexts ind.(ci_ind) mdecl idecl p brs) brs brs' ->
    red1 Σ Γ (tCase ind p c brs) (tCase ind p c brs')

| proj_red p c c' : red1 Σ Γ c c' -> red1 Σ Γ (tProj p c) (tProj p c')

| app_red_l M1 N1 M2 : red1 Σ Γ M1 N1 -> red1 Σ Γ (tApp M1 M2) (mkApps N1 M2)
| app_red_r M2 N2 M1 : OnOne2 (red1 Σ Γ) M2 N2 -> red1 Σ Γ (tApp M1 M2) (tApp M1 N2)

| prod_red_l na M1 M2 N1 : red1 Σ Γ M1 N1 -> red1 Σ Γ (tProd na M1 M2) (tProd na N1 M2)
| prod_red_r na M2 N2 M1 : red1 Σ (Γ ,, vass na M1) M2 N2 ->
                               red1 Σ Γ (tProd na M1 M2) (tProd na M1 N2)

| evar_red ev l l' : OnOne2 (red1 Σ Γ) l l' -> red1 Σ Γ (tEvar ev l) (tEvar ev l')

| cast_red_l M1 k M2 N1 : red1 Σ Γ M1 N1 -> red1 Σ Γ (tCast M1 k M2) (tCast N1 k M2)
| cast_red_r M2 k N2 M1 : red1 Σ Γ M2 N2 -> red1 Σ Γ (tCast M1 k M2) (tCast M1 k N2)
| cast_red M1 k M2 : red1 Σ Γ (tCast M1 k M2) M1

| fix_red_ty mfix0 mfix1 idx :
    OnOne2 (on_Trel_eq (red1 Σ Γ) dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix1 ->
    red1 Σ Γ (tFix mfix0 idx) (tFix mfix1 idx)

| fix_red_body mfix0 mfix1 idx :
    OnOne2 (on_Trel_eq (red1 Σ (Γ ,,, fix_context mfix0)) dbody (fun x => (dname x, dtype x, rarg x)))
      mfix0 mfix1 ->
    red1 Σ Γ (tFix mfix0 idx) (tFix mfix1 idx)

| cofix_red_ty mfix0 mfix1 idx :
    OnOne2 (on_Trel_eq (red1 Σ Γ) dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix1 ->
    red1 Σ Γ (tCoFix mfix0 idx) (tCoFix mfix1 idx)

| cofix_red_body mfix0 mfix1 idx :
    OnOne2 (on_Trel_eq (red1 Σ (Γ ,,, fix_context mfix0)) dbody (fun x => (dname x, dtype x, rarg x))) mfix0 mfix1 ->
    red1 Σ Γ (tCoFix mfix0 idx) (tCoFix mfix1 idx)

| array_red_val l v v' d ty :
    OnOne2 (fun t u => red1 Σ Γ t u) v v' ->
    red1 Σ Γ (tArray l v d ty) (tArray l v' d ty)

| array_red_def l v d d' ty :
    red1 Σ Γ d d' ->
    red1 Σ Γ (tArray l v d ty) (tArray l v d' ty)

| array_red_type l v d ty ty' :
    red1 Σ Γ ty ty' ->
    red1 Σ Γ (tArray l v d ty) (tArray l v d ty').

Redirect "recursors_named/tests/08_01_red1_custom" MetaCoq Run (print_rec "red1").
Redirect "recursors_named/tests/08_01_red1_gen"  MetaCoq Run (gen_rec E <% red1 %>).

(*
(* ################################################# *)
(* MetaCoq Examples                                   *)

Unset Elimination Schemes.

Definition term_ind := term_forall_list_ind.

Redirect "recursors_named/tests/08_02_term_custom" MetaCoq Run (print_rec "term").
Redirect "recursors_named/tests/08_02_term_gen"  MetaCoq Run (gen_rec E <% term %>).

Definition red1_ind := red1_ind_all.

(* Bugs: Issue with let in ?  *)
Redirect "recursors_named/tests/08_03_red1_custom" MetaCoq Run (print_rec "red1").
Redirect "recursors_named/tests/08_03_red1_gen"  MetaCoq Run (gen_rec E <% red1 %>).


(* Bugs : Issue with flags *)
(* From MetaCoq.Common Require Import config.
Variable (x : checker_flags).
Existing Instance x.
Redirect "recursors_named/tests/05_09_TemplateTyping_custom" MetaCoq Run (print_rec "typing_env").
Redirect "recursors_named/tests/05_09_TempalteTyping_gen"  MetaCoq Run (gen_rec E <% typing %>). *)

*)