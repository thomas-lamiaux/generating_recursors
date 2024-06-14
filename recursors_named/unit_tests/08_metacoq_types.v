From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import All.

Require Import unit_tests.
Require Import nesting_param.

Inductive red1_test (Γ : context) : term -> term -> Type :=
| abs_red_r na M M' N : red1_test (Γ ,, vass na N) M M' -> red1_test Γ (tLambda na N M) (tLambda na N M').

Print red1_test_ind.

(*
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
*)

Redirect "recursors_named/tests/08_01_red1_test_custom" MetaCoq Run (print_rec "red1_test").
Redirect "recursors_named/tests/08_01_red1_test_gen"  MetaCoq Run (gen_rec E <% red1_test %>).

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