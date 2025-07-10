From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.

From PluginNestedElim Require Import test_functions.

Unset Elimination Schemes.
Unset MetaRocq Strict Unquote Universe Mode.


(* There are two functions:
- generate_sparse_parametricty : ∀ {A : Type}, param_env → sort → A → TemplateMonad unit that given
  - a list of information about types used for nesting, like strictly uniform parameters,
    sparse parametricty and local fundamental lemma for nested case
  - the return sort
  - an inductive type

  Generates the sparse parametrictiy and the local fundamental lemma

- generate_elim ! ∀ {A : Type}, param_env → ident → sort → A → TemplateMonad unit that given:
  - a list of information about types used for nesting, like strictly uniform parameters,
    sparse parametricty and local fundamental lemma for nested case
  - a name
  - the return sort
  - an indictive type

  Generates the eliminator for the nested inductive type
*)


(* Example 1: RoseTree *)
Inductive RoseTree A : Type :=
| RTleaf (a : A) : RoseTree A
| RTnode (l : list (RoseTree A)) : RoseTree A.


(* generate the sparse parametricity and the local fundamental theorem *)
MetaRocq Run (generate_sparse_parametricty [] sProp list).

Print listₛ.
Print lfl_listₛ.

(* Compute and add the date to the environment *)
MetaRocq Run (get_paramEp list []).


(* generate the nested eliminator *)
MetaRocq Run (generate_elim [kmp_list] "RoseTree_elim" sProp RoseTree).

Check RoseTree_elim.
Print RoseTree_elim.




(* Example 2: typing *)
Inductive term : Type :=
| tCase : term -> list term -> term.

Inductive All (A : Type) (P : A -> Prop) : list A -> Prop :=
| All_nil : All A P []
| All_cons a l : P a -> All A P l -> All A P (a::l).

Inductive typing : term -> term -> Prop :=
| typing_tCase (discr ind : term) (branches : list term) (return_type : term) :
          typing discr ind -> All term (fun a => typing a return_type) branches ->
          typing (tCase discr branches) return_type.


(* generate the sparse parametricity and the local fundamental theorem *)
MetaRocq Run (generate_sparse_parametricty [kmp_list] sProp All).

Print Allₛ.
Print lfl_Allₛ.

(* It needs to know the strictly postive uniform parameters of list
   to compute striclty postive uniform parameters for All *)
MetaRocq Run (get_paramEp ( @All ) [kmp_list]).

(* generate the nested eliminator *)
MetaRocq Run (generate_elim [kmp_list; kmp_All] "typing_elim" sProp typing).

Check typing_elim.
Print typing_elim.
