From Coq Require Export List.
Export ListNotations.

From MetaCoq.Utils Require Export utils.
From MetaCoq.Template Require Export All.


(* Aux Functions *)
Definition isSome {A} : option A -> bool :=
  fun x => match x with Some _ => true | _ => false end.


Definition fold_right_i {A B} : (nat -> B -> A -> A) -> A -> list B -> A :=
  fun f a =>
  let fix aux n l : A :=
    match l with
    | [] => a
    | b :: l => f n b (aux (S n) l)
  end in
  aux 0.

Definition fold_left_i {A B} : (nat -> A -> B -> A) -> list B -> A -> A :=
  fun f =>
  let fix aux n l a0 : A :=
    match l with
    | [] => a0
    | b :: l => aux (S n) l (f n a0 b)
  end in
  aux 0.

Definition find_errori {A} (p : A -> bool) (l : list A) (default : A) : nat * A :=
  let fix aux n l : nat * A :=
    match l with
    | [] => (n , default)
    | a::l => if p a then (n, a) else aux (S n) l
    end
  in aux 0 l.

(*

This interface is inspired from work by Weituo DAI, and Yannick Forester

#############################
###      Constrains       ###
#############################

1. Be able to refer to variables indirectly by names
2. Keep track of the old variables for weakening
3. Be able to replace variables by term on the fly


#############################
###   Backend interface   ###
#############################


(* 0. Datastructre and General Purposed Functions *)
- info_decl : Type
- info : Type
- init_info : info

(* 1. General Purposed Functions *)
- fold_right_ie : {A} (nat -> A -> info -> (info -> term) -> term)
    (list A) -> info -> (info -> term) -> term
- fold_left_ie : {A} (nat -> A -> info -> (info -> term) -> term)
    (list A) -> info -> (info -> term) -> term
- add_idecl : info_decl -> info -> info
- add_pdecl : info_pdecl -> info -> info

(* 2. Access the inductive type *)
- get_pdecl : kername -> info -> info_pdecl
- get_uparams     : kername -> info -> context
- get_nb_uparams  : kername -> info -> nat
- get_nuparams    : kername -> info -> context
- get_nb_nuparams : kername -> info -> nat
- get_params      : kername -> info -> context
- get_nb_params   : kername -> info -> nat
- get_mdecl       : kername -> info -> mutual_inductive_body
- get_ind_bodies  : kername -> info -> list one_inductive_body
- get_indb        : kername -> nat  -> info -> one_inductive_body
- get_relevance   : kername -> nat  -> info -> relevance
- get_ctor        : kername -> nat  -> nat  -> info -> constructor_body

(* 3. Access the context *)
- get_one_term  : ident -> info -> term
- get_term      : list ident -> info -> list term
- get_one_type  : ident -> info -> term
- get_type      : list ident -> info -> list term
- get_typing_context : info -> context
- get_aname :

(* 3. Check var *)
Definition isVar_ident : ident -> nat -> info -> bool
Definition isVar_pos : ident -> nat -> nat -> info -> bool

(* 4. Weakening *)
- weaken : info -> term -> term
- weaken_decl : info -> context_decl -> context_decl
- weaken_context : info -> context -> context

(* 5. Add variables *)
- init_info : info
- add_fresh_var : option ident -> context_decl -> info -> info
- add_old_var : option ident -> context_decl -> info -> info
- add_replace_var : option ident -> term -> info -> info
- add_unscoped_var : option ident -> context_decl -> term -> info -> info

- ++ context version

(* 6. Notations *)
- let* x y z <- f in   n-ary binding

(* 7. Debug *)
- Print_info : info -> list term
*)


(* 0. Datastructre and General Purposed Functions *)
Record info_decl : Type := mk_idecl
  { info_name    : ident ;
    info_old     : bool ;
    info_replace : bool ;
    info_scope   : bool ;
    info_def     : context_decl ;
}.

Record info_pdecl : Type := mk_pdecl
{ info_kname       : kername ;
  info_uparams     : context ;
  info_nb_uparams  : nat ;
  info_nuparams    : context ;
  info_nb_nuparams : nat ;
  info_mdecl       : mutual_inductive_body ;
}.

Record info : Type := mk_info
{ info_context : list info_decl;
  info_ind : list info_pdecl ;
}.


Definition init_info : info := mk_info [] [].

Axiom failwith : forall A, string -> A.
Arguments failwith {_}.



(* 1. General Purposed Functions  *)

(* 1.1 Fold_left and Fold_right *)
Definition fold_right_info {A B X} (tp : nat -> A -> info -> (X -> info -> B) -> B)
  (l:list A) (e:info) (t : list X -> info -> B) : B :=
  let fix aux n ids1 l e t : B :=
    match l with
    | [] => t (rev ids1) e
    | a :: l => tp n a e (fun id1 e => aux (S n) (id1 :: ids1) l e t)
  end in
  aux 0 [] l e t.

  Definition fold_right_info2 {A B X Y} (tp : nat -> A -> info -> (X -> Y -> info -> B) -> B)
  (l:list A) (e:info) (t : list X -> list Y -> info -> B) : B :=
  let fix aux n ids1 ids2 l e t : B :=
    match l with
    | [] => t (rev ids1) (rev ids2) e
    | a :: l => tp n a e (fun id1 id2 e => aux (S n) (id1 :: ids1) (id2 :: ids2) l e t)
  end in
  aux 0 [] [] l e t.

Definition fold_right_info3 {A B X Y Z} (tp : nat -> A -> info -> (X -> Y -> Z -> info -> B) -> B)
  (l:list A) (e:info) (t : list X -> list Y -> list Z -> info -> B) : B :=
  let fix aux n ids1 ids2 ids3 l e t : B :=
    match l with
    | [] => t (rev ids1) (rev ids2) (rev ids3) e
    | a :: l => tp n a e (fun id1 id2 id3 e => aux (S n) (id1 :: ids1) (id2 :: ids2) (id3 :: ids3) l e t)
  end in
  aux 0 [] [] [] l e t.

Definition fold_left_info {A B X} (tp : nat -> A -> info -> (X -> info -> B) -> B)
  (l:list A) (e:info) (t : list X -> info -> B) : B :=
  fold_right_info tp (rev l) e t.

Definition fold_left_info2 {A B X Y} (tp : nat -> A -> info -> (X -> Y -> info -> B) -> B)
  (l:list A) (e:info) (t : list X -> list Y -> info -> B) : B :=
  fold_right_info2 tp (rev l) e t.

Definition fold_left_info3 {A B X Y Z} (tp : nat -> A -> info -> (X -> Y -> Z -> info -> B) -> B)
  (l:list A) (e:info) (t : list X -> list Y -> list Z -> info -> B) : B :=
  fold_right_info3 tp (rev l) e t.

(* 1.2 Fold_right and Fold_left conditional *)
Definition fold_right_info_opt {A B X} (tp : nat -> A -> info -> (list X -> info -> B) -> B)
  (l:list A) (e:info) (t : list X -> info -> B) : B :=
  let fix aux n ids1 l e t : B :=
    match l with
    | [] => t (rev ids1) e
    | a :: l => tp n a e (fun fid1 e => aux (S n) (fid1 ++ ids1) l e t)
  end in
  aux 0 [] l e t.

Definition fold_right_info_opt2 {A B X Y} (tp : nat -> A -> info -> (list X -> list Y -> info -> B) -> B)
  (l:list A) (e:info) (t : list X -> list Y -> info -> B) : B :=
  let fix aux n ids1 ids2 l e t : B :=
    match l with
    | [] => t (rev ids1) (rev ids2) e
    | a :: l => tp n a e (fun fid1 fid2 e => aux (S n) (fid1 ++ ids1) (fid2 ++ ids2) l e t)
  end in
  aux 0 [] [] l e t.

Definition fold_right_info_opt3 {A B X Y Z} (tp : nat -> A -> info -> (list X -> list Y -> list Z -> info -> B) -> B)
  (l:list A) (e:info) (t : list X -> list Y -> list Z -> info -> B) : B :=
  let fix aux n ids1 ids2 ids3 l e t : B :=
    match l with
    | [] => t (rev ids1) (rev ids2) (rev ids3) e
    | a :: l => tp n a e (fun fid1 fid2 fid3 e => aux (S n) (fid1 ++ ids1) (fid2 ++ ids2) (fid3 ++ ids3) l e t)
  end in
  aux 0 [] [] [] l e t.

Definition fold_left_info_opt {A B X} (tp : nat -> A -> info -> (list X -> info -> B) -> B)
  (l:list A) (e:info) (t : list X -> info -> B) : B :=
  fold_right_info_opt tp (rev l) e t.

Definition fold_left_info_opt2 {A B X Y} (tp : nat -> A -> info -> (list X -> list Y -> info -> B) -> B)
  (l:list A) (e:info) (t : list X -> list Y -> info -> B) : B :=
  fold_right_info_opt2 tp (rev l) e t.

Definition fold_left_info_opt3 {A B X Y Z} (tp : nat -> A -> info -> (list X -> list Y -> list Z -> info -> B) -> B)
  (l:list A) (e:info) (t : list X -> list Y -> list Z -> info -> B) : B :=
  fold_right_info_opt3 tp (rev l) e t.

(* 1.3 Others *)
Definition add_idecl : info_decl -> info -> info :=
  fun idecl e => mk_info (idecl :: e.(info_context)) e.(info_ind).

Definition add_pdecl : info_pdecl -> info -> info :=
  fun pdecl e => mk_info e.(info_context) (pdecl :: e.(info_ind)).

Definition check_ident : ident -> info_decl -> bool :=
  fun i idecl => eqb idecl.(info_name) i.

Definition fresh_ident_aux : option ident -> nat -> ident :=
  fun x k => match x with
  | Some s => String.append s (string_of_nat k)
  | None   => String.append "Var" (string_of_nat k)
  end.

Definition fresh_ident : option ident -> info -> ident :=
  fun x e => fresh_ident_aux x (length e.(info_context)).

Definition fresh_id_context : option ident -> info -> context -> list ident * list (ident * context_decl) :=
  fun x e cxt =>
    let le := length e.(info_context) in
    let id_cxt := (mapi (fun i cdecl => (fresh_ident_aux x (i + le), cdecl)) (rev cxt)) in
    (map fst id_cxt, rev id_cxt).

Definition get_id1: list ident -> nat -> ident :=
  fun ids pos_id => nth pos_id ids (failwith "error get one of them").

Definition get_id2 : list (list ident) -> nat -> nat -> ident :=
  fun idss pos1 pos2 =>
  let ids := nth pos1 idss (failwith "error get2 pos1") in
  nth pos2 ids (failwith "error get2 pos2").



(* 2. Debug and Printing Functions *)
Notation "x ^^ y" := (String.append x y) (left associativity, at level 50).
Notation "x ^^^ y" := (x ^^ " ; " ^^ y ) (left associativity, at level 50).

Definition show_def : string -> string -> string :=
  fun key value => key ^^ " := " ^^ value.

Definition show_kername : kername -> string :=
  fun kname => show_def "kername" (snd kname).

Definition show_info_decl : info_decl -> string :=
  fun ' (mk_idecl name old replace scope (mkdecl an db ty)) =>
      show_def "info_name"      (name)
  ^^^ show_def "info_old"       (string_of_bool old)
  ^^^ show_def "info_replace"   (string_of_bool replace)
  ^^^ show_def "info_scope"     (string_of_bool scope)
  ^^^ show_def "info_decl_type" (string_of_term ty)
  ^^^ show_def "info_decl_body" (string_of_option (string_of_term) db).

Definition show_info : info -> string :=
  fun e => fold_left String.append (map show_info_decl e.(info_context)) "".

Definition info_to_term (e : info) : list term :=
  map (fun idecl => tVar (show_info_decl idecl)) (rev e.(info_context)).

Definition show_error_kname : kername -> info -> string :=
  fun kname e =>
      show_kername kname
  ^^^ show_info e.

Definition show_error_indb : kername -> nat -> info -> string :=
  fun kname pos_indb e =>
      show_kername kname
  ^^^ show_def "pos_indb" (string_of_nat pos_indb)
  ^^^ show_info e.

Definition show_error_ctor : kername -> nat -> nat -> info -> string :=
  fun kname pos_indb pos_ctor e =>
      show_kername kname
  ^^^ show_def "pos_indb" (string_of_nat pos_indb)
  ^^^ show_def "pos_ctor" (string_of_nat pos_ctor)
  ^^^ show_info e.



(* 3. Access the inductive types *)
Definition get_pdecl : kername -> info -> info_pdecl :=
  fun kname e =>
    match find (fun pdecl => eqb pdecl.(info_kname) kname) e.(info_ind) with
    | Some pdecl => pdecl
    | None => failwith ("get_pdecl => " ^^ show_error_kname kname e)
    end.

Definition get_uparams : kername -> info -> context :=
  fun kname e => (get_pdecl kname e).(info_uparams).

Definition get_nb_uparams : kername -> info -> nat :=
  fun kname e => (get_pdecl kname e).(info_nb_uparams).

Definition get_nuparams : kername -> info -> context :=
  fun kname e => (get_pdecl kname e).(info_nuparams).

Definition get_nb_nuparams : kername -> info -> nat :=
  fun kname e => (get_pdecl kname e).(info_nb_nuparams).

Definition get_params : kername -> info -> context :=
  fun kname e => (get_pdecl kname e).(info_mdecl).(ind_params).

Definition get_nb_params : kername -> info -> nat :=
  fun kname e => (get_pdecl kname e).(info_mdecl).(ind_npars).

Definition get_mdecl : kername -> info -> mutual_inductive_body :=
  fun kname e => (get_pdecl kname e).(info_mdecl).

Definition get_ind_bodies : kername -> info -> list one_inductive_body :=
  fun kname e => (get_pdecl kname e).(info_mdecl).(ind_bodies).

Definition get_indb : kername -> nat -> info -> one_inductive_body :=
  fun kname pos_indb e => nth pos_indb (get_ind_bodies kname e)
    (failwith (show_error_indb kname pos_indb e)).

Definition get_relevance : kername -> nat -> info -> relevance :=
  fun kname pos_indb e => (get_indb kname pos_indb e).(ind_relevance).

Definition get_ctor : kername -> nat -> nat -> info -> constructor_body :=
  fun kname pos_indb pos_ctor e => nth pos_ctor (get_indb kname pos_indb e).(ind_ctors)
    (failwith (show_error_ctor kname pos_indb pos_ctor e)).



(* 4. Acces the Context *)

(* Aux *)
Definition get_term_idecl : nat -> info_decl -> term :=
  fun pos_idecl idecl =>
  match idecl.(info_def).(decl_body) with
  | Some tm => if idecl.(info_replace)
                then (if idecl.(info_scope) then lift0 (S pos_idecl) tm  else lift0 pos_idecl tm)
               else tRel pos_idecl
  | None => tRel pos_idecl
  end.

Definition get_type_idecl : nat -> info_decl -> term :=
  fun pos_idecl idecl => lift0 (S pos_idecl) idecl.(info_def).(decl_type).

Definition get_info : (nat -> info_decl -> term) -> (info_decl -> bool) ->  info -> list term :=
  fun f p e =>
  let fix aux i e :=
  match e with
  | [] => []
  | idecl :: e =>
    let next := (if idecl.(info_scope) then aux (S i) e else aux i e) in
    if p idecl then f i idecl :: next else next
  end in
  aux 0 e.(info_context).

Definition get_term_info : (info_decl -> bool) -> info -> list term :=
  get_info get_term_idecl.

Definition get_type_info : (info_decl -> bool) -> info -> list term :=
  get_info get_type_idecl.

Definition get_idecl : ident -> info -> (nat * info_decl) :=
  fun id e =>
  let fix aux n e' :=
  match e' with
  | [] => failwith ("get_idecl => " ^^ id ^^ " NOT IN SCOPE " ^^ show_info e)
  | idecl :: e' => if eqb id idecl.(info_name) then (n, idecl)
                    else if idecl.(info_scope) then aux (S n) e' else aux n e'
  end in
  aux 0 e.(info_context).

(* 1.3 Get terms and type *)
Definition get_one_term : ident -> info -> term :=
  fun id e => let ' (pos_var, idecl) := get_idecl id e in
              get_term_idecl pos_var idecl.

Definition get_one_of_term : list ident -> nat -> info -> term :=
  fun ids pos_id e =>
    let ' (pos_var, idecl) := get_idecl (get_id1 ids pos_id) e in
    get_term_idecl pos_var idecl.

Definition get_one_of_term2 : list (list ident) -> nat -> nat -> info -> term :=
  fun idss pos1 pos2 e =>
    let ' (pos_var, idecl) := get_idecl (get_id2 idss pos1 pos2) e in
    get_term_idecl pos_var idecl.

Definition get_term : list ident -> info -> list term :=
  fun ids e => map (fun id => get_one_term id e) ids.

Definition get_one_type : ident -> info -> term :=
fun id e => let ' (pos_var, idecl) := get_idecl id e in
            get_type_idecl pos_var idecl.

Definition get_type : list ident -> info -> list term :=
fun ids e => map (fun id => get_one_type id e) ids.

  (* Works ??? *)
Definition get_typing_context : info -> context :=
  fun e => map info_def e.(info_context).

Definition get_one_aname : ident -> info -> aname :=
  fun id e => let ' (_, idecl) := get_idecl id e in
              idecl.(info_def).(decl_name).

Definition get_aname : list ident -> info -> list aname :=
  fun ids e => map (fun id => get_one_aname id e) ids.

Definition check_term : info -> ident -> term -> bool :=
  fun e id tm => eqb (get_one_term id e) tm.



(* 5. Weakening and Lets *)
Definition get_subst : info -> list term :=
  get_term_info info_old.

Definition weaken : info -> term -> term :=
  fun e => subst0 (get_subst e).

Definition weaken_decl : info -> context_decl -> context_decl :=
  fun e cdecl =>
  let ' (mkdecl an db ty) := cdecl in
  mkdecl an (option_map (weaken e) db) (weaken e ty).



(* 6. Add Inductive Types *)
Definition add_mdecl : kername -> nat -> mutual_inductive_body -> info -> info  :=
  fun kname nb_uparams mdecl e =>
    let rev_params := rev mdecl.(ind_params) in
    add_pdecl (
      mk_pdecl kname
               (rev (firstn nb_uparams rev_params)) nb_uparams
               (rev (skipn nb_uparams rev_params)) (mdecl.(ind_npars) - nb_uparams)
               mdecl) e.


(* 7. Add variables *)
Definition add_old_var : ident -> context_decl -> info -> info :=
  fun x decl e => add_idecl (mk_idecl x true false true (weaken_decl e decl)) e.

Definition add_old_context : list (ident * context_decl) -> info -> info :=
  fun id_cxt e => fold_right (fun ' (id, cdecl) e => add_old_var id cdecl e) e id_cxt.

Definition add_fresh_var : ident -> context_decl -> info -> info :=
  fun x decl e => add_idecl (mk_idecl x false false true decl) e.

Definition add_fresh_context : list (ident * context_decl) -> info -> info :=
  fun id_cxt e => fold_right (fun ' (id, cdecl) e => add_fresh_var id cdecl e) e id_cxt.

Definition add_replace_var : ident -> context_decl -> term -> info -> info :=
  fun x cxt tm e => let ' mkdecl an _ ty := weaken_decl e cxt in
                    add_idecl (mk_idecl x true true true (mkdecl an (Some tm) ty)) e.

Definition add_unscoped_var : ident -> context_decl -> term -> info -> info :=
  fun x cxt tm e => let ' mkdecl an _ ty := weaken_decl e cxt in
                    add_idecl (mk_idecl x false true false (mkdecl an (Some tm) ty)) e.

(* Warning needs list of same length *)
(* terms are in reversed order *)
Definition add_replace_context : list (ident * context_decl) -> list term -> info -> info :=
  fun id_cxt ltm e =>
  fold_right (fun ' ((id, cdecl), tm) e => add_replace_var id cdecl tm e)
  e (combine id_cxt (rev ltm)).

Definition weaken_context : info -> context -> context :=
  fun e cxt =>
  fold_right_info (
    fun i cdecl e t =>
    let cdecl' := weaken_decl e cdecl in
    let e' := add_old_var "foo" cdecl e in
    cdecl' :: (t I e'))
  cxt e (fun _ _ => []).



(* 8. Notations *)
Notation "e ↑" := (weaken e) (at level 10).

Notation "let* x .. z '<-' c1 'in' c2" := (c1 (fun x => .. (fun z => c2) ..))
(at level 100, x binder, z binder, c1 at next level, right associativity).




(* ########################################################################## *)
(* ########################################################################## *)
(* ########################################################################## *)

(*
#############################
###  Frontend interface   ###
#############################

(* 0. Else *)
- get_indices      : kername -> nat -> info -> context
- get_ctor_indices : kername -> nat -> nat -> info -> list term


(* 1. Keep Binders & 2. Add Binders *)
- kp_tLetIn  : aname -> term -> term -> option ident -> info -> (info -> term) -> term
- kp_binder  : (aname -> term -> term -> term) -> aname -> term ->
                option ident -> info -> (info -> term) -> term
- kp_tProd   : aname -> term -> option ident -> info -> (info -> term) -> term
- kp_tLambda : aname -> term -> option ident -> info -> (info -> term) -> term
- it_kp_binder : ...
- closure_params, closure_uparams, closure_nuparams,

- mk versions: mk_tLetIn, mk_binder, mk_tProd, mk_tLambda, it_mk_binder
- closure_indices

- mk_tFix / mk_tCase

(* 3. Inductive Types *)
- kname_to_ident : ident -> kername -> ident
- replace_ind : kername -> mutual_inductive_body -> info -> info
- split_params : nat -> mutual_inductive_body -> context * context
- make_ind : nat -> info -> term
- make_cst : nat -> nat -> info -> term

(* 4. Reduction *)
- reduce_except_lets : info -> term -> term
- reduce_full : info -> term -> term


(* 5. Decide Interface *)
- check_args_by_arg : (term -> info -> A) -> context -> info -> A
- check_ctors_by_arg : (term -> info -> A) -> list context -> info -> A
- debug_check_args_by_arg {A} : global_env -> (term -> info -> A) -> context -> info -> list A
- debug_check_ctors_by_arg {A} : global_env -> (term -> info -> A) -> list context -> info -> list (list A)
- get_args : mutual_inductive_body -> list context
*)



(* 1. Inductive Types *)
Definition ind_to_cxt : kername -> info -> context :=
  fun kname e =>
  map (fun indb => mkdecl (mkBindAnn nAnon indb.(ind_relevance)) None indb.(ind_type))
  (rev (get_ind_bodies kname e)).

Definition ind_to_terms : kername -> info -> list term :=
  fun kname e => mapi (fun i _ => (tInd (mkInd kname i) [])) (get_ind_bodies kname e).

Definition replace_ind : kername -> info -> (list ident) * info :=
  fun kname e =>
  let ' (id_inds, id_cxt_inds) := fresh_id_context (Some "Ind") e (ind_to_cxt kname e) in
  let e := add_replace_context id_cxt_inds (ind_to_terms kname e) e in
  (id_inds, e).

(* Builds: Ind A1 ... An B0 ... Bm i1 ... il *)
Definition make_ind : kername -> nat -> list ident -> list ident -> list ident -> info -> term :=
  fun kname pos_indb id_uparams id_nuparams id_indices e =>
  mkApps (tInd (mkInd kname pos_indb) [])
          (  get_term id_uparams  e
          ++ get_term id_nuparams e
          ++ get_term id_indices e).

(* Builds: Cst A1 ... An B0 ... Bm *)
Definition make_cst : kername -> nat -> nat -> list ident -> list ident -> info -> term :=
  fun kname pos_indb pos_ctor id_uparams id_nuparams e =>
  mkApps (tConstruct (mkInd kname pos_indb) pos_ctor [])
          (get_term id_uparams e ++ get_term id_nuparams e).

Arguments make_cst _ pos_indb pos_ctor id_uparams id_nuparams _.

Definition get_indices : kername -> nat -> info -> context :=
  fun kname pos_indb e => weaken_context e (get_indb kname pos_indb e).(ind_indices).

Definition get_ctor_indices : kername -> nat -> nat -> info -> list term :=
  fun kname pos_indb pos_ctor e => map (e ↑) (get_ctor kname pos_indb pos_ctor e).(cstr_indices).



(* 2. Keep and Add Binders *)
Definition kp_tLetIn : aname -> term -> term -> info -> (ident -> info -> term) -> term :=
  fun an db t1 e t2 =>
    let id := fresh_ident (Some "LET") e in
    let db' := e ↑ db in
    let t1' := e ↑ t1 in
    let e := add_old_var id (mkdecl an (Some db) t1) e in
    tLetIn an db' t1' (t2 id e).

Definition mk_tLetIn : aname -> term -> term -> info -> (ident -> info -> term) -> term :=
  fun an db t1 e t2 =>
    let id := fresh_ident (Some "LET") e in
    let e := add_fresh_var id (mkdecl an (Some db) t1) e in
    tLetIn an db t1 (t2 id e).

Section Binder.

  Context (binder : aname -> term -> term -> term).

  Definition kp_binder : aname -> term -> option ident -> info -> (ident -> info -> term) -> term :=
    fun an t1 x e t2 =>
      let id := fresh_ident x e in
      let t1' := e ↑ t1 in
      let e  := add_old_var id (mkdecl an None t1) e in
      binder an t1' (t2 id e).

  Definition it_kp_binder : context -> option ident -> info -> (list ident -> info -> term) -> term :=
    fun cxt x => fold_left_info
    (fun _ cdecl e t =>
      let '(mkdecl an db ty) := cdecl in
      match db with
      | None => kp_binder an ty x e t
      | Some db => kp_tLetIn an db ty e t
      end) cxt.

  (* new functions *)
  Definition closure_uparams : kername -> info -> (list ident -> info -> term) -> term :=
    fun kname e => it_kp_binder (get_uparams kname e) (Some "uparams") e.

  Definition closure_nuparams : kername -> info -> (list ident -> info -> term) -> term :=
    fun kname e => it_kp_binder (get_nuparams kname e) (Some "nuparams") e.

  Definition closure_params : kername -> info -> (list ident -> info -> term) -> term :=
  fun kname e => it_kp_binder (get_params kname e) (Some "params") e.


  Definition mk_binder : aname -> term -> option ident -> info -> (ident -> info -> term) -> term :=
    fun an t1 x e t2 =>
      let id := fresh_ident x e in
      let e := add_fresh_var id (mkdecl an None t1) e in
      binder an t1 (t2 id e).

  Definition it_mk_binder : context -> option ident -> info -> (list ident -> info -> term) -> term :=
    fun cxt x => fold_left_info
    (fun _ cdecl e t =>
      let '(mkdecl an db ty) := cdecl in
      match db with
      | None => mk_binder an ty x e t
      | Some db => mk_tLetIn an db ty e t
      end) cxt.

  Definition closure_binder {A} (x : option ident) (l : list A)
    (naming : nat -> A -> aname) (typing : nat -> A -> info -> term) :
    info -> (list ident -> info -> term) -> term :=
    fold_right_info
      (fun n a e t => mk_binder (naming n a) (typing n a e) x e t)
      l .

  Definition closure_indices : kername -> nat -> info -> (list ident -> info -> term) -> term :=
    fun kname pos_indb e => it_mk_binder (get_indices kname pos_indb e) (Some "indices") e.

End Binder.

Definition kp_tProd := kp_binder tProd.
Definition kp_tLambda := kp_binder tLambda.

Definition it_kp_tProd := it_kp_binder tProd.
Definition it_kp_tLambda := it_kp_binder tLambda.

Definition mk_tProd := mk_binder tProd.
Definition mk_tLambda := mk_binder tLambda.

Definition it_mk_tProd := it_mk_binder tProd.
Definition it_mk_tLambda := it_mk_binder tLambda.



Section mk_tFix.
  Context (ind_bodies : list one_inductive_body).
  Context (fan   : nat -> one_inductive_body -> info -> aname).
  Context (fty   : nat -> one_inductive_body -> info -> term).
  Context (frarg : nat -> one_inductive_body -> info -> nat).

  Definition mk_tFix : nat -> info -> (list ident -> nat -> one_inductive_body -> info -> term) -> term :=
    fun focus e tmc =>
    let cxt_fix := rev (mapi (fun pos_indb indb => mkdecl (fan pos_indb indb e) None (fty pos_indb indb e)) ind_bodies) in
    let ' (id_fix, id_cxt_fix) := fresh_id_context (Some "Fix") e cxt_fix in
    let e_Fix := add_fresh_context id_cxt_fix e in
    tFix (mapi (fun pos_indb indb => mkdef _ (fan pos_indb indb e) (fty pos_indb indb e)
                    (tmc id_fix pos_indb indb e_Fix) (frarg pos_indb indb e)) ind_bodies) focus.

End mk_tFix.


  Section MktCase.
  Context (kname : kername).
  Context (pos_indb : nat).
  Context (indb : one_inductive_body).

  Context (mk_case_info : nat -> one_inductive_body -> info -> case_info).
  Context (mk_case_pred : list ident -> ident -> nat -> one_inductive_body -> info -> term).
  Context (id_uparams id_nuparams : list ident).

  Definition mk_info_pred : info -> list ident * ident * info :=
    fun e =>
    let ' (id_findices , id_cxt_indices) := fresh_id_context None e indb.(ind_indices) in
    let e_pred := add_fresh_context id_cxt_indices e in
    let fVarMatch := (mkdecl (mkBindAnn nAnon indb.(ind_relevance)) None
                          (make_ind kname pos_indb id_uparams id_nuparams id_findices e_pred)) in
    let id_fVarMatch := fresh_ident None e_pred in
    let e_pred := add_fresh_var id_fVarMatch fVarMatch e_pred in
    (id_findices, id_fVarMatch, e_pred).

  Definition mk_pred : info -> predicate term :=
    fun e =>
    let ' (id_findices, id_fVarMatch, e_pred) := mk_info_pred e in
    mk_predicate []
      ((get_term id_uparams e ++ get_term id_nuparams e))
      (get_aname [id_fVarMatch] e_pred ++ get_aname id_findices e_pred)
      (mk_case_pred id_findices id_fVarMatch pos_indb indb e_pred).

  Definition mk_tCase : term -> info -> (nat -> constructor_body -> info -> branch term) -> term :=
    fun tm_match e branch =>
    tCase (mk_case_info pos_indb indb e) (mk_pred e) tm_match
    (mapi (fun pos_ctor ctor => branch pos_ctor ctor e) indb.(ind_ctors)).

End MktCase.



(* 3. Reduction *)
From MetaCoq Require Import Template.Checker.
Import RedFlags.

Definition noiota_flags := mk true true false true true true.

Definition reduce_except_lets :  global_env -> info -> term -> term :=
  fun E e t =>
  match reduce_opt noiota_flags empty_global_env (get_typing_context e) 5000 t with
  | Some t => t
  | None => tVar "ERREUR REDUCTION"
  end.

Definition reduce_lets : info -> term -> term :=
  fun e t => expand_lets (get_typing_context e) t.

Definition reduce_full : global_env -> info -> term -> term :=
  fun E e t =>
  match reduce_opt default E (get_typing_context e) 5000 t with
  | Some t => t
  | None => tVar "ERREUR REDUCTION"
  end.



(* ########################################################################## *)
(* ########################################################################## *)
(* ########################################################################## *)

(*
#############################
###    Decide interface   ###
#############################

*)

Section CheckArg.

  Context {A : Type}.
  Context (bop : A -> A -> A).
  Context (default : A).
  Context (E : global_env).
  Context (kname : kername).

Definition check_args_by_arg : (term -> info -> A) -> context -> info -> A :=
  fun check_arg args e =>
  fold_left_info
    ( fun i arg e t =>
        let rty := reduce_full E e (e ↑ arg.(decl_type)) in
        let id_arg := fresh_ident (Some "arg") e in
        let e' := add_old_var id_arg arg e in
        match arg.(decl_body) with
        | None => bop (check_arg rty e) (t id_arg e')
        | Some _ => t id_arg e'
        end
  )
  args e (fun _ _ => default).

Definition check_ctors_by_arg : (term -> info -> A) -> list context -> info -> A :=
  fun check_arg lcxt e =>
  fold_left bop (map (fun cxt => check_args_by_arg check_arg cxt e) lcxt) default.

End CheckArg.

Definition debug_check_args_by_arg {A} : global_env -> (term -> info -> A) -> context -> info -> list A :=
  fun E check_arg cxt e =>
  check_args_by_arg (@app A) [] E (fun x e => [check_arg x e]) cxt e.

Definition debug_check_ctors_by_arg {A} : global_env -> (term -> info -> A) -> list context -> info -> list (list A) :=
  fun E check_arg lcxt e => map (fun cxt => debug_check_args_by_arg E check_arg cxt e) lcxt.

Definition get_args : mutual_inductive_body -> list context :=
  fun mdecl => map cstr_args (concat (map ind_ctors mdecl.(ind_bodies))).