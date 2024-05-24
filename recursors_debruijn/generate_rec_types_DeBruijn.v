From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import All.
From MetaCoq.Common Require Import Universes.

Import MCMonadNotation.


Definition type_of_constructor mdecl (cdecl : constructor_body) (c : inductive * nat) (u : list Level.t) :=
  let mind := inductive_mind (fst c) in
  subst0 (inds mind u mdecl.(ind_bodies)) (subst_instance u (cstr_type cdecl)).


(* ############################
   ###         Lemma        ###
   ############################ *)

Definition printInductive (q : qualid): TemplateMonad unit :=
  kn <- tmLocate1 q ;;
  match kn with
  | IndRef ind => (tmQuoteInductive ind.(inductive_mind)) >>= tmPrint
  | _ => tmFail ("[" ^ q ^ "] is not an inductive")
  end.

Definition printConstant (q : qualid) b : TemplateMonad unit :=
  kn <- tmLocate1 q ;;
  match kn with
  | ConstRef kn => (tmQuoteConstant kn b) >>= tmPrint
  | _ => tmFail ("[" ^ q ^ "] is not a constant")
  end.

MetaCoq Run (printInductive "list").

Definition AnonRel := {| binder_name := nAnon; binder_relevance := Relevant |}.


(* rel_list shift n => [tRel (shift + n-1); ...; tRel (shift)] *)
Fixpoint rel_list (shift : nat) (n : nat) : list term :=
  match n with
  | 0 => []
  | S n => (tRel (shift + n)) :: (rel_list (shift) n)
  end.

Fixpoint fold_right_ig {A B} (f : nat -> B -> A -> A) (a0 : A) (l : list B)
 (i : nat) : A :=
  match l with
  | [] => a0
  | h :: q => f i h (fold_right_ig f a0 q (S i))
  end.

Definition fold_right_i {A B} (f : nat -> B -> A -> A) (a0 : A) (l : list B) : A
  := fold_right_ig f a0 l 0.


(* ############################
   ###     PreProcessing    ###
   ############################ *)

  Definition Kername_ctor (l : list term) (shift : nat) (ctor : constructor_body)
  (pos : nat) : constructor_body :=
  {| cstr_name    := ctor.(cstr_name) ;
     cstr_args    := subst_context l shift ctor.(cstr_args);
     cstr_indices := ctor.(cstr_indices);
     cstr_type    := ctor.(cstr_type);
     cstr_arity   := ctor.(cstr_arity)
  |}.

Definition Kername_one (l : list term) (shift : nat) (indb : one_inductive_body)
  : one_inductive_body :=
  {| ind_name      := indb.(ind_name) ;
     ind_indices   := indb.(ind_indices) ;
     ind_sort      := indb.(ind_sort) ;
     ind_type      := indb.(ind_type) ;
     ind_kelim     := indb.(ind_kelim) ;
     ind_ctors     := mapi (fun pos ctor => Kername_ctor l shift ctor pos) indb.(ind_ctors) ;
    ind_projs     := indb.(ind_projs) ;
    ind_relevance := indb.(ind_relevance) ;
  |}.

Definition Kername_mutual (l : list term) (shift : nat) (mdecl : mutual_inductive_body)
  : mutual_inductive_body :=
  {| ind_finite    := mdecl.(ind_finite)   ;
     ind_npars     := mdecl.(ind_npars)    ;
     ind_params    := mdecl.(ind_params)   ;
     ind_bodies    := mapi (fun i indb => Kername_one l shift indb) mdecl.(ind_bodies)  ;
     ind_universes := mdecl.(ind_universes) ;
     ind_variance  := mdecl.(ind_variance)
  |}.

(* ############################
   ###      Generation      ###
   ############################ *)

(* Step 2 : Closure Parameters
  Inductive Name A1 ... An := ...
    => forall A1, ... An, t *)

Definition gen_closure_param (params : context) (t : term) : term :=
  fold_right (fun param t' => tProd (param.(decl_name)) (param.(decl_type)) t')
  t (rev params). (* Parameters are stored in snoc order => rev *)


(* Step 3 : Closure Predicates
  Inductive Name A1 ... An := ...
   => forall P : (Name A1 ... An) -> U *)

Definition gen_closure_one_pred (name : kername) (pos : nat) (indb : one_inductive_body)
  (nb_params : nat) (U : term) (t : term) : term :=
  (* P : forall n1 ... nk, Ind A1 ... An n1 ... nk -> U *)
  tProd {| binder_name := nNamed "P"; binder_relevance := Relevant |}
    (* Closure indices : forall n1 ... nk *)
    (fold_right (fun indice t' => tProd indice.(decl_name) indice.(decl_type) t')
    (* Ind A1 ... An n1 ... nk -> U *)
      ((tProd AnonRel
              (tApp (tInd {| inductive_mind := name; inductive_ind := pos |} [])
                    (    rel_list (pos + #|indb.(ind_indices)|) nb_params
                      ++ rel_list 0 #|indb.(ind_indices)|                 ))
              U))
    (rev indb.(ind_indices))) (* Indices are stored in snoc order => rev *)
  t.

Definition gen_closure_pred (name : kername) (mdecl : mutual_inductive_body)
  (U : term) (t : term) : term :=
  fold_right_i (fun i indb t => gen_closure_one_pred name i indb mdecl.(ind_npars) U t)
  t mdecl.(ind_bodies).


(* Step 4 : Generate Constructors
  Inductive Name A1 ... An :=
  | c n1 ... nk x1 ... xl : Name A1 ... An
  ...
   => (forall n1 ... nk, forall x1 [P n1 ... nk x1],
                         ...
                         forall x1 [P n1 ... nk x1],
                         c n1 ... nk x1 ... xk      ) *)


(* WIP *)
Definition type_of_arg (kname : kername) (nb_blocks : nat) (shift : nat) (t : term) : term :=
  lift shift nb_blocks t.

Definition rec_call (type_arg : term) : option term := None.

Inductive Arg_or_Rec :=
| Arg : Arg_or_Rec
| Rec : Arg_or_Rec.

Fixpoint compute_ctor_closure (kname : kername) (nb_blocks : nat) (shift : nat) (args : context) :
  list (Arg_or_Rec * (binder_annot name) * term) :=
  match args with
  | [] => []
  | (arg::q) =>
    let targ := type_of_arg kname nb_blocks shift arg.(decl_type) in
    match rec_call targ with
    | Some rarg =>    (Arg, arg.(decl_name), targ)
                   :: (Rec, AnonRel, rarg)
                   :: (compute_ctor_closure kname nb_blocks (shift + 1) q)
    | None      =>    (Arg, arg.(decl_name), targ)
                   :: (compute_ctor_closure kname nb_blocks shift q)
    end
  end.

Fixpoint compute_arg_cst (rshift : nat)
  (l : list (Arg_or_Rec * binder_annot name * term)) : list term :=
  match l with
  | [] => []
  | (Arg, _, _)::q => (tRel rshift) :: compute_arg_cst (rshift -1) q
  | (Rec, _, _)::q => compute_arg_cst (rshift -1) q
  end.

Definition gen_closure_ctor (shiftP : nat) (kname : kername) (nb_blocks : nat) (cb_block : nat)
      (nb_params : nat) (cst : constructor_body) (nb_cst : nat) (t : term) : term :=
  let closure := compute_ctor_closure kname nb_blocks nb_cst (rev cst.(cstr_args)) in
  let nb_fclosure := #|closure| in
   (* IHC : forall x1 ... xn, P (c x1 ... xn)  *)
  tProd {| binder_name := nNamed (String.append "IH" cst.(cstr_name)) ;
           binder_relevance := Relevant |}
        (* Closure : forall x1 ... xn *)
        (fold_right (fun arg t' => tProd (snd (fst arg)) (snd arg) t')
          (* P (c x1 ... xn) *)
          (tApp (tRel (shiftP + nb_fclosure))
                [tApp (tConstruct {| inductive_mind := kname; inductive_ind := cb_block|} nb_cst [])
                (    rel_list (nb_blocks + nb_fclosure) nb_params
                  ++ compute_arg_cst (nb_fclosure - 1) closure)])
        closure)
        t.


        (* Besoin de savoir quoi ???
=> nb déjà traité => récupérer P
=> kername
=> besoin de savoir le nb cst
*)

Definition gen_closure_ctors2 (shiftP : nat) (kname : kername) (nb_blocks : nat)
  (nb_params : nat) (indb : one_inductive_body) (t : term) : term :=
  fold_right_i (fun i ctor t' => gen_closure_ctor (i + shiftP) kname nb_blocks 0 nb_params ctor i t')
    t
  indb.(ind_ctors).


(* Old  *)
(* Definition gen_closure_cst (name : kername) (pos : nat)
  (cst : constructor_body) (i : nat) (t : term) : term :=
  tProd {| binder_name := nNamed (String.append "IH" cst.(cstr_name)) ; binder_relevance := Relevant |}
    (tProd AnonRel
          (tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
                   inductive_ind := 0 |} [])
          (tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
                   inductive_ind := 0 |} []))
    t.

Definition gen_closure_ctors (name : kername) (mdecl : mutual_inductive_body)
  (t : term) : term :=
  (* Closure ind block *)
  fold_right_i (fun pos indb t' =>
    (* Closure ctors *)
    fold_right_i (fun i ctor t'' => gen_closure_cst name pos ctor i t'')
    t' indb.(ind_ctors))
  t mdecl.(ind_bodies). *)



(* Step 5 : Generate Output
Inductive Name A1 ... An := ...
  => forall n1 ... nk, forall x : (Name A1 ... An n1 ... nk), P x *)

Definition gen_output (shiftParam shiftP : nat) (nb_params : nat)
  (ind : inductive) (indb : one_inductive_body)  : term :=
  (* Closure indicies *)
  fold_right (fun indice t' => tProd (indice.(decl_name)) (indice.(decl_type)) t')
    (* forall x : Ind Name A1 ... An n1 ... nk *)
    (tProd {| binder_name := nNamed "x"; binder_relevance := Relevant |}
           (tApp (tInd ind [])
                 (    rel_list (#|indb.(ind_indices)| + shiftParam) nb_params
                   ++ rel_list 0 #|indb.(ind_indices)|))
    (* P n1 ... nk x *)
    (tApp (tRel (1 + #|indb.(ind_indices)| + shiftP))
          (rel_list 1 #|indb.(ind_indices)| ++ [tRel 0])))
  (rev indb.(ind_indices)). (* Indices are stored in snoc order => rev *)


(* Generate the type of a recursor
TODO :
- Deal with constructors ???
- Parametrise by allowed_elim
- Deal with names
- Deal with Nested
*)

Polymorphic Definition gen_rec_type (ind : inductive) (mdecl : mutual_inductive_body)
  (indb : one_inductive_body)
  : term :=
  let nb_ctors := fold_right (fun indb t => #|indb.(ind_ctors)| + t)
                  0 mdecl.(ind_bodies) in
  (* 1. PreProcessing *)
  (* 2. Closure by Parameters *)
  gen_closure_param mdecl.(ind_params)
  (* 3. Closure by Predicate *)
  (gen_closure_pred ind.(inductive_mind) mdecl (tSort (Universe.of_levels (inl PropLevel.lProp)))
  (* 4. Closure Constructors *)
  (* (gen_closure_ctors ind.(inductive_mind) mdecl *)
  (gen_closure_ctors2 0 ind.(inductive_mind) #|mdecl.(ind_bodies)| mdecl.(ind_npars) indb
  (* 5. Output *)
  (gen_output (#|mdecl.(ind_bodies)| + nb_ctors) (* The number of predicate created*)
              (* -1 because tRel start at 0 but #|mdecl.(ind_bodies)| >= 1*)
              (#|mdecl.(ind_bodies)| -ind.(inductive_ind) -1 + nb_ctors)
              mdecl.(ind_npars)
              ind
              indb))).











(* ############################
   ###    Tests Functions   ###
   ############################ *)

Polymorphic Definition test_term (tm : Ast.term) : TemplateMonad term :=
  match tm with
  | tInd ind _ =>
    mdecl <- tmQuoteInductive (inductive_mind ind) ;;
    (* PreProcessing : Replacing tRel by tInd*)
    let Klist := (inds (inductive_mind ind) [] mdecl.(ind_bodies)) in
    let mdecl := (Kername_mutual Klist mdecl.(ind_npars) mdecl) in
    (* PreProcessing : Replacing [tRel (k-1), ... , tRel(0)] by
    [tRel (n + k-1 ), ... , tRel(n + 0)] as we are going to add n predicates *)
    let mdecl := (Kername_mutual (rel_list #|mdecl.(ind_bodies)| mdecl.(ind_npars)) 0 mdecl) in
    let foo := nth_error mdecl.(ind_bodies) (inductive_ind ind) in
    match foo with
    | Some indb =>
      let rec_typ := tmEval all (gen_rec_type ind mdecl indb) in
      rec_typ
    | None    => tmFail "Error"
    end
  | _ => tmPrint tm ;; tmFail " is not an inductive"
  end.

Polymorphic Definition test (tm : Ast.term) : TemplateMonad unit :=
  t <- test_term tm ;;
  (* tmPrint t. *)
  x <- (tmUnquote t) ;;
  y <- (tmEval all x.(my_projT2)) ;;
  tmPrint y.


(* ############################
   ###      Quick Tests     ###
   ############################ *)

(* No Parameters *)
MetaCoq Run (test <% False %>).
MetaCoq Run (test <% bool %>).
MetaCoq Run (test <% nat %>).

Inductive three_nat : Set :=
| tO : three_nat
| tS : three_nat -> three_nat -> three_nat -> three_nat.

MetaCoq Run (test <% three_nat %>).

Inductive bnat : Set :=
| bO : bnat
| bS : bnat -> bool -> bnat -> bnat.

MetaCoq Run (test <% bnat %>).

(* Parameters *)
MetaCoq Run (test <% list %>).
MetaCoq Run (test <% prod %>).
MetaCoq Run (test <% sum %>).

(* Indices *)
Inductive vec : nat -> Set :=
| vec0   : vec 0
| vecS n : vec n -> vec (S n).

MetaCoq Run (printInductive "vec").
MetaCoq Run (test <% vec %>).

Inductive vec2 (A B : Set) : nat -> bool -> Set :=
| vnil (a : A)   : vec2 A B 0 true
| vin  (b : B) n : vec2 A B n false.

MetaCoq Run (test <% vec2 %>).

(* Mutual inductive Type *)
Inductive teven : Prop :=
| tevenb  : teven
| tevenS : todd -> teven
with
  todd : Prop :=
  | toddS : teven ->  todd.

MetaCoq Run (test <% teven %>).
MetaCoq Run (test <% todd %>).

Inductive even : nat -> Prop :=
  | even0   : even 0
  | evenS n : odd n -> even (S n)
with
  odd : nat -> Prop :=
  | oddS n : even n -> odd (S n).

MetaCoq Run (test <% even %>).
MetaCoq Run (test <% odd %>).

(* Others  *)
(* Inductive three_nat : Set :=
| tO : three_nat
| tS : three_nat -> three_nat -> three_nat -> three_nat.

MetaCoq Run (test <% three_nat %>). *)

(* Inductive bnat : Set :=
| bO : bnat
| bS : bnat -> bool -> bnat -> bnat.

MetaCoq Run (test <% bnat %>). *)










(* ############################
   ###    Examples Tests    ###
   ############################ *)

(* False => no cst
   Inductive False : Prop :=  .
   False_rec : forall P : Set, False -> P *)

MetaCoq Run (test <% False %>).

(* bool => no rec
   Inductive bool : Set :=  true : bool | false : bool.
   bool_rec : forall P : bool -> Set,
              P true ->
              P false ->
              forall b : bool, P b *)

MetaCoq Run (test <% bool %>).

(*
Nat => basic rec
Inductive nat : Set :=  O : nat | S : nat -> nat.
nat_rec : forall P : nat -> Set,
          P 0 ->
          (forall n : nat, P n -> P (S n)) ->
          forall n : nat, P n
nat_ind : forall P : nat -> Prop,
          P 0 ->
          (forall n : nat, P n -> P (S n))
          -> forall n : nat, P n *)

MetaCoq Run (test <% nat %>).

(* three_nat_rec => several arg
  forall P : three_nat -> Set,
  P O ->
  (forall t  : three_nat, P t ->
    forall t0 : three_nat, P t0 ->
    forall t1 : three_nat, P t1 ->
    P (S t t0 t1)) ->
  forall t : three_nat, P t *)

MetaCoq Run (test <% three_nat %>).

(* bnat_rec => arg of different type
  forall P : bnat -> Set,
  P bO ->
  (forall b : bnat, P b ->
   forall (b0 : bool),
   forall (b1 : bnat), P b1 ->
   P (bS b b0 b1)) ->
  forall b : bnat, P b *)

MetaCoq Run (test <% bnat %>).

(* Lists => polymorphism
list_rec : forall (A : Type) (P : list A -> Set),
           P (nil A) ->
           (forall (a : A) (l : list A), P l -> P (cons A a l)) ->
           forall l : list A, P l
*)
MetaCoq Run (test <% list %>).

(* vec => basic index inductive type
vec_rec : forall P : forall n : nat, vec n -> Set,
          P 0 vec0 ->
          (forall (n : nat) (v : vec n), P n v -> P (S n) (vecS n v)) ->
          forall (n : nat) (v : vec n), P n v *)

MetaCoq Run (test <% vec %>).

(* teven => trivial mutual
teven_todd_ind : forall (P : teven -> Prop)
                        (P0 : todd -> Prop),
                 P even ->
                 (forall t : todd, P0 t -> P (evenS t)) ->
                 (forall t : teven, P t -> P0 (oddS t)) ->
                 forall t : teven, P t
*)
Scheme teven_todd_ind := Induction for teven Sort Prop
  with todd_teven_ind := Induction for todd Sort Prop.
Check teven_todd_ind.

(*
even odd => mutual inductive type +
even_odd_ind : forall (P : forall n : nat, even n -> Prop)
                      (P0 : forall n : nat, odd n -> Prop),
               P 0 even0 ->
               (forall (n : nat) (o : odd n),  P0 n o -> P  (S n) (evenS n o)) ->
               (forall (n : nat) (e : even n), P  n e -> P0 (S n) (oddS n e)) ->
               forall (n : nat) (e : even n), P n e *)

MetaCoq Run (test <% even %>).






