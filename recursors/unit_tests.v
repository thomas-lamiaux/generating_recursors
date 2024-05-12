From MetaCoq.Utils Require Import utils.
From MetaCoq.Utils Require Import MCString.
From MetaCoq.Template Require Import All.
From MetaCoq.Common Require Import Universes.

Import MCMonadNotation.

Require Import preliminary.
Require Import preprocess_debruijn_to_named.
Require Import generate_rec_types_named.
Require Import postprocess_named_to_debruijn.


(* ############################
   ###    Tests Functions   ###
   ############################ *)

Inductive Tests : Set := 
| PrintPreprocess : Tests
| PrintTypeRec    : Tests
| PrintTermRec    : Tests
| TestTermTypeRec : Tests.

Definition type_test2 (wt : Tests) : Type := 
  match wt with  
  | PrintPreprocess => unit
  | _ => term 
  end.

Definition gen_rec_term := tRel 0.



(* 
1. debug : look up preprocess / type / term generated 
2. Test type / term / both 

*)

(* 

Print mdecl => Stop here 
Else => continue 
  let t := 
    If Type match as e return 
    gen_type 
    | Print => tmPrint 
    | LookUp => convert 
    Else ???
  let tm := 
    If Temr match as e return 
    gen_type 
    | Print => tmPrint 
    | Test => convert 
    Else 
  
      
Only during Unquote that it bugs !

*)

MetaCoq Test Quote string.

Print String.

Definition tmPrintb {A} (b : bool) (a : A) : TemplateMonad unit := 
  if b then tmPrint a else tmMsg "".

Definition test_term (print_mdecl print_term print_type : bool) (tm : term) 
  : TemplateMonad _ :=
  match tm with
  | tInd ind0 _ =>
    let kname := inductive_mind ind0 in 
    let pos_block := inductive_ind ind0 in
    (* Get the mdecl definition and preprocess it *)
    mdecl <- tmQuoteInductive (inductive_mind ind0) ;;
    tmPrintb print_mdecl mdecl  ;; 
    let mdecl := preprocessing_mind kname mdecl in
    (* Get the pos_block body under scrutiny *)
    match nth_error mdecl.(ind_bodies) pos_block with
      | Some indb => 
        (* Compute term *)
        named_tm_rec <- tmEval all (gen_rec_term) ;;
        tmPrintb print_term named_tm_rec ;;
        debruijn_tm_rec <- tmEval all (named_to_debruijn 100 named_tm_rec) ;;
        (* Compute type *)
        named_ty_rec <- tmEval all (gen_rec_type kname pos_block mdecl indb) ;;
        tmPrintb print_type named_ty_rec ;; 
        debruijn_ty_rec <- tmEval all (named_to_debruijn 100 named_ty_rec) ;;
        (* return *)
        tmReturn (debruijn_tm_rec, debruijn_ty_rec)
        | None    => tmFail "Error"
    end
  | _ => tmPrint tm ;; tmFail " is not an inductive"
  end.

Inductive mode := 
| Debug     : mode 
| PrintType : mode 
| PrintTerm : mode 
| TestBoth  : mode. 

Definition test_option (print_mdecl print_term print_type : bool) (m : mode) (tm : term) : TemplateMonad unit :=
  t <- test_term print_mdecl print_term print_type tm ;;
  let tm_rec := fst t in 
  let ty_rec := snd t in 
  match m with 
  | Debug => tmMsg ""
  | PrintType =>  x <- (tmUnquote ty_rec) ;;
                  ker_ty_rec <- (tmEval all x.(my_projT2)) ;;
                  tmPrint ker_ty_rec
  | PrintTerm =>  x <- (tmUnquote tm_rec) ;;
                  ker_tm_rec <- (tmEval all x.(my_projT2)) ;;
                  tmPrint ker_tm_rec
  | TestBoth  => tmFail "bugs at the moment"
                 (* x <- (tmUnquote ty_rec) ;;
                 ker_ty_rec <- (tmEval all x.(my_projT2)) ;;
                 ker_tm_rec <- tmUnquoteTyped ker_ty_rec tm_rec ;; 
                 tmPrint ker_tm_rec ;; 
                 tmPrint ker_ty_rec *)
  end.

Definition test (tm : term) := test_option false false false PrintType tm.



(* ############################
   ###      Quick Tests     ###
   ############################ *)


(* ################################################# *)
(* 1. Mutual : NO / Parameters : NO / Indices : NO *)

(* MetaCoq Run (printInductive "False"). *)
MetaCoq Run (test <% False %>).

(* MetaCoq Run (printInductive "bool"). *)
MetaCoq Run (test <% bool %>).

(* MetaCoq Run (printInductive "nat"). *)
MetaCoq Run (test <% nat %>).

Inductive bnat : Set :=
| bO : bnat
| bS : bnat -> bool -> bnat -> bnat.

(* MetaCoq Run (printInductive "bnat"). *)
MetaCoq Run (test <% bnat %>).


(* ################################################# *)
(* 2. Mutual : NO / Parameters : YES / Indices : NO *)

(* MetaCoq Run (printInductive "list"). *)
MetaCoq Run (test <% list %>).

(* MetaCoq Run (printInductive "prod"). *)
MetaCoq Run (test <% prod %>).

Inductive prod4 (A B C D : Set) : Set :=
  | inj : A -> B -> C -> D -> prod4 A B C D.

MetaCoq Run (test <% prod4 %>).


(* ################################################# *)
(* 3. Mutual : NO / Parameters : NO / Indices : YES *)

Inductive vec : nat -> Set :=
| vnil    : vec 0
| vcons n : vec n -> vec (S n).

(* MetaCoq Run (printInductive "vec"). *)
(* Check vec_ind. *)
MetaCoq Run (test <% vec %>).

Inductive vec2 : nat -> bool -> Set :=
| vnil2     : vec2 0 true
| vcons2  n : vec2 n false.

MetaCoq Run (test <% vec2 %>).


(* ################################################# *)
(* 4. Mutual : NO / Parameters : YES / Indices : YES *)

Inductive vec3 (A : Set) : nat -> Set :=
| vnil3    : vec3 A 0
| vcons3 n : A -> vec3 A n -> vec3 A (S n).

MetaCoq Run (test <% vec3 %>).

Inductive vec4 (A B : Set) : nat -> bool -> Set :=
| vnil4 (a : A)    : vec4 A B 0 true
| vcons4 (b : B) n : vec4 A B n false.

MetaCoq Run (test <% vec4 %>).

(* Inductive eq (A:Type) (x:A) : A -> Prop :=
    eq_refl : x = x :>A

where "x = y :> A" := (@eq A x y) : type_scope.

MetaCoq Run (test <% eq %>). *)


(* ################################################# *)
(* 5. Mutual : YES / Parameters : NO / Indices : NO *)

Inductive teven : Prop :=
| tevenb : teven
| tevenS : todd -> teven
with
  todd : Prop :=
  | toddS : teven ->  todd.

(* MetaCoq Run (printInductive "teven"). *)
MetaCoq Run (test <% teven %>).

(* ################################################# *)
(* 6. Mutual : YES / Parameters : Yes / Indices : NO *)


(* ################################################# *)
(* 7. Mutual : YES / Parameters : NO / Indices : YES *)
Inductive even : nat -> Prop :=
  | even0   : even 0
  | evenS n : odd n -> even (S n)
with
  odd : nat -> Prop :=
  | oddS n : even n -> odd (S n).

Scheme even_odd_rec := Induction for even Sort Prop
  with odd_even_rec := Induction for odd Sort Prop.

Check even_odd_rec.

MetaCoq Run (test <% even %>).
MetaCoq Run (test <% odd %>).

(* ################################################# *)
(* 8. Mutual : YES / Parameters : Yes / Indices : YES *)