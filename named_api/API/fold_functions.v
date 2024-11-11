From Coq Require Export List.
Export ListNotations.

(* 1. General Purposed Fold Functions
- fold_right_state : {A B X state} : (nat -> A -> state -> (X -> state -> B) -> B)
  -> list A -> state -> (list X -> state -> B) -> B
- fold_left_state : {A B X state} : (nat -> A -> state -> (X -> state -> B) -> B)
  -> list A -> state -> (list X -> state -> B) -> B
- fold_right_state_opt {A B X state} : (tp : nat -> A -> state -> (list X -> state -> B) -> B)
  -> list A -> state -> (list X -> state -> B) : B
- fold_left_state_opt {A B X state} : (tp : nat -> A -> state -> (list X -> state -> B) -> B)
  -> list A -> state -> (list X -> state -> B) : B

=> 2 / 3 / 4 variants

*)


(* 1.1 Fold_left and Fold_right *)
Definition fold_right_state {A B X state} (tp : nat -> A -> state -> (state -> X -> B) -> B)
  (l:list A) (s:state) (t : state -> list X -> B) : B :=
  let fix aux n ids1 l s t : B :=
    match l with
    | [] => t s (rev ids1)
    | a :: l => tp n a s (fun s id1 => aux (S n) (id1 :: ids1) l s t)
  end in
  aux 0 [] l s t.

  Definition fold_right_state2 {A B X Y state} (tp : nat -> A -> state -> (state -> X -> Y -> B) -> B)
  (l:list A) (s:state) (t : state -> list X -> list Y -> B) : B :=
  let fix aux n ids1 ids2 l s t : B :=
    match l with
    | [] => t s (rev ids1) (rev ids2)
    | a :: l => tp n a s (fun s id1 id2 => aux (S n) (id1 :: ids1) (id2 :: ids2) l s t)
  end in
  aux 0 [] [] l s t.

Definition fold_right_state3 {A B X Y Z state} (tp : nat -> A -> state -> (state -> X -> Y -> Z -> B) -> B)
  (l:list A) (s:state) (t : state -> list X -> list Y -> list Z -> B) : B :=
  let fix aux n ids1 ids2 ids3 l s t : B :=
    match l with
    | [] => t s (rev ids1) (rev ids2) (rev ids3)
    | a :: l => tp n a s (fun s id1 id2 id3 => aux (S n) (id1 :: ids1) (id2 :: ids2) (id3 :: ids3) l s t)
  end in
  aux 0 [] [] [] l s t.

Definition fold_left_state {A B X state} (tp : nat -> A -> state -> (state -> X -> B) -> B)
  (l:list A) (s:state) (t : state -> list X -> B) : B :=
  fold_right_state tp (rev l) s t.

Definition fold_left_state2 {A B X Y state} (tp : nat -> A -> state -> (state -> X -> Y -> B) -> B)
  (l:list A) (s:state) (t : state -> list X -> list Y -> B) : B :=
  fold_right_state2 tp (rev l) s t.

Definition fold_left_state3 {A B X Y Z state} (tp : nat -> A -> state -> (state -> X -> Y -> Z -> B) -> B)
  (l:list A) (s:state) (t : state -> list X -> list Y -> list Z -> B) : B :=
  fold_right_state3 tp (rev l) s t.

(* 1.2 Fold_right and Fold_left conditional *)
Definition fold_right_state_opt {A B X state} (tp : nat -> A -> state -> (state -> list X -> B) -> B)
  (l:list A) (s:state) (t : state -> list X -> B) : B :=
  let fix aux n ids1 l s t : B :=
    match l with
    | [] => t s (rev ids1)
    | a :: l => tp n a s (fun s fid1 => aux (S n) (fid1 ++ ids1) l s t)
  end in
  aux 0 [] l s t.

Definition fold_right_state_opt2 {A B X Y state} (tp : nat -> A -> state -> (state -> list X -> list Y -> B) -> B)
  (l:list A) (s:state) (t : state -> list X -> list Y -> B) : B :=
  let fix aux n ids1 ids2 l s t : B :=
    match l with
    | [] => t s (rev ids1) (rev ids2)
    | a :: l => tp n a s (fun s fid1 fid2 => aux (S n) (fid1 ++ ids1) (fid2 ++ ids2) l s t)
  end in
  aux 0 [] [] l s t.

Definition fold_right_state_opt3 {A B X Y Z state} (tp : nat -> A -> state -> (state -> list X -> list Y -> list Z -> B) -> B)
  (l:list A) (s:state) (t : state -> list X -> list Y -> list Z -> B) : B :=
  let fix aux n ids1 ids2 ids3 l s t : B :=
    match l with
    | [] => t s (rev ids1) (rev ids2) (rev ids3)
    | a :: l => tp n a s (fun s fid1 fid2 fid3 => aux (S n) (fid1 ++ ids1) (fid2 ++ ids2) (fid3 ++ ids3) l s t)
  end in
  aux 0 [] [] [] l s t.

Definition fold_right_state_opt4 {A B X Y Z W state} (tp : nat -> A -> state -> (state -> list X -> list Y -> list Z -> list W -> B) -> B)
  (l:list A) (s:state) (t : state -> list X -> list Y -> list Z -> list W -> B) : B :=
  let fix aux n ids1 ids2 ids3 ids4 l s t : B :=
    match l with
    | [] => t s (rev ids1) (rev ids2) (rev ids3) (rev ids4)
    | a :: l => tp n a s (fun s fid1 fid2 fid3 fid4 =>
          aux (S n) (fid1 ++ ids1) (fid2 ++ ids2) (fid3 ++ ids3) (fid4 ++ ids4) l s t)
  end in
  aux 0 [] [] [] [] l s t.

Definition fold_left_state_opt {A B X state} (tp : nat -> A -> state -> (state -> list X -> B) -> B)
  (l:list A) (s:state) (t : state -> list X -> B) : B :=
  fold_right_state_opt tp (rev l) s t.

Definition fold_left_state_opt2 {A B X Y state} (tp : nat -> A -> state -> (state -> list X -> list Y -> B) -> B)
  (l:list A) (s:state) (t : state -> list X -> list Y -> B) : B :=
  fold_right_state_opt2 tp (rev l) s t.

Definition fold_left_state_opt3 {A B X Y Z state} (tp : nat -> A -> state -> (state -> list X -> list Y -> list Z -> B) -> B)
  (l:list A) (s:state) (t : state -> list X -> list Y -> list Z -> B) : B :=
  fold_right_state_opt3 tp (rev l) s t.

Definition fold_right_state_op4t {A B X Y Z W state} (tp : nat -> A -> state -> (state -> list X -> list Y -> list Z -> list W -> B) -> B)
  (l:list A) (s:state) (t : state -> list X -> list Y -> list Z -> list W -> B) : B :=
  fold_right_state_opt4 tp (rev l) s t.

