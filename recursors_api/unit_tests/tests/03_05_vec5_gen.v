

(forall (A B : Set) (P : forall H H0 : nat, vec5 A B H H0 -> Prop),
 (forall a : A, P 0 0 (vnil5 A B a)) ->
 (forall (b : B) (n m : nat), P n m (vcons A B b n m)) ->
 forall (H H0 : nat) (x : vec5 A B H H0), P H H0 x)
