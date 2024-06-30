

(forall (A B : Set) (P : forall (H : nat) (H0 : bool), vec4 A B H H0 -> Prop),
 (forall a : A, P 0 true (vnil4 A B a)) ->
 (forall (b : B) (n : nat), P n false (vcons4 A B b n)) ->
 forall (H : nat) (H0 : bool) (x : vec4 A B H H0), P H H0 x)
