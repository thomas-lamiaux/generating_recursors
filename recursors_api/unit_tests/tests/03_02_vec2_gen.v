

(forall P : forall (H : nat) (H0 : bool), vec2 H H0 -> Prop,
 P 0 true vnil2 ->
 (forall (n : nat) (H : vec2 n false), P (S n) true (vcons2 n H)) ->
 forall (H : nat) (H0 : bool) (x : vec2 H H0), P H H0 x)
