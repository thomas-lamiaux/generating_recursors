

(forall (A : Set) (P : forall H : nat, vec3 A H -> Prop),
 P 0 (vnil3 A) ->
 (forall (n : nat) (H : A) (H0 : vec3 A n), P (S n) (vcons3 A n H H0)) ->
 forall (H : nat) (x : vec3 A H), P H x)
