

(forall P : forall n : nat, nu_vec n -> Prop,
 (forall n : nat, P n (vnil_pa n)) ->
 (forall (n : nat) (H : nu_vec (S n)), P n (vcons_pa n H)) ->
 forall (n : nat) (x : nu_vec n), P n x)
