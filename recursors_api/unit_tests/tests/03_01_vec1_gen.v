

(forall P : forall H : nat, vec1 H -> Prop,
 P 0 vnil1 ->
 (forall (n : nat) (H : vec1 n), P (S n) (vcons1 n H)) ->
 forall (H : nat) (x : vec1 H), P H x)
