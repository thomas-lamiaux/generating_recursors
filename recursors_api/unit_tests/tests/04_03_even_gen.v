

(forall (P : forall H : nat, even H -> Prop)
   (P0 : forall H : nat, odd H -> Prop),
 P 0 even0 ->
 (forall (n : nat) (H : odd n), P (S n) (evenS n H)) ->
 (forall (n : nat) (H : even n), P0 (S n) (oddS n H)) ->
 forall (H : nat) (x : even H), P H x)
