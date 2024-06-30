

(forall P : nat -> Prop,
 P 0 -> (forall H : nat, P (S H)) -> forall x : nat, P x)
