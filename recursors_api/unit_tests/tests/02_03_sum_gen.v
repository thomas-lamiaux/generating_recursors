

(forall (A B : Type) (P : A + B -> Prop),
 (forall H : A, P (inl H)) ->
 (forall H : B, P (inr H)) -> forall x : A + B, P x)
