

(forall (A B : Type) (P : A × B -> Prop),
 (forall (H : A) (H0 : B), P (H, H0)) -> forall x : A × B, P x)
