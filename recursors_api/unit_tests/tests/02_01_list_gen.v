

(forall (A : Type) (P : list A -> Prop),
 P [] ->
 (forall (H : A) (H0 : list A), P (H :: H0)) -> forall x : list A, P x)
