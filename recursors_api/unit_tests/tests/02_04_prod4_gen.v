

(forall (A B C D : Set) (P : prod4 A B C D -> Prop),
 (forall (H : A) (H0 : B) (H1 : C) (H2 : D), P (cst A B C D H H0 H1 H2)) ->
 forall x : prod4 A B C D, P x)
