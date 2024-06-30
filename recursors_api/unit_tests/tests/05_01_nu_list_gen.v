

(forall P : forall A : Type, nu_list A -> Prop,
 (forall A : Type, P A (nu_nil A)) ->
 (forall (A : Type) (H : nu_list (A × A)), P A (nu_cons A H)) ->
 forall (A : Type) (x : nu_list A), P A x)
