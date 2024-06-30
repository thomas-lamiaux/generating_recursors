

(forall P : bnat -> Prop,
 P bO ->
 (forall (H H0 : bnat) (H1 : bool), P (bS H H0 H1)) -> forall x : bnat, P x)
