

(forall (P : teven -> Prop) (P0 : todd -> Prop),
 P teven0 ->
 (forall H : todd, P (tevenS H)) ->
 (forall H : teven, P0 (toddS H)) -> forall x : todd, P0 x)
