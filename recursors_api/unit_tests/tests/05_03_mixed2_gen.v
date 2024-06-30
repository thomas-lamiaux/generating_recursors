

(forall P : forall A B C : Type, mixed2 A B C -> Prop,
 (forall (A B C : Type) (H : mixed2 A bool C), P A B C (mc21 A B C H)) ->
 (forall (A B C : Type) (H : mixed2 nat B C), P A B C (mc22 A B C H)) ->
 forall (A B C : Type) (x : mixed2 A B C), P A B C x)
