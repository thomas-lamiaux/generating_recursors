

(forall (A : Type) (P : forall B C : Type, mixed1 A B C -> Prop),
 (forall B C : Type, P B C (mc11 A B C)) ->
 (forall (B C : Type) (H : mixed1 A nat C), P B C (mc12 A B C H)) ->
 forall (B C : Type) (x : mixed1 A B C), P B C x)
