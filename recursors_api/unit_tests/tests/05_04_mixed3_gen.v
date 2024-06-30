

(forall P : forall A B C D : Type, mixed3 A B C D -> Prop,
 (forall (A B C D : Type) (H : mixed3 A B C bool) (H0 : nat),
  P A B C D (mc31 A B C D H H0)) ->
 (forall (A B C D : Type) (H : mixed3 A B nat D) (H0 : nat),
  P A B C D (mc32 A B C D H H0)) ->
 (forall (A B C D : Type) (H : nat) (H0 : mixed3 A B bool D),
  P A B C D (mc33 A B C D H H0)) ->
 (forall (A B C D : Type) (H : mixed3 nat B C D) (H0 : mixed3 A B C D),
  P A B C D (mc34 A B C D H H0)) ->
 (forall (A B C D : Type) (H : mixed3 A nat C D) (H0 : mixed3 B A C D),
  P A B C D (mc35 A B C D H H0)) ->
 forall (A B C D : Type) (x : mixed3 A B C D), P A B C D x)
