Theorem test : forall (A : Type) (P : A -> Prop) (x : A), P x -> P x.
Admitted.

Theorem test2nat : forall n : nat, n = 0 \/ n <> 0.
Proof.
  intros n.
  destruct n.
  - admit.
  - admit.
Admitted.