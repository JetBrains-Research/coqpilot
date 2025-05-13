Theorem test : forall (A : Type) (P : A -> Prop) (x : A), P x -> P x.
Proof.
    auto.
Qed.
