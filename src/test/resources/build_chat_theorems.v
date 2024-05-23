Theorem plus : forall n:nat, 1 + n = S n.
Proof.
    auto.
Qed.

Theorem plus_assoc : forall a b c, a + (b + c) = a + b + c.
Proof.
    intros.
    induction a.
        reflexivity.
        simpl. rewrite IHa. reflexivity.
Qed.

Theorem test : forall (A : Type) (P : A -> Prop) (x : A), P x -> P x.
Proof.
    admit.
Admitted.