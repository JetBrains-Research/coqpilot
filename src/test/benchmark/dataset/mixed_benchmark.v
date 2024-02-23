Theorem test_plus_1 : forall n:nat, 1 + n = S n.
Proof.
    auto.
Qed.

Theorem test_thr : forall n:nat, 0 + n = n.
Proof.
    admit.
Admitted.

Theorem add_comm : forall n m:nat, n + m = m + n.
Proof.
    admit.
Admitted.

Theorem add_comm_1 : forall n:nat, n + 1 = 1 + n.
Proof.
    admit.
Admitted.