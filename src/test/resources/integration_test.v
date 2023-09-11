Theorem test_thr : forall n:nat, 0 + n = n.
Proof.
    intros n. Print plus.
    reflexivity.
Qed.

Lemma test_thr1 : forall n:nat, 0 + n + 0 = n.
Proof.
    intros n. Print plus.
    rewrite <- plus_n_O.
    reflexivity.
Qed.