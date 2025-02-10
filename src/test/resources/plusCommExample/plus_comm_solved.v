Theorem plus_comm : forall n m : nat, n + m = m + n.
Proof.
  intros n m.
  induction n.
  - (* Base case: n = 0 *)
    auto.
  - (* Inductive case: 
    assume n + m = m + n, prove (S n) + m = m + (S n) *)
    simpl. rewrite IHn. rewrite <- plus_n_Sm. reflexivity.
Qed.
