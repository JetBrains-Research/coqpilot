Theorem test : forall (A : Type) (P : A -> Prop) (x : A), P x -> P x.
Proof.
    admit.
Admitted.

Theorem test2 : forall (A : Type) (P : A -> Prop) (x : A), P x -> P x.
Proof.
    intros A P x H.
    admit.
Admitted.

Theorem test2nat1 : forall n : nat, n = 0 \/ n <> 0.
Proof.
  intros n.
  destruct n.
  - admit.
  - right.
  discriminate.
Admitted.

Theorem test2nat2 : forall n : nat, n = 0 \/ n <> 0.
Proof.
    intros n.
    destruct n.
    {
        admit.
    }
    {
        admit.
    }
Admitted.

Theorem test_thr : forall n:nat, 0 + n = n.
Proof.
    intros n. Print plus.
    admit.
    (* reflexivity. *)
Admitted.

Lemma test_thr1 : forall n:nat, 0 + n + 0 = n.
Proof.
    intros n. Print plus.
    admit.
    (* reflexivity. *)
Admitted.
