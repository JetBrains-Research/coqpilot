Theorem test : forall (A : Type) (P : A -> Prop) (x : A), P x -> P x.
Proof.
    (* auto. *)
    admit.
Admitted.

Theorem test2 : forall (A : Type) (P : A -> Prop) (x : A), P x -> P x.
Proof.
    intros A P x H.
    (* auto. *)
    admit.
Admitted.

Theorem test2nat : forall n : nat, n = 0 \/ n <> 0.
Proof.
    intros n.
    destruct n.
    {
        (* auto. *)
        admit.
    }
    {
        admit.
    }
Admitted.

Theorem test_thr : forall n:nat, 0 + n = n.
Proof.
    intros n. Print plus.
    (* auto. *)
    admit.
Admitted.

Lemma test_thr1 : forall n:nat, 0 + n + 0 = n.
Proof.
    intros n. Print plus.
    (* now rewrite <- plus_n_O. *)
    admit.
Admitted.