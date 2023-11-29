Theorem test_1 : forall n:nat, 0 + n = n.
Proof.
    intros n. constructor.
Qed.

Lemma test_2 : forall n:nat, 0 + n = n.
Proof.
    intros n. constructor.
Qed.

Definition test_3 : forall n:nat, 0 + n = n.
Proof.
    intros n. constructor.
Qed.

Definition test_4 : forall n:nat, 0 + n = n.
Proof.
    intros n. constructor.
Defined.

(* This one is not yet parsed. Is ignored bacause it does not contain Proof. *)
Definition test_5 : forall n:nat, 0 + n = n.
    intros n. constructor.
Defined.

Theorem test_6 : forall n:nat, 0 + n = n.
Proof.
    intros n. constructor.
Admitted.

Definition test_7 : forall n:nat, 0 + n = n.
Proof.
    intros n. constructor.
Admitted.