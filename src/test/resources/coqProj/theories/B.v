From CP Require Import A.

Theorem test : forall n : nat, evenb (S n) = negb (evenb n).
Proof.
    intros n. simpl. reflexivity.
Qed.