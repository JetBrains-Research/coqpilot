From CP Require Import A.

Theorem test_admitted : forall n : nat, evenb (S n) = negb (evenb n).
Proof.
    admit.
Admitted.