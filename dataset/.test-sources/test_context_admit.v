Theorem contextTestBefore : forall (A : Type) (P : A -> Prop) (x : A), P x -> P x.
Proof.
    auto.
Qed.

Theorem admittedTestBefore : forall (A : Type) (P : A -> Prop) (x : A), P x -> P x.
Proof.
    auto.
Admitted.

Theorem unprovedTestBefore : forall (A : Type) (P : A -> Prop) (x : A), P x -> P x.
Proof.
    admit.
Admitted.

Theorem test : forall (A : Type) (P : A -> Prop) (x : A), P x -> P x.
Proof.
    admit. (* Test Target *)
Admitted.

Theorem contextTestAfter : forall (A : Type) (P : A -> Prop) (x : A), P x -> P x.
Proof.
    auto.
Qed.

Theorem admittedTestAfter : forall (A : Type) (P : A -> Prop) (x : A), P x -> P x.
Proof.
    auto.
Admitted.

Theorem unprovedTestAfter : forall (A : Type) (P : A -> Prop) (x : A), P x -> P x.
Proof.
    admit.
Admitted.
