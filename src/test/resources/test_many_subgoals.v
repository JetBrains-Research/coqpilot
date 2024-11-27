Lemma one_subgoal : forall n:nat, 0 + n + 0 = n.
Proof.
    intros. admit.
Admitted.

Lemma two_subgoals : forall n:nat, n + 0 = n.
Proof.
    intros.
    induction n.
    admit. 
    admit.
Admitted.

Inductive MyType : Type :=
| First : MyType
| Second : MyType
| Third : MyType.

Theorem three_subgoals : forall t : MyType,
  (t = First) \/ (t = Second) \/ (t = Third).
Proof.
    intros t. destruct t.
    admit.
    admit.
    admit.
Admitted.