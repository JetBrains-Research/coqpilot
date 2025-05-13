Section Globals.

  Variable A : Type.
  Variable x y : A.
  Hypothesis Hxy : x = y.

  Theorem test : x = y.
  Proof.
    apply Hxy.
  Qed.

End Globals.