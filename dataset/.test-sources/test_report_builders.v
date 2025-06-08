Theorem only_auto_th1 : forall (A : Type) (P : A -> Prop) (x : A), P x -> P x.
Proof.
    auto.
Qed.

Theorem only_auto_th2 : forall (A : Type) (P : A -> Prop) (x : A), P x -> P x.
Proof.
    auto.
Qed.

Theorem excluded_by_options : forall (A : Type) (P : A -> Prop) (x : A), P x -> P x.
Proof.
    auto.
Qed.

Theorem auto_or_reflexivity_th : forall n:nat, 0 + n = n.
Proof.
    reflexivity.
Qed.

Inductive mybool : Type :=
  | MyTrue
  | MyFalse.

Theorem only_inversion_th : MyTrue <> MyFalse.
Proof. 
    inversion 1.
Qed.

Theorem hard_th : forall n m:nat, n + m = m + n.
Proof.
    intros n m.   
    induction n.   
    - simpl. rewrite <- plus_n_O. reflexivity.   
    - simpl. rewrite IHn. rewrite <- plus_n_Sm. reflexivity.
Qed.
