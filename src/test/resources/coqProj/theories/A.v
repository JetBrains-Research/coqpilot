Fixpoint Test (n : nat) : bool :=
  match n with
  | 0 => true
  | 1 => false
  | S (S n') => Test n'
  end.

Fixpoint evenb (n : nat) : bool :=
    match n with
    | 0 => true
    | S n' => negb (evenb n')
    end.