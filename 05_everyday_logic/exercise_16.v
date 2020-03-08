(* Exercise 5.16 *)

Definition my_le (n p : nat) :=
  forall P : nat -> Prop, P n -> (forall q : nat, P q -> P (S q)) -> P p.

Lemma my_le_n : forall n : nat, my_le n n.
Proof.
  unfold my_le.
  intros n P H H0.
  assumption.
Qed.

Lemma my_le_S : forall n p : nat, my_le n p -> my_le n (S p).
Proof.
  unfold my_le.
  intros n p H P H0 H1.
  apply H1.
  apply H.
  assumption.
  intros q H2.
  apply H1.
  assumption.
Qed.

Lemma my_le_le : forall n p : nat, my_le n p -> n <= p.
Proof.
  unfold my_le.
  intros n p H.
  pattern p.
  apply H.
  apply le_n.
  intros q H0.
  apply le_S.
  assumption.
Qed.
