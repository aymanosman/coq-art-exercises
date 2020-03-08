(* Exercise 5.11 *)
(* Prove the following theorem, first by a direct use of `eq_ind`,
   then with the `rewrite` tactic: *)

Theorem eq_trans_with_exact : forall (A: Type) (x y z : A), x = y -> y = z -> x = z.
Proof.
  intros A x y z H H0.
  exact (eq_ind y _ H _ H0).
Qed.

Theorem eq_trans : forall (A: Type) (x y z : A), x = y -> y = z -> x = z.
Proof.
  intros A x y z H H0.
  apply eq_ind with y; assumption.
Qed.

Theorem eq_trans_with_rewrite : forall (A: Type) (x y z : A), x = y -> y = z -> x = z.
Proof.
  intros A x y z H H0.
  rewrite H.
  assumption.
Qed.
