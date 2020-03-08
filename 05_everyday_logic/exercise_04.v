(* Exercise 5.4 *)

Definition dyslexic_imp := forall P Q : Prop, (P -> Q) -> (Q -> P).
Definition dyslexic_contrap := forall P Q : Prop, (P -> Q) -> (~P -> ~Q).

Theorem dyslexic_imp_is_false : ~dyslexic_imp.
Proof.
  unfold not.
  unfold dyslexic_imp.
  intros dyslexic_imp.
  apply (dyslexic_imp False True).
  intro false.
  apply False_ind.
  assumption.
  apply I.
Qed.

Theorem dyslexic_contrap_is_false : ~dyslexic_contrap.
Proof.
  unfold not.
  unfold dyslexic_contrap.
  intros dyslexic_contrap.
  apply (dyslexic_contrap False True).
  intro false.
  apply False_ind.
  assumption.
  intro false.
  assumption.
  apply I.
Qed.