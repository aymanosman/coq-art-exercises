(* Exercise 5.12 *)

Definition my_True : Prop := forall P : Prop, P -> P.
Definition my_False : Prop := forall P : Prop, P.

Theorem my_I' : my_True.
Proof.
  intros P p; assumption.
Qed.

Theorem my_False_ind' : forall P : Prop, my_False -> P.
Proof.
  intros P F; apply F.
Qed.

Print my_I'.
Print my_False_ind'.

Definition my_I : my_True := fun P p => p.
Definition my_False_ind := forall P : Prop, my_False -> P.

