(* Exercise 5.13 *)
(* It is possible to define negation on top of our notion of
   falsehood: *)

Definition my_True : Prop := forall P : Prop, P -> P.
Definition my_False : Prop := forall P : Prop, P.

Definition my_I : my_True := fun P p => p.
Definition my_False_ind := forall P : Prop, my_False -> P.

Definition my_not (P : Prop) : Prop := P -> my_False.

(* Redo Exercise 5.3 using `my_False` and `my_not` instead of `False` and `not`. *)

Theorem theorem1 : my_not my_False.
Proof.
  unfold my_not, my_False.
  intros H P.
  apply H.
Qed.

Theorem theorem2 : forall P : Prop, my_not (my_not (my_not P)) -> my_not P.
Proof.
  unfold my_not, my_False.
  intros P H p P0.
  apply H.
  intros H0 P1.
  apply H0; assumption.
Qed.

Theorem theorem3 : forall P Q : Prop, my_not (my_not (my_not P)) -> P -> Q.
Proof.
  unfold my_not, my_False.
  intros P Q H p.
  apply H.
  intros H0 P0.
  apply H0; assumption.
Qed.

Theorem theorem4 : forall P Q : Prop, (P -> Q) -> my_not Q -> my_not P.
Proof.
  unfold my_not, my_False.
  intros P Q H H0 p P0.
  apply H0, H; assumption.
Qed.

Theorem theorem5 : forall P Q R : Prop, (P -> Q) -> (P -> my_not Q) -> P -> R.
Proof.
  unfold my_not, my_False.
  intros P Q R H H0 p.
  apply H0, H; assumption.
Qed.
