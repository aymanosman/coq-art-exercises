(* Exercise 5.15 *)

Definition my_True : Prop := forall P : Prop, P -> P.
Definition my_False : Prop := forall P : Prop, P.

Definition my_I : my_True := fun P p => p.
Definition my_False_ind := forall P : Prop, my_False -> P.

Definition my_not (P : Prop) : Prop := P -> my_False.

Definition my_and (P Q : Prop) :=
  forall R : Prop, (P -> Q -> R) -> R.

Definition my_or (P Q : Prop) :=
  forall R : Prop, (P -> R) -> (Q -> R) -> R.

Definition my_ex (A : Set) (P : A -> Prop) :=
  forall R : Prop, (forall x : A, P x -> R) -> R.

Theorem theorem1 : forall P Q : Prop, my_and P Q -> P.
Proof.
  unfold my_and.
  intros P Q H.
  apply H; intros; assumption.
Qed.

Theorem theorem2 : forall P Q : Prop, my_and P Q -> Q.
Proof.
  unfold my_and.
  intros P Q H.
  apply H; intros; assumption.
Qed.

Theorem theorem3 : forall P Q R : Prop, (P -> Q -> R) -> my_and P Q -> R.
Proof.
  unfold my_and.
  intros P Q R H H0.
  apply H0; assumption.
Qed.

Theorem theorem4 : forall P Q : Prop, P -> my_or P Q.
Proof.
  unfold my_or.
  intros P Q p R Hleft Hright.
  apply Hleft; assumption.
Qed.

Theorem theorem5 : forall P Q : Prop, Q -> my_or P Q.
Proof.
  unfold my_or.
  intros P Q p R Hleft Hright.
  apply Hright; assumption.
Qed.

Theorem theorem6 : forall P Q R : Prop, (P -> R) -> (Q -> R) -> my_or P Q -> R.
Proof.
  unfold my_or.
  intros P Q R H H0 H1.
  apply H1; assumption.
Qed.

Theorem theorem7 : forall P : Prop, my_or P my_False -> P.
Proof.
  unfold my_or, my_False.
  intros P H.
  apply H.
  apply id.
  intro H0.
  apply H0.
Qed.

Theorem theorem8 : forall P Q : Prop, my_or P Q -> my_or Q P.
Proof.
  unfold my_or.
  intros P Q H R H0 H1.
  apply H; assumption.
Qed.

Theorem theorem9 : forall (A : Set) (P : A -> Prop) (a : A), P a -> my_ex A P.
Proof.
  unfold my_ex.
  intros A P a H R H0.
  apply H0 with a; assumption.
Qed.

Theorem theorem10 : forall (A : Set) (P : A -> Prop), my_not (my_ex A P) -> forall a : A, my_not (P a).
Proof.
  unfold my_not, my_ex, my_False.
  intros A P H a H0 Q.
  apply H.
  intros R H1.
  apply H1 with a; assumption.
Qed.
