(* Exercise 5.1 *)
(* Redo Exercise 3.2 given on page 58, but with closed statements,
 in other words, statements where the propositional variables are not the
 pre-declared variables P, Q, R, but the universally quantified variables.*)

Lemma id_P : forall P : Prop, P -> P.
Proof.
  intros P p.
  assumption.
Qed.

Lemma id_PP : forall P : Prop, (P -> P) -> (P -> P).
Proof.
  intros P H.
  assumption.
Qed.

Lemma imp_trans : forall P Q R : Prop, (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros P Q R H H' p.
  apply H'.
  apply H.
  assumption.
Qed.

Lemma imp_perm : forall P Q R : Prop, (P -> Q -> R) -> (Q -> P -> R).
Proof.
  intros P Q R H q p.
  apply H.
  assumption.
  assumption.
Qed.

Lemma ignore_Q : forall P Q R : Prop, (P -> R) -> P -> Q -> R.
Proof.
  intros P Q R H p q.
  apply H.
  assumption.
Qed.

Lemma delta_imp : forall P Q : Prop, (P -> P -> Q) -> P -> Q.
Proof.
  intros P Q H p.
  apply H.
  assumption.
  assumption.
Qed.

Lemma delta_impR : forall P Q : Prop, (P -> Q) -> (P -> P -> Q).
Proof.
  intros P Q H p0 p1.
  apply H.
  assumption.
Qed.

Lemma diamond : forall P Q R S T : Prop, (P -> Q) -> (P -> R) -> (Q -> R -> T) -> P -> T.
Proof.
  intros P Q R S T H0 H1 H2 p.
  apply H2.
  apply H0.
  assumption.
  apply H1.
  assumption.
Qed.

Lemma weak_peirce : forall P Q : Prop, ((((P -> Q) -> P) -> P) -> Q) -> Q.
Proof.
  intros P Q H.
  apply H.
  intros H1.
  apply H1.
  intro p.
  apply H.
  intro H2.
  assumption.
Qed.