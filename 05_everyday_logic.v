(* Exercise 5.3 *)

Lemma ex1 : ~False.
Proof.
  intro H.
  assumption.
Qed.

Theorem ex2 : forall P:Prop, ~~~P->~P.
Proof.
  intros P H.
  intro p.
  apply H.
  intro q.
  apply q.
  assumption.
Qed.

Theorem ex3 : forall P Q: Prop, ~~~P->P->Q.
Proof.
  intros P Q H p.
  elim H.
  intro H0.
  apply H0.
  assumption.
Qed.

Theorem ex4 : forall P Q: Prop, (P -> Q) -> ~Q -> ~P.
Proof.
  intros P Q H H0 p.
  apply H0.
  apply H.
  assumption.
Qed.

Theorem ex5 : forall P Q R: Prop, (P->Q)->(P->~Q)->P->R.
Proof.
  intros P Q R H H0 p.
  elim H0.
  assumption.
  apply H.
  assumption.
Qed.