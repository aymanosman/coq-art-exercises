(* Exercise 5.6 *)

Theorem ex5_6_1 : forall A B C: Prop, A /\ (B /\ C) -> (A /\ B) /\ C.
Proof.
  intros A B C H.
  repeat apply conj.
  apply H.
  apply H.
  apply H.
Qed.

Theorem ex5_6_2 : forall A B C D : Prop, (A -> B) /\ (C -> D) /\ A /\ C -> B /\ D.
Proof.
  intros A B C D H.
  apply conj; repeat apply H.
Qed.

Theorem ex5_6_3 : forall A : Prop, ~(A /\ ~A).
Proof.
  intros A H.
  repeat apply H.
Qed.

Theorem ex5_6_4 : forall A B C : Prop, A \/ (B \/ C) -> (A \/ B) \/ C.
Proof.
  intros A B C H.
  apply (or_ind (A:=(A)) (B:=(B\/C))).
  intro a.
  repeat apply or_introl.
  assumption.
  intro b_or_c.
  apply (or_ind (A:=B) (B:=C)).
  intro b.
  apply or_introl.
  apply or_intror.
  assumption.
  intro c.
  repeat apply or_intror.
  assumption.
  assumption.
  assumption.
Qed.


Theorem ex5_6_4_with_exact : forall A B C : Prop, A \/ (B \/ C) -> (A \/ B) \/ C.
Proof.
  intros A B C H.
  exact (or_ind (fun a => (or_introl (or_introl a)))
                (fun b_or_c => or_ind (fun b => (or_introl (or_intror b)))
                                      (fun c => (or_intror c))
                                      b_or_c)
                H).
Qed.

Theorem ex5_6_4_with_cut : forall A B C : Prop, A \/ (B \/ C) -> (A \/ B) \/ C.
Proof.
  intros A B C H.
  cut (A -> (A \/ B) \/ C).
  intro H0.
  cut (B \/ C -> (A \/ B) \/ C).
  intro H1.
  apply (or_ind H0 H1).
  assumption.

  intro b_or_c.
  cut (B -> (A \/ B) \/ C).
  intro H2.
  cut (C -> (A \/ B) \/ C).
  intro H3.
  apply (or_ind H2 H3).
  assumption.

  intro c.
  repeat apply or_intror.
  assumption.

  intro b.
  apply or_introl.
  apply or_intror.
  assumption.

  intro a.
  repeat apply or_introl.
  assumption.
Qed.

Theorem ex5_6_4_with_assert : forall A B C : Prop, A \/ (B \/ C) -> (A \/ B) \/ C.
Proof.
  intros A B C H.
  assert (Ha : A -> (A \/ B) \/ C).
  intro a.
  repeat apply or_introl.
  assumption.

  assert (Hbc : B \/ C -> (A \/ B) \/ C).
  intro b_or_c.

  assert (Hb : B -> (A \/ B) \/ C).
  intro b.
  apply or_introl.
  apply or_intror.
  assumption.

  assert (Hc : C -> (A \/ B) \/ C).
  intro c.
  repeat apply or_intror.
  assumption.

  apply (or_ind Hb Hc).
  assumption.
  apply (or_ind Ha Hbc).
  assumption.
Qed.

Theorem ex5_6_4_with_elim : forall A B C : Prop, A \/ (B \/ C) -> (A \/ B) \/ C.
Proof.
  intros A B C H.
  elim H.
  intro a.
  repeat left; assumption.
  intro H0.
  elim H0.
  intro b.
  left; right; assumption.
  intro c.
  repeat right; assumption.
Qed.

Theorem ex5_6_4_with_intuition : forall A B C : Prop, A \/ (B \/ C) -> (A \/ B) \/ C.
Proof.
  intuition.
Qed.

Theorem ex5_6_5 : forall A : Prop, ~~(A \/ ~A).
Proof.
  unfold not.
  intros A H.
  apply H.
  apply or_intror.
  intro a.
  apply H.
  apply or_introl.
  assumption.
Qed.

Theorem ex5_6_6 : forall A B : Prop, (A \/ B) /\ ~A -> B.
Proof.
  intros A B H.
  elim H.
  intros H0 H1.
  elim H0.
  intro a.
  apply False_ind.
  apply H1.
  assumption.

  apply id.
Qed.