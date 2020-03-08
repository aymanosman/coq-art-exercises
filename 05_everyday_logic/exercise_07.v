(* Exercise 5.7 *)
(* Here are five statements that are often considered as characterizations
   of classical logic. Prove that these five propositions are equivalent. *)

Definition peirce := forall P Q : Prop, ((P -> Q) -> P) -> P.
Definition classic := forall P : Prop, ~~P -> P.
Definition excluded_middle := forall P : Prop, P \/ ~P.
Definition de_morgan_not_and_not := forall P Q : Prop, ~(~P /\ ~Q) -> P \/ Q.
Definition implies_to_or := forall P Q : Prop, (P -> Q) -> (~P \/ Q).

Theorem excluded_middle_peirce_with_elim : excluded_middle -> peirce.
Proof.
  unfold excluded_middle, peirce.
  intros excluded_middle P Q H.
  elim (excluded_middle P).
  apply id.
  intro H0.
  apply H.
  intro p.
  apply False_ind.
  apply H0.
  assumption.
Qed.

Theorem excluded_middle_peirce_with_exact : excluded_middle -> peirce.
Proof.
  unfold excluded_middle, peirce.
  intros excluded_middle P Q H.
  exact (or_ind (* (P:=P) *)
                (fun p => p)
                (fun H0 => (H (fun p => False_ind Q (H0 p))))
                (excluded_middle P)).
Qed.

Theorem excluded_middle_peirce : excluded_middle -> peirce.
Proof.
  unfold excluded_middle, peirce.
  intros excluded_middle P Q H.
  cut (~P -> P).
  intro H0.
  apply (or_ind (fun p => p) H0).
  apply excluded_middle.
  intro H1.
  apply H.
  intro p.
  apply False_ind.
  apply H1.
  assumption.
Qed.


Theorem peirce_implies_classic : peirce -> classic.
Proof.
  unfold peirce, classic.
  intros peirce P H.
  apply (peirce P False).
  intro H0.
  apply False_ind.
  apply H.
  intro p.
  apply H0.
  assumption.
Qed.

Theorem classic_implies_excluded_middle : classic -> excluded_middle.
Proof.
  unfold classic, excluded_middle.
  intros classic P.
  apply classic.
  intro H.
  apply H.
  right.
  intro p.
  apply H.
  left.
  assumption.
Qed.

Theorem excluded_middle_implies_to_or_with_exact :  excluded_middle -> implies_to_or.
Proof.
  unfold excluded_middle, implies_to_or.
  intros excluded_middle P Q H.
  exact (or_ind (fun p : P => or_intror (H p))
                (fun H0 : ~P => or_introl H0)
        (excluded_middle P)).
Qed.

Theorem excluded_middle_implies_to_or_with_elim :  excluded_middle -> implies_to_or.
Proof.
  unfold excluded_middle, implies_to_or.
  intros excluded_middle P Q H.
  elim (excluded_middle P).
  intro p.
  right.
  apply H.
  assumption.
  intro H0.
  left.
  assumption.
Qed.

Theorem excluded_middle_implies_to_or :  excluded_middle -> implies_to_or.
Proof.
  unfold excluded_middle, implies_to_or.
  intros excluded_middle P Q H.
  cut (P -> ~P \/ Q).
  intro H0.
  cut (~P -> ~P \/ Q).
  intro H1.
  apply (or_ind H0 H1).
  apply excluded_middle.
  apply or_introl.
  intro p.
  apply or_intror.
  apply H.
  assumption.
Qed.

Theorem implies_to_or_excluded_middle : implies_to_or -> excluded_middle.
Proof.
  unfold implies_to_or, excluded_middle.
  intros implies_to_or P.
  apply or_comm.
  apply (implies_to_or P P).
  apply id.
Qed.

Theorem implies_to_or_excluded_middle_with_exact : implies_to_or -> excluded_middle.
Proof.
  unfold implies_to_or, excluded_middle.
  intros implies_to_or P.
  exact (match (implies_to_or P P (fun p : P => p)) with
         | or_introl H => or_intror H
         | or_intror H => or_introl H
        end).
Qed.

Theorem implies_to_or_excluded_middle_with_elim : implies_to_or -> excluded_middle.
Proof.
  unfold implies_to_or, excluded_middle.
  intros implies_to_or P.
  elim (implies_to_or P P).
  intro H.
  apply or_intror.
  assumption.
  intro p.
  apply or_introl.
  assumption.
  apply id.
Qed.


Theorem classic_de_morgan_not_and_not : classic -> de_morgan_not_and_not.
  unfold classic, de_morgan_not_and_not.
  intros classic P Q H.
  apply classic.
  intro H0.
  apply H.
  apply conj.
  intro p.
  apply H0.
  apply or_introl.
  assumption.
  intro q.
  apply H0.
  apply or_intror.
  assumption.
Qed.

Theorem de_morgan_not_and_not_excluded_middle : de_morgan_not_and_not -> excluded_middle.
Proof.
  unfold de_morgan_not_and_not, excluded_middle.
  intros de_morgan_not_and_not P.
  apply de_morgan_not_and_not.
  intro H.
  apply H.
  intro p.
  apply proj1 in H.
  apply H.
  assumption.
Qed.

Theorem de_morgan_not_and_not_excluded_middle_with_assert : de_morgan_not_and_not -> excluded_middle.
Proof.
  unfold de_morgan_not_and_not, excluded_middle.
  intros de_morgan_not_and_not P.
  apply de_morgan_not_and_not.
  intro H.
  apply H.
  intro p.
  assert (H0 : ~P).
  apply H.
  apply H0.
  assumption.
Qed.
