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


(* Exercise 5.2 *)
(* Using tactics, redo the proofs of Exercise 4.5 *)
Theorem all_perm' : forall (A : Type) (P : A -> A -> Prop),
    (forall x y : A, P x y)
    -> forall x y : A, P y x.
Proof.
  intros A P H x y.
  apply H.
Qed.

Theorem resolution : forall (A : Type) (P Q R S : A -> Prop),
    (forall a : A, Q a -> R a -> S a)
    -> (forall b : A, P b -> Q b)
    -> (forall c : A, P c -> R c -> S c).
Proof.
  intros A P Q R S H H0 c pc rc.
  apply H.
  apply H0.
  assumption.
  assumption.
Qed.

(* Exercise 5.3 *)
(* Find the proofs that can be done without `False_ind`. Show how the
   corresponding theorems can be seen as simple applications of more general
   theorems from minimal propositional logic.*)

Lemma ex1 : ~False.
Proof.
  intro H.
  assumption.
Qed.

Theorem ex2 : forall P : Prop, ~~~P -> ~P.
Proof.
  intros P H p.
  apply H.
  intro H0.
  apply H0.
  assumption.
Qed.

Theorem ex3 : forall P Q : Prop, ~~~P -> P -> Q.
Proof.
  intros P Q H p.
  apply False_ind.
  apply H.
  intro H0.
  apply H0.
  assumption.
Qed.

Theorem ex4 : forall P Q : Prop, (P -> Q) -> ~Q -> ~P.
Proof.
  intros P Q H H0 p.
  apply H0.
  apply H.
  assumption.
Qed.

Theorem ex5 : forall P Q R : Prop, (P -> Q) -> (P -> ~Q) -> P -> R.
Proof.
  intros P Q R H H0 p.
  apply False_ind.
  apply H0.
  assumption.
  apply H.
  assumption.
Qed.

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

(* Exercise 5.5 *)

Theorem ex5_5 : forall (A: Set) (a b c d : A), a=c \/ b=c \/ c=c \/ d=c.
Proof.
  intros A a b c d.
  apply or_intror.
  apply or_intror.
  apply or_introl.
  apply eq_refl.
Qed.

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
  (* exact (or_ind (fun a => (or_introl (or_introl a))) *)
  (*               (fun b_or_c => or_ind (fun b => (or_introl (or_intror b))) *)
  (*                                     (fun c => (or_intror c)) *)
  (*                                     b_or_c) *)
  (*               H). *)
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

