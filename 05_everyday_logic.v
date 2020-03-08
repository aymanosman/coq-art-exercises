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

