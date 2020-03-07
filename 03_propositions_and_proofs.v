(* Exercise 3.2 *)
(* Only use `assumption` `intro(s)` and `apply` *)

Section Minimal_propositional_logic.
  Variables P Q R T: Prop.

  Lemma id_P : P -> P.
  Proof.
    intro p.
    assumption.
  Qed.

  Lemma id_PP : (P -> P) -> (P -> P).
  Proof.
    intro H.
    assumption.
  Qed.

  Lemma imp_trans : (P -> Q) -> (Q -> R) -> P -> R.
  Proof.
    intros H H' p.
    apply H'.
    apply H.
    assumption.
  Qed.

  Lemma imp_perm : (P -> Q -> R) -> (Q -> P -> R).
  Proof.
    intros H q p.
    apply H.
    assumption.
    assumption.
  Qed.

  Lemma ignore_Q : (P -> R) -> P -> Q -> R.
  Proof.
    intros H p q.
    apply H.
    assumption.
  Qed.

  Lemma delta_imp : (P -> P -> Q) -> P -> Q.
  Proof.
    intros H p.
    apply H.
    assumption.
    assumption.
  Qed.

  Lemma delta_impR : (P -> Q) -> (P -> P -> Q).
  Proof.
    intros H p0 p1.
    apply H.
    assumption.
  Qed.

  Lemma diamond : (P -> Q) -> (P -> R) -> (Q -> R -> T) -> P -> T.
  Proof.
    intros H0 H1 H2 p.
    apply H2.
    apply H0.
    assumption.
    apply H1.
    assumption.
  Qed.

  Lemma weak_peirce : ((((P -> Q) -> P) -> P) -> Q) -> Q.
  Proof.
    intros H.
    apply H.
    intros H1.
    apply H1.
    intro p.
    apply H.
    intro H2.
    assumption.
  Qed.



  (* Exercise 3.3 *)
  (* Redo exercise 3.2, using as many tacticals as needed to perform
 each proof in only one complex step*)

  Lemma id_P' : P -> P.
  Proof.
    intro p; assumption.
  Qed.

  Lemma id_PP' : (P -> P) -> (P -> P).
  Proof.
    intro H; assumption.
  Qed.

  Lemma imp_trans' : (P -> Q) -> (Q -> R) -> P -> R.
  Proof.
    intros H H' p; apply H'; apply H; assumption.
  Qed.

  Lemma imp_perm' : (P -> Q -> R) -> (Q -> P -> R).
  Proof.
    intros H q p; apply H; assumption.
  Qed.

  Lemma ignore_Q' : (P -> R) -> P -> Q -> R.
  Proof.
    intros H p q; apply H; assumption.
  Qed.

  Lemma delta_imp' : (P -> P -> Q) -> P -> Q.
  Proof.
    intros H p; apply H; assumption.
  Qed.

  Lemma delta_impR' : (P -> Q) -> (P -> P -> Q).
  Proof.
    intros H p0 p1; apply H; assumption.
  Qed.

  Lemma diamond' : (P -> Q) -> (P -> R) -> (Q -> R -> T) -> P -> T.
  Proof.
    intros H0 H1 H2 p; apply H2;[apply H0 | apply H1];assumption.
  Qed.

  Lemma weak_peirce' : ((((P -> Q) -> P) -> P) -> Q) -> Q.
  Proof.
    intros H;
      apply H; intros H1; apply H1; intro p; apply H; intro H2; assumption.
  Qed.


  (* Exercise 3.5 *)
  (* Perform the same proof without using `cut` and compare both
 approaches and both proof terms *)

  Section section_for_cut_example.
    Hypotheses (H : P -> Q)
               (H0 : Q -> R)
               (H1 : (P -> R) -> T -> Q)
               (H2 : (P -> R) -> T).

    (*
    Theorem cut_example : Q.
    Proof.
      cut (P -> R).
      intro H3.
      apply H1;[assumption | apply H2; assumption].
      intro p; apply H0; apply H; assumption.
    Qed.
     *)

    Theorem without_cut : Q.
    Proof.
      apply H1.
      intro p; apply H0; apply H; assumption.
      apply H2.
      intro p; apply H0; apply H; assumption.
    Qed.

  End section_for_cut_example.

End Minimal_propositional_logic.
