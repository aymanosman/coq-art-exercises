(* Exercise 3.2 *)
(* Only use `assumption` `intro(s)` and `apply` *)

Section Minimal_propositional_logic.
  Variables P Q R T: Prop.

  Lemma id_P : P -> P.
  Proof.
    intro p; assumption.
  Qed.

  Lemma id_PP : (P -> P) -> (P -> P).
  Proof.
    intro H; assumption.
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
    Undo 3.
    (* in one step *)
    apply H; assumption.
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
    Undo 3.
    (* in one step *)
    apply H; assumption.
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
    Undo 5.
    (* in one step *)
    apply H2;[apply H0 | apply H1];assumption.
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

End Minimal_propositional_logic.


(* Exercise 3.3 *)
(* Redo exercise 3.2, using as many tacticals as needed to perform
 each proof in only one complex step*)
