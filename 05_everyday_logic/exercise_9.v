Section Exercise9.
  Variables (A : Set)
            (P Q : A -> Prop).

  Theorem theorem1_with_elim : (exists x : A, P x \/ Q x) -> (ex P) \/ (ex Q).
  Proof.
    intros H.
    elim H.
    intros a H0.
    elim H0.
    intro H1.
    left.
    exists a.
    assumption.
    intro H2.
    right.
    exists a.
    assumption.
  Qed.

  Theorem theorem1_without_cut : (exists x : A, P x \/ Q x) -> ex P \/ ex Q.
  Proof.
    intros H.
    apply ex_ind
      with (P := fun x => P x \/ Q x)
           (P0 := ex P \/ ex Q)
      in H.
    assumption.
    intros x H0.
    apply or_ind
          with (P := ex P \/ ex Q)
          in H0.
    apply H0.
    intro H1.
    apply or_introl.
    apply ex_intro with x.
    assumption.
    intro H2.
    apply or_intror.
    apply ex_intro with x.
    assumption.
  Qed.

  Theorem theorem1 : (exists x : A, P x \/ Q x) -> ex P \/ ex Q.
  Proof.
    intro H.
    cut (forall x : A, P x \/ Q x -> ex P \/ ex Q).
    intro H0.
    apply (ex_ind H0 H).
    intros x H1.
    cut (P x -> ex P \/ ex Q).
    intro H2.
    cut (Q x -> ex P \/ ex Q).
    intro H3.
    apply (or_ind H2 H3 H1).
    intro H4.
    apply or_intror.
    apply ex_intro with x.
    assumption.
    intro H5.
    apply or_introl.
    apply ex_intro with x.
    assumption.
  Qed.

  Theorem theorem1_with_exact : (exists x : A, P x \/ Q x) -> ex P \/ ex Q.
  Proof.
    intro H.
    exact
      (ex_ind
         (fun (x : A)
              (H0 : P x \/ Q x)
          => or_ind (fun H1 => or_introl (ex_intro _ x H1))
                    (fun H1 => or_intror (ex_intro _ x H1))
                    H0)
         H).
  Qed.

  Theorem theorem2_with_exact : ex P \/ ex Q -> (exists x: A, P x \/ Q x).
  Proof.
    intro H.
    exact
      (or_ind (fun H0 : ex P => ex_ind (fun x H1 => ex_intro _ x (or_introl H1))
                                       H0)
              (fun H0 : ex Q => ex_ind (fun x H1 => ex_intro _ x (or_intror H1))
                                       H0)
              H).

  Theorem theorem2_with_elim : ex P \/ ex Q -> (exists x: A, P x \/ Q x).
  Proof.
    intro H.
    elim H.
    intro H0.
    elim H0.
    intros x H1.
    exists x.
    left; assumption.
    intro H2.
    elim H2.
    intros x H3.
    exists x.
    right; assumption.
  Qed.

  Theorem theorem2 : ex P \/ ex Q -> (exists x: A, P x \/ Q x).
  Proof.
    intro H.
    cut (ex P -> exists x : A, P x \/ Q x).
    intro H0.
    cut (ex Q -> exists x : A, P x \/ Q x).
    intro H1.
    apply (or_ind H0 H1 H).
    intro H2.
    cut (forall x : A, Q x -> exists x : A, P x \/ Q x).
    intro H3.
    apply (ex_ind H3 H2).
    intros x H4.
    apply ex_intro with x.
    apply or_intror.
    assumption.
    intro H5.
    cut (forall x : A, P x -> exists x : A, P x \/ Q x).
    intro H6.
    apply (ex_ind H6 H5).
    intros x H7.
    apply ex_intro with x.
    apply or_introl.
    assumption.
  Qed.

  Theorem theorem3_with_exact : (exists x : A, (forall R : A -> Prop, R x)) -> 2 = 3.
  Proof.
    intro H.
    exact
      (ex_ind (fun (x : A)
                   (H0 : forall R : A -> Prop, R x)
               => False_ind (2=3) (H0 (fun _ => False)))
              H).
  Qed.

  Theorem theorem3 : (exists x : A, (forall R : A -> Prop, R x)) -> 2 = 3.
  Proof.
    intro H.
    cut (forall x : A, (forall R : A -> Prop, R x) -> 2 = 3).
    intros H0.
    apply (ex_ind H0 H).
    intros x H1.
    apply False_ind.
    apply H1 with (R := fun _ => False).
  Qed.

  Theorem theorem3_with_elim : (exists x : A, (forall R : A -> Prop, R x)) -> 2 = 3.
  Proof.
    intro H.
    elim H.
    intros x H0.
    elim (H0 (fun _ => False)).
  Qed.

  Theorem theorem4_with_elim : (forall x : A, P x) -> ~(exists y : A, ~ P y).
  Proof.
    intros H H0.
    elim H0.
    intros x H1.
    apply H1.
    apply H.
  Qed.


  Theorem theorem4 : (forall x : A, P x) -> ~(exists y : A, ~ P y).
  Proof.
    intros H H0.
    cut (forall x : A, ~ P x -> False).
    intro H1.
    apply (ex_ind H1 H0).
    intros x H2.
    apply H2.
    apply H.
  Qed.

End Exercise9.
