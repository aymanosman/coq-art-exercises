(* Exercise 5.14 *)

Section leibniz.
  Set Implicit Arguments.
  Unset Strict Implicit.
  Variable A : Set.

  Definition leibniz (a b : A) : Prop :=
    forall P : A -> Prop, P a -> P b.

  Require Import Relations.

  (* Theorem leibniz_sym : symmetric A leibniz. *)

  Theorem leibniz_refl : reflexive A leibniz.
  Proof.
    unfold reflexive, leibniz.
    intros x P H.
    assumption.
  Qed.

  Theorem leibniz_trans : transitive A leibniz.
    unfold transitive, leibniz.
    intros x y z H H0 P H1.
    apply H0, H; assumption.
  Qed.

  Theorem leibniz_equiv : equiv A leibniz.
    unfold  equiv, leibniz.
    unfold reflexive, transitive, symmetric.
    repeat apply conj.
    intros x P H; assumption.
    intros x y z H H0 P H1.
    apply H0, H; assumption.
    intros x y H P H0.

    cut (x=y).
    intro H1.
    rewrite H1; assumption.
    pattern y.
    apply H.
    apply eq_refl.
  Qed.

  Theorem leibniz_least_reflexive :
    forall R : relation A, reflexive A R -> inclusion A leibniz R.
  Proof.
    unfold relation, reflexive, inclusion, leibniz.
    intros R H x y H0.
    pattern x.
    apply H0, H.
  Qed.

  Theorem leibniz_eq : forall a b : A, leibniz a b -> a = b.
  Proof.
    unfold leibniz.
    intros a b H.
    pattern a.
    apply H, eq_refl.
  Qed.

  Theorem eq_leibniz : forall a b : A, a = b -> leibniz a b.
  Proof.
    unfold leibniz.
    intros a b H P H0.
    rewrite <- H.
    assumption.
  Qed.

  Theorem leibniz_ind :
    forall (x : A) (P : A -> Prop), P x -> forall y : A, leibniz x y -> P y.
  Proof.
    unfold leibniz.
    intros x P H y H0.
    apply H0.
    assumption.
  Qed.

  Unset Implicit Arguments.

End leibniz.
