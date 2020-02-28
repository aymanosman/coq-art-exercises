(* Exercise 4.3 *)

Section A_declared.
  Variables (A:Set)(P Q:A->Prop)(R:A->A->Prop).

  Theorem all_perm : (forall a b:A, R a b) -> forall a b:A, R b a.
  Proof.
    intros H a b.
    apply H.
  Qed.

  Theorem all_imp_dist : (forall a:A, P a -> Q a) -> (forall a:A, P a) -> forall a:A, Q a.
  Proof.
    intros H H0 a.
    apply H.
    apply H0.
  Qed.


  Theorem all_delta : (forall a b:A, R a b)->forall a:A, R a a.
  Proof.
    intros H a.
    apply H.
  Qed.

End A_declared.

(* Exercise 4.5 *)

Theorem all_perm' : forall (A:Type) (P:A->A->Prop),
    (forall x y: A, P x y)
    -> forall x y:A, P y x.
Proof.
Admitted.

Theorem resolution :
  forall (A:Type)(P Q R S:A->Prop),
    (forall a:A, Q a -> R a -> S a)
    -> (forall b:A, P b -> Q b)
    -> (forall c:A, P c -> R c -> S c).
Proof.
Admitted.
