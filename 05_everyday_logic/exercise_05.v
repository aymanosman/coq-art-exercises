(* Exercise 5.5 *)

Theorem ex5_5 : forall (A: Set) (a b c d : A), a=c \/ b=c \/ c=c \/ d=c.
Proof.
  intros A a b c d.
  apply or_intror.
  apply or_intror.
  apply or_introl.
  apply eq_refl.
Qed.