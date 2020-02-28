(* Exercise 5.3 *)

Lemma ex1 : ~False.
Proof.
  Admitted.
Qed.

Theorem ex2 : forall P:Prop, ~~~P->~P.
Proof.
  Admitted.
Qed.

Theorem ex3 : forall P Q: Prop, ~~~P->P->Q.
Proof.
  Admitted.
Qed.

Theorem ex4 : forall P Q: Prop, (P -> Q) -> ~Q -> ~P.
Proof.
  Admitted.
Qed.

Theorem ex5 : forall P Q R: Prop, (P->Q)->(P->~Q)->P->R.
Proof.
  Admitted.
Qed.
