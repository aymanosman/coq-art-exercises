(* Exercise 4.3 *)

Section A_declared.
  Variables (A:Set)(P Q:A->Prop)(R:A->A->Prop).

  Theorem all_perm : (forall a b:A, R a b) -> forall a b:A, R b a.
  Proof.
  Admitted.

  Theorem all_imp_dist : (forall a:A, P a -> Q a) -> (forall a:A, P a) -> forall a:A, Q a.
  Proof.
  Admitted.


  Theorem all_delta : (forall a b:A, R a b)->forall a:A, R a a.
  Proof.
  Admitted.

End A_declared.
