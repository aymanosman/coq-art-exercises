(* Exercise 5.10 *)
(* In a first step, one should only use the tactics `rewrite`, `pattern`, `intros`,
   `apply`, or `reflexivity`, excluding all automatic tactics. However, the following
   theorems from the `Arith` library can be used:

   plus_comm : forall n m : nat, n+m = m+n
   plus_assoc : forall n m p : nat, n+(m+p) = n+m+p *)

Require Import Arith.

Theorem plus_permute2 : forall n m p : nat, n+m+p = n+p+m.
Proof.
  intros n m p.
  rewrite <- plus_assoc.
  rewrite plus_comm with m p.
  rewrite plus_assoc.
  apply f_equal.
  apply eq_refl.
Qed.
