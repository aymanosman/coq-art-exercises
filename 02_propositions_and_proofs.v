(* Exercise 3.2 *)
(* Only use `assumption` `intro(s)` and `apply` *)

Section Minimal_propositional_logic.
  Variables P Q R T: Prop.

  Lemma id_P : P -> P.
  Admitted.

  Lemma id_PP : (P -> P) -> (P -> P).
  Admitted.

  Lemma imp_trans : (P -> Q) -> (Q -> R) -> P -> R.
  Admitted.

  Lemma imp_perm : (P -> Q -> R) -> (Q -> P -> R).
  Admitted.

  Lemma ignore_Q : (P -> R) -> P -> Q -> R.
  Admitted.

  Lemma delta_imp : (P -> P -> Q) -> P -> Q.
  Admitted.

  Lemma delta_impR : (P -> Q) -> (P -> P -> Q).
  Admitted.

  Lemma diamond : (P -> Q) -> (P -> R) -> (Q -> R -> T) -> P -> T.
  Admitted.

  Lemma weak_peirce : ((((P -> Q) -> P) -> P) -> Q) -> Q.
  Admitted.

End Minimal_propositional_logic.
