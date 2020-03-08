(* Exercise 5.7 Extra *)

(* Print excluded_middle_peirce_with_elim. *)
Check fun (excluded_middle : forall P : Prop, P \/ ~ P)
          (P Q : Prop)
          (H : (P -> Q) -> P) =>
        or_ind (id (A:=P))
               (fun H0 : ~ P =>
                  H (fun p : P =>
                       False_ind Q (H0 p)))
               (excluded_middle P).


(* Print excluded_middle_peirce_with_exact. *)
Check fun (excluded_middle : forall P : Prop, P \/ ~ P)
          (P Q : Prop)
          (H : (P -> Q) -> P) =>
        or_ind (fun p : P => p)
               (fun H0 : ~P =>
                  H (fun p : P =>
                       False_ind Q (H0 p)))
               (excluded_middle P).


(* Print excluded_middle_peirce. *)
Eval lazy zeta beta in
    fun (excluded_middle : forall P : Prop, P \/ ~ P)
        (P Q : Prop)
        (H : (P -> Q) -> P) =>
      let H0 : ~ P -> P := fun H0 : ~ P =>
                             H (fun p : P =>
                                  False_ind Q (H0 p))
      in
      (fun H1 : ~ P -> P =>
         or_ind (fun p : P => p)
                H1
                (excluded_middle P))
        H0.
