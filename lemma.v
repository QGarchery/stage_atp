Require Import SMTCoq.

Lemma squarepos :
  forall x : Z,
    Bool.eqb (Z.geb (x * x) 0) true.

Proof.
  intro x. destruct x; simpl; reflexivity.
Qed.

