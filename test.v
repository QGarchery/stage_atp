Require Import SMTCoq.




Lemma neg_neg (A : Prop) : A -> ~~A.

Proof.
  intros a na. now apply na.
Qed.








  


  