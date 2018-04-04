Require Import SMTCoq.

Lemma square_pos (x : Z) :
  Z.geb (x * x) 0 = true.


Proof.
  destruct x;
  unfold Z.geb;
  now simpl.
Qed.

Print square_pos.

