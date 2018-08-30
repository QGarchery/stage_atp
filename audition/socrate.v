Require Import SMTCoq.
Variable homme : Z -> bool.
Variable mortel : Z -> bool.
Variable Socrate : Z.
Infix "-->" := implb (at level 50).

Axiom hommes_mortels : forall h, homme h --> mortel h.
Axiom homme_Socrate : homme Socrate.
Add_lemmas hommes_mortels homme_Socrate.

Lemma mortel_Socrate : mortel Socrate.
Proof.
  verit.
Qed.  

