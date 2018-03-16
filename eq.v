Lemma Leibniz (A : Type):
  forall (x : A) y (P : A -> Prop), eq x y -> P x -> P y.

Proof.
  intros. now apply eq_rect with x.
Qed.
  
  Set Printing All.
  Print eq.
  Print eq_rect.
  About nat_rec.
  Print nat.
  Check isFalse.