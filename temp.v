Lemma double_inv f :
  (forall n, exists x, n = f (x))->
  exists y, f (f (y)) = 3.


Proof.
  intro.
  pose (g := fun x : nat => 3).
  destruct (H 3) as [x H3].
  destruct (H x) as [x0 Hx].
  rewrite Hx in H3.
  symmetry in H3.
  now exists x0.
Qed.

Print double_inv.

Print list.





