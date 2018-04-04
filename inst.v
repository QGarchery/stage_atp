Lemma forall_inst n Q :
  Q = n 2 ->
  (forall x, n x >= 0) -> Q >= 0.

Proof.
  intros q H. rewrite q. auto.
Qed.

Parameter P : nat -> Prop.

Theorem dec_forallP :
  (forall x, P x) \/ ~(forall x, P x).

Proof.  
  assert (forall x, P x \/ ~ (P x)).
  admit.
  Admitted.
  


Lemma forall_inst2 Q : 
  Q = P 2 ->
  ~(forall x, P x) \/ Q.

Proof.
  intro q.
  destruct dec_forallP.
  -right. rewrite q. auto.
  -left. assumption.
Qed.







