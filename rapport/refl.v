

Fixpoint plus (n1 : nat) (n2 : nat) :=
  match n1 with
  | 0 => n2
  | S n1' => S (plus n1' n2) end.

Lemma plus23 : plus 2 3 = 5.
Proof. exact (eq_refl). Qed.


