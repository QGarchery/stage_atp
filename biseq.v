Section biseq.
  Variable Scalars : Set.
  Variable Points : Set.
  Variable Lines : Set.

  Variable eq : Scalars -> Scalars -> Prop.
  Variable In : Points -> Lines -> Prop.
  Variable d : Points -> Points -> Scalars.
  Variable b : Points -> Points -> Lines.

  Hypothesis b_def :
    forall x y z, In x (b y z) <-> eq (d x y) (d x z).

  Hypothesis eq_trans :
    forall x y z, (eq x y /\ eq y z) -> eq x z.

  Lemma biseq_triangle :
    forall w x y z,
      (In w (b x y) /\ In w (b y z)) ->
      In w (b x z).

  Proof.
    intros w x y z H. destruct H as [Hxy Hyz].
    apply b_def.
    apply eq_trans with (d w y).
    now split; apply b_def.
  Qed.

End biseq.

Print biseq_triangle.



