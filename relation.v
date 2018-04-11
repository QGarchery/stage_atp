Section Relation.
  Context {A : Type}.

  Variable R : A -> A -> Prop.

  Inductive star : A -> A -> Prop :=
  | zero a : star a a
  | next a b c : R a b ->
                 star b c ->
                 star a c.

  Inductive star_right : A -> A -> Prop :=
  | zer a : star_right a a
  | nex a b c : star_right a b ->
                R b c ->
                star_right a c.
  
  Lemma star_right_star a b:
        star_right a b ->
        star a b.

  Proof.
    intro sr. induction sr.
    -apply zero.
    -clear sr.
     induction IHsr.
     apply next with c.
     assumption. apply zero.
     apply next with b.
     assumption.
     now apply IHIHsr.
  Qed.     

  Lemma star_star_right a b:
        star a b ->
        star_right a b.

  Proof.
    intro s. induction s.
    -apply zer.
    -clear s.
     induction IHs.
     apply nex with a.
     apply zer. assumption.
     apply nex with b.
     now apply IHIHs.
     assumption.
  Qed.
     
  Lemma eq_stars a b :
    star a b <-> star_right a b.

  Proof.
    split; intro H.
    -now apply star_star_right.
    -now apply star_right_star.
  Qed.

  Inductive plus : A -> A -> Prop :=
  | def a b c : R a b ->
                star b c ->
                plus a c.
End Relation.



Section RelationProperties.
  Context {A : Type}.
  Variable R : A -> A -> Prop.
  
  Definition irreducible t :=
    forall a, ~ (R t a).
  
  Lemma irreducible_star t c :
    star R t c ->
    irreducible t ->
    t = c.

  Proof.
    intros t_c irrt.
    destruct t_c as [ | t b c r_t_b b_c].
    reflexivity.
    exfalso. now apply (irrt b).
  Qed.

  Definition sym a b := R a b \/ R b a.

  Definition congruent a b :=
    star sym a b.

  Lemma congr_symm a b :
    congruent a b -> congruent b a.

  Proof.
    intro congr_a_b.
    induction congr_a_b.
    -apply zero.
    -unfold congruent.
     apply eq_stars.
     apply nex with b.
     now apply eq_stars.
     unfold sym in *. intuition.
  Qed.
  
  Definition is_normal_form a t :=
    star R a t /\ irreducible t.

  Hypothesis confluent :
    forall up a b,
      star R up a ->
      star R up b ->
      exists bot,
        star R a bot /\ star R b bot.

  Lemma one_nf up t1 t2 :
    is_normal_form up t1 ->
    is_normal_form up t2 ->
    t1 = t2.

  Proof.
    intros [up_t1 irrt1] [up_t2 irrt2].
    destruct (confluent up t1 t2 up_t1 up_t2) as [bot [t1_bot t2_bot]].
    rewrite (irreducible_star t1 bot); trivial.
    now rewrite (irreducible_star t2 bot).
  Qed.

  Hypothesis terminating :
    forall a, exists t, is_normal_form a t.

  (* Fixpoint reduce a := *)
  (*   if irreducible a *)
  (*   then a *)
  (*   else reduce (one_step R a) *)
    
  Variable reduce : A -> A.
  
  Hypothesis reduce_spec :
    forall a, is_normal_form a (reduce a).

  Lemma rel_same_reduce a b :
    R a b -> reduce a = reduce b.

  Proof.
    intro r_a_b.
    apply (one_nf a (reduce a) (reduce b)).
    apply reduce_spec.
    destruct (reduce_spec b).
    split.
    -now apply next with b.
    -assumption.
  Qed.
    
  Lemma congr_iff_same_reduce a b:
    congruent a b <-> reduce a = reduce b.

  Proof.
    split; intro H.
    -induction H.
     reflexivity.
     destruct H; apply rel_same_reduce in H.
     now rewrite H.
     now rewrite <- H.
    -destruct (reduce_spec a) as [Ga H0].
     destruct (reduce_spec b) as [Gb H1].
     rewrite <- H in Gb.
     clear confluent reduce_spec H0 H1 H.
     induction Ga.
     +induction Gb.
      apply zero.
      apply congr_symm.
      apply congr_symm in IHGb.
      apply next with b.
      now left.
      apply IHGb.
     +apply next with b0.
      now left.
      now apply IHGa.
  Qed.
  
