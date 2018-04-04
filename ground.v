Require Import Bool.

Inductive F : Set :=
| Bottom : F
| Var : nat -> F
| Or : F -> F -> F.


Inductive ground : F -> Prop :=
| Ground_bottom : ground Bottom
| Ground_or f1 f2: ground f1 ->
                   ground f2 ->
                   ground (Or f1 f2).



Fixpoint ground_dec f : bool :=
  match f with
  | Bottom => true
  | Var _ => false
  | Or f1 f2 => andb (ground_dec f1) (ground_dec f2)
  end.

Lemma ground_dec_correct f : ground_dec f = true -> ground f.

Proof.
  intro. induction f; simpl in *.
  -apply Ground_bottom.
  -apply False_ind. now apply diff_false_true.
  -apply andb_true_iff in H.
   destruct H. apply Ground_or.
   now apply IHf1.
   now apply IHf2.
Qed.

Lemma ground_ororor :
  ground (Or (Or (Or Bottom Bottom) Bottom) (Or Bottom (Or (Or Bottom Bottom) Bottom))).

Proof.  
  exact (ground_dec_correct (Or (Or (Or Bottom Bottom) Bottom) (Or Bottom (Or (Or Bottom Bottom) Bottom))) (eq_refl _)).
Qed.

Print ground_dec_correct.


Definition x : bool.
  exact false.
Defined.


Lemma xisfalse: x = false.
Proof.
  now unfold x.
Qed.  





