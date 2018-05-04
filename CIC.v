Section Leibniz.
  Variable A : Type.
  Definition eq (x y : A) :=
    forall P : A -> Prop, P x -> P y.

  Lemma eq_intro x :
    eq x x.
  Proof.
    now intros P Px.
  Qed.

  Lemma eq_elim t u:
    eq t u -> forall B : A -> Prop, B t ->
    B u.
  Proof.    
    intros eqtu B Bt.
    now apply eqtu.
  Qed.
  
  Lemma eq_sym x y :
    eq x y -> eq y x.

  Proof.
    intro eqxy.
    apply (eqxy (fun z => eq z x)).
    now intros P Px.
  Qed.
End Leibniz.  



  
Section Peano.

  Variable N : Type.
  Variable z : N.
  Variable S : N -> N.

  Variable le : N -> N -> Prop.
  Variable lez : forall x : N, le z x.
  Variable leS : forall x y : N, le x y -> le (S x) (S y).
  
  Lemma lesszz : le z z.
  Proof.
    exact (lez z).
  Qed.

  Lemma lessSzSz : le (S z) (S z).
  Proof.
    exact (leS z z lesszz).
  Qed.



  Variable ind : forall P : N -> Prop,
      P z -> (forall x : N, P x -> P (S x)) -> forall x : N, P x.

  Lemma le_refl : forall x : N, le x x.

  Proof.
    exact (ind (fun x => le x x) lesszz (fun x => leS x x)).
  Qed.

End Peano.


Inductive le : nat -> nat -> Prop :=
  lez x: le 0 x
| leS x y: le x y -> le (S x) (S y).

Inductive RT {A : Type} (R : A -> A -> Prop) : A -> A -> Prop :=
  RTrefl x: RT R x x
| RTR x y: R x y -> RT R x y
| RTtran x y z: RT R x z -> RT R z y -> RT R x y.

Lemma le_ref x :
  le x x.
Proof.
  induction x.
  apply lez.
  now apply leS.
Qed.
  
Lemma le_trans x y z:
  le x y -> le y z -> le x z.

Proof.  
  revert y z.
  induction x.
  +intros. apply lez.
  +intros y z leSxy leyz.
   inversion leSxy.
   rewrite <- H1 in *.
   clear x0 H H1 y.
   inversion leyz.
   rewrite <- H2 in *.
   clear H H2 x0 z leSxy leyz.
   apply (IHx y0 y H0) in H1.
   now apply leS.
Qed.
   
Lemma le_is_RTsucc x y:
  le x y <-> RT (fun x y => y = S x) x y.

Proof.  
  split; intro H.

  -induction H.
   +induction x.
    apply RTrefl.
    apply RTtran with x.
    assumption.
    now apply RTR.
   +clear H.
    induction IHle.
    *apply RTrefl.
    *apply RTR. now rewrite H.
    *now apply RTtran with (S z).
  -induction H.
   apply le_ref.
   rewrite H.
   clear H y. induction x.
   apply lez.
   now apply leS.
   now apply le_trans with z.
Qed.

Print le_is_RTsucc.


    
    