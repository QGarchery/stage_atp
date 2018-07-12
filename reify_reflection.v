Require Import Bool.

Inductive AndTree :=
  And (_ _: AndTree)
| Bool (_ : bool).

Fixpoint eval (t : AndTree) :=
  match t with
  | And t1 t2 => eval t1 && eval t2
  | Bool n => n 
  end.

Fixpoint append t1 t2 :=
  match t1 with
  | Bool n => And t1 t2
  | And t11 t12 => append t11 (append t12 t2)
  end.

Fixpoint peigne (t : AndTree) :=
  match t with
  | Bool n => t
  | And t1 t2 => let t1' := peigne t1 in
                 let t2' := peigne t2 in
                 append t1' t2'
  end.

Inductive eqt : AndTree -> AndTree -> Prop :=
| refl t : eqt t t
| sym t1 t2 : eqt t1 t2 -> eqt t2 t1
| assoc t1 t2 t3: eqt (And t1 (And t2 t3)) (And (And t1 t2) t3)
| congru ta1 ta2 tb1 tb2 : eqt ta1 tb1 -> eqt ta2 tb2 ->
                           eqt (And ta1 ta2) (And tb1 tb2)
| trans t1 t2 t3 : eqt t1 t2 -> eqt t2 t3 -> eqt t1 t3.

Lemma eqt_is_eq t1 t2:
  eqt t1 t2 -> eval t1 = eval t2.
Proof.
  intro eq12. induction eq12; simpl.
  -reflexivity.
  -auto.
  -apply andb_assoc.
  -rewrite IHeq12_1.
   now rewrite IHeq12_2.
  -now rewrite IHeq12_1.
Qed.   

Lemma append_correct t1 t2:
  eqt (append t1 t2) (And t1 t2).
Proof.
  revert t2. induction t1; intro t2; simpl.
  -eapply trans. apply IHt1_1. eapply trans. eapply congru.
   apply refl. apply IHt1_2. apply assoc.
  -apply refl.
Qed.

Lemma peigne_correct t:
  eqt t (peigne t).

Proof.
  apply sym. induction t; simpl.
  -eapply trans. apply append_correct. now apply congru.
  -apply refl.
Qed.

Ltac reify A :=  match A with 
  | andb ?X ?Y => let rx := reify X in
                  let ry := reify Y in
                  constr:(And rx ry)
  | ?X => constr:(Bool X) end.

Ltac peignify :=
  match goal with
  | [ |- ?A = ?B] =>
    let a := reify A in
    let b := reify B in
    change A with (eval a);
    change B with (eval b);
    rewrite (eqt_is_eq a _ (peigne_correct a));
    rewrite (eqt_is_eq b _ (peigne_correct b));
    simpl
  end.

Lemma peigne4 b1 b2 b3 b4:
  (b1 && b2) && (b3 && b4) = b1 && ((b2 && b3) && b4).

Proof.
  peignify. reflexivity.
Qed.  

Print peigne4.





