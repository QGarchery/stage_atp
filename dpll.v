
Require Import List Bool ZArith.
Import ListNotations.
Local Open Scope Z_scope.

Inductive pair {A B : Type} :=
  | P (a : A) (b : B) : pair.

Definition fst {A B : Type} : @pair A B -> A :=
  fun p => match p with P a b => a end.

Definition snd {A B : Type} : @pair A B -> B :=
  fun p => match p with P a b => b end.

Section dpll.
  Variable Atom : Set.
  Hypothesis eq_atom : Atom -> Atom -> bool.
  
  Definition Literal := @pair Atom bool.
  Definition neg : Literal -> Literal :=
    fun l => match l with P a b => P a (negb b) end.

  Lemma neg_neg l : neg (neg l) = l.
  Proof.
    now destruct l; destruct b.
  Qed.
  
  Definition a_l (a : Atom) : Literal := P a false.
  Coercion a_l : Atom >-> Literal.

  Definition Guess := @pair Literal bool.

  Definition l_g (l : Literal) : Guess := P l false.
  Coercion l_g : Literal >-> Guess.

  Definition atom (g : Guess) : Atom :=
    fst (fst g).

  Definition is_neg (g : Guess) : bool :=
    snd (fst g).

  Definition is_guessed (g : Guess) : bool :=
    snd g.

  Definition eq_guess (g1 g2 : Guess) : bool :=
    if eqb (is_guessed g1) (is_guessed g2)
    then if eqb (is_neg g1) (is_neg g2)
         then eq_atom (atom g1) (atom g2)
         else false
    else false.
  
  Definition Clause := list Literal.

  Definition Formula := list Clause.

  Definition Guesses := list Guess.
  
  Inductive State := Ok : Guesses -> State | FailState.

  Definition gs_s (m : Guesses) :=
    Ok m.
  Coercion gs_s : Guesses >-> State.
  
  Fixpoint val (l : Literal) (gs : Guesses) : option bool :=
    match gs with
    | [] => None
    | g :: t => if eq_atom (atom g) (atom l)
                then Some (eqb (is_neg g) (is_neg l))
                else val l t
    end.

  
  Fixpoint sat (c : Clause) (gs : Guesses) : option bool :=
    match c with
    | [] => Some false
    | l :: c' => match sat c' gs with
                   None => match val l gs with
                             None => None
                           | Some bl => if bl
                                        then Some true
                                        else None end
                 | Some bc => if bc
                              then Some true
                              else match val l gs with
                                     None => None
                                   | Some bl => if bl
                                                then Some true
                                                else Some false end end end.

  Definition eq_opt (o1 o2 : option bool) : bool :=
    match o1 with
      None => match o2 with
              | Some _ => false
              | None => true end
    | Some b1 => match o2 with
                   None => false
                 | Some b2 => eqb b1 b2
                 end
    end.

  Fixpoint rem (l : Literal) (c : Clause) :=
    match c with
    | [] => []
    | h :: t => if eq_guess l h
                then t
                else h :: rem l t
    end.

  
  Fixpoint one_has_prop {A : Type} (p : A -> Prop) (l : list A) : Prop :=
    match l with
    | [] => False
    | h :: t => p h \/ one_has_prop p t
    end.

  Lemma has_prop_split A p l:
    @one_has_prop A p l ->
    exists l1 l2 x, l = l1 ++ (x :: l2) /\ p x.

  Proof.
    induction l; intros.
    -destruct H.
    -destruct H. exists [], l, a.
     now split; simpl.
     apply IHl in H. destruct H as [l1 H]. destruct H as [l2 H].
     destruct H as [x H]. destruct H.
     exists (a::l1), l2, x.
     split. rewrite H. apply app_comm_cons.
     assumption.
  Qed.

  Lemma get_one A p l:
    @one_has_prop A p l ->
    exists x, In x l /\ p x.

  Proof.
    intro.
    apply has_prop_split in H.
    destruct H. destruct H. destruct H. destruct H.
    exists x1. split.
    rewrite H. apply in_app_iff. right.
    now left. assumption.
  Qed.

  Lemma has_prop_app A p l1 l2 :
    @one_has_prop A p (l1 ++ l2) <->
    @one_has_prop A p l1 \/ @one_has_prop A p l2.

  Proof.
    induction l1; intros.
    -simpl in *.
     intuition.
    -rewrite <- app_comm_cons.
     simpl. rewrite IHl1. intuition.
  Qed.

  Lemma has_prop_spec A p l :
    @one_has_prop A p l <->
    exists x, In x l /\ p x.

  Proof.
    split; intro.
    now apply get_one.
    destruct H. destruct H.
    apply in_split in H.
    destruct H. destruct H. rewrite H.
    apply has_prop_app. right. now left.
  Qed.
     
  (* Fixpoint one_is_true {A : Type} (p : A -> bool) (l : list A) : bool := *)
  (*   match l with *)
  (*   | [] => false *)
  (*   | h :: t => p h || one_is_true p t *)
  (*   end. *)

  Lemma eq_opt_dec (o1 o2 : option bool) :
    o1 = o2 \/ ~ (o1 = o2).

  Proof.
    destruct o1; destruct o2; try destruct b; try destruct b0;
      intuition; right; intro; discriminate H.
  Qed.

  Inductive transition (f : Formula) : State -> State -> Prop :=
  | UnitPropagate c l m:
      In c f -> In l c ->
      sat (rem l c) m = Some false ->
      val l m = None ->
      transition f m (Ok ((l_g l) :: m))
  | PureLiteral l m:
      one_has_prop (In l) f ->
      ~ one_has_prop (In (neg l)) f ->
      eq_opt (val l m) None = true ->
      transition f m (Ok ((l_g l)::m))
  | Decide l m:
      one_has_prop (In l) f \/
      one_has_prop (In (neg l)) f ->
      eq_opt (val l m) None = true ->
      transition f m (Ok ((P l true) :: m))
  | Fail c m :
      In c f ->
      sat c m = Some false ->
      ~ one_has_prop (fun x => is_guessed x = true) m ->
      transition f m FailState
  | Backtrack l m (n : Guesses) c :
      sat c (n ++ ((P l true) :: m)) = Some false ->
      ~ one_has_prop (fun x => is_guessed x = true) m ->
      transition f (Ok (n ++ ((P l true) :: m)))
                 (Ok ((P (neg l) false) :: m)).

  Lemma sat_spec c gs:
    (sat c gs = None <->
     one_has_prop (fun x => val x gs = None) c /\
     ~ one_has_prop (fun x => val x gs = Some true) c) /\
    (sat c gs = Some true <->
     one_has_prop (fun x => val x gs = Some true) c) /\
    (sat c gs = Some false <->
     ~ one_has_prop (fun x => val x gs = None) c /\
     ~ one_has_prop (fun x => val x gs = Some true) c).
    

  Proof.
    induction c.
    -simpl. intuition; auto; try discriminate H.
    -destruct IHc. destruct H0.
     simpl.
     destruct_with_eqn (sat c gs).
     destruct_with_eqn b.
     +assert (G := eq_refl (Some true)).
      apply H0 in G.
      intuition.
     +destruct_with_eqn (val a gs).
      destruct_with_eqn b0.
      intuition. discriminate H5.
      intuition.
      assert (G:= eq_refl (Some false)).
      apply H1 in G.
      destruct G.
      split. split; intro. split. now left.
      intro. destruct H5. discriminate H5.
      now apply H3. reflexivity.
      split. split; intro. discriminate H4.
      destruct H4. discriminate H4.
      exfalso. now apply H3.
      split; intro. discriminate H4.
      destruct H4. exfalso. apply H4. now left.
     +destruct_with_eqn (val a gs).
      destruct_with_eqn b.
      intuition. discriminate H5. discriminate H5.
      intuition. discriminate H8. discriminate H7.
      intuition.
  Qed.      

  Lemma equal_false b :
    b = false <-> ~(b = true).
  Proof.
    destruct b; intuition.
  Qed.
         
  Lemma nf_is_complete f gs:
    ~ (exists m', transition f (Ok gs) m') ->
    forall l, one_has_prop (In l) f \/ one_has_prop (In (neg l)) f ->
              eq_opt (val l gs) None = false.

  Proof.
    intros. rewrite equal_false. intro.
    apply H. exists (Ok ((P l true) :: gs)).
    now apply Decide.
  Qed.
     
  Lemma nf f gs:
    ~ (exists m', transition f (Ok gs) m') ->
    forall c, In c f -> sat c gs = Some true.
  Proof.
    intros.
    destruct_with_eqn (one_is_true is_guessed gs).
    -
    -destruct_with_eqn (sat c gs).
     destruct_with_eqn b.
     +reflexivity.
     +exfalso. apply H. exists FailState. now apply Fail with c.
     +assert (G :=sat_spec c gs).
      destruct G. apply H1 in Heqo.
      destruct Heqo. exfalso.
      

    
End dpll.


Print transition.



Lemma one_transition :
  transition Z Zeq_bool
             [[P 1 false; P 2 false]; [P 3 true; P 4 false]]
             (Ok _ [P (P 1 true) false])
             (Ok _ [P (P 2 false) false; P (P 1 true) false]).
Proof.
  eapply UnitPropagate.
  simpl. now left.
  simpl. right. now left.
  now simpl.
  now simpl.
Qed.


    

  
  

      

  
  

  

  

  
  
  
    

    

  
  