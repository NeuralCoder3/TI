Require Import List.
Import ListNotations Bool.

Section DFA.
 Definition dec X := {X} + {~X}.
  Notation "'eq_dec' X" := (forall x y: X, dec (x = y)) (at level 70).

  Notation "x 'el' A" := (In x A) (at level 70).
  Notation "x 'nel' A" := (~ In x A) (at level 70).

  Definition state := nat.
  Definition action := bool.

  Hypothesis actionEq: eq_dec action.
  Hypothesis stateEq: eq_dec state.

  Definition s0 := 0.
  Definition s1 := 1.
  Definition s2 := 2.
  Definition s3 := 3.

  Definition stateBeq x y := if stateEq x y then true else false.
  Definition actionBeq x y := if actionEq x y then true else false.

  Notation "A × B" := (prod A B)(at level 71).
  Notation "a ∈ A" := (In a A)(at level 71).
  Notation "A ⊆ B" := (incl A B)(at level 71).

  Definition DFA := (list state×list action×(state->action->state)×state×list state).

  Definition word := list action.
  Implicit Type (Q:list state) (Σ:list action) (δ:state->action->state) (q:state) (f:list state) (w:word).

  Lemma inState q Q: dec(q el Q).
  Proof.
    apply in_dec. apply stateEq.
  Qed.

  Definition valid (a:DFA) : Prop :=
    match a with
      (Q,Σ,δ,q0,f) =>
      q0 el Q /\ f ⊆ Q /\
      forall a x, x el Q -> δ x a el Q
    end.

  Fixpoint parseAux f δ q0 w : bool :=
    match w with
      [] => if inState q0 f then true else false
    | c::cs => parseAux f δ (δ q0 c) cs
    end.

  Definition parse (d:DFA) w :=
    match d with
      (Q,Σ,δ,q0,f) => parseAux f δ q0 w
    end.

  Lemma stateEqEq x : stateBeq x x = true.
  Proof.
    unfold stateBeq.
    destruct stateEq;congruence.
  Qed.

  Goal forall (x:action), exists (d:DFA), forall (y:action), parse d [y] = true <-> x=y.
  Proof.
    intros.
    exists ([s0;s1;s2],[],(fun q1 a => if stateBeq q1 s0 && actionBeq a x then s1 else s2),s0,[s1]).
    intros y. cbn. rewrite stateEqEq. unfold actionBeq; destruct actionEq;cbn.
    all: destruct inState;split;auto;try congruence.
    - contradict n; now left.
    - intros _. exfalso. unfold s2,s1 in i. firstorder;congruence.
  Qed.

  Definition prodList {X Y:Type} (xs:list X) (ys:list Y) : list (X×Y) :=
    concat(map (fun x => map (fun y => (x,y)) ys) xs).

  Variable (goed:nat × nat->nat) (degoed:nat->nat × nat).
  Hypothesis (degoed_bij: forall n, goed(degoed n)=n).
  Hypothesis (goed_bij: forall n, degoed(goed n)=n).


  Definition boolDec X (H:dec X) := if H then true else false.

  Coercion boolDec : dec >-> bool.

  Lemma filter_Nin: forall (A : Type) (f : A -> bool) (x : A) (l : list A), x nel filter f l <-> x nel l \/ f x = false.
  Proof.
    intros. split;intros.
    - destruct f eqn: F.
      + left. contradict H.
        apply filter_In. now split.
      + now right.
    - destruct H.
      + contradict H.
        now apply filter_In in H as [].
      + intros []%filter_In. congruence.
  Qed.

  Lemma prodIn {X Y:Type} (a:X) (b:Y) (A:list X) (B:list Y):
    a el A -> b el B -> (a,b) el prodList A B.
  Proof.
    intros.
    induction A in H, B, H0 |- *;cbn.
    - destruct H.
    - destruct H as [-> | H].
      + apply in_app_iff. left. now apply in_map.
      + apply in_app_iff. right. now apply IHA.
  Qed.

  Definition injective {X Y:Type} (f:X->Y) := forall x y, f x=f y -> x = y.

  Lemma map_In {X Y:Type} (f:X->Y): injective f -> forall x xs, f x el map f xs -> x el xs.
  Proof.
    intros.
    induction xs;cbn in *.
    - exact H0.
    - destruct H0 as [->%H | H0].
      + now left.
      + right. now apply IHxs.
  Qed.

  Lemma injGoed: injective goed.
  Proof.
    intros x y H.
    rewrite <- goed_bij.
    rewrite <- goed_bij at 1.
    now rewrite H.
  Qed.

  Lemma injDegoed: injective degoed.
  Proof.
    intros x y H.
    rewrite <- degoed_bij.
    rewrite <- degoed_bij at 1.
    now rewrite H.
  Qed.

  Lemma prod_In {X Y:Type} (x:X) (y:Y) xs ys: (x,y) el prodList xs ys -> x el xs /\ y el ys.
  Proof.
    induction xs in ys |- *;cbn;intros H.
    - destruct H.
    - rewrite in_app_iff in H.
      destruct H.
      + clear IHxs. induction ys;cbn in *.
        * destruct H.
        * destruct H.
          -- injection H as -> ->.
             split;now left.
          -- apply IHys in H as [].
             destruct H; tauto.
      + destruct (IHxs ys).
        * exact H.
        * tauto.
  Qed.

  Goal forall (f:bool->bool->bool) (a b:DFA), valid a -> valid b -> exists (c:DFA), valid c /\ forall x, parse c x = f (parse a x) (parse b x).
  Proof.
    intros.
    unfold parse, valid in *.
    destruct a as [[[[Qa _ ] δa ] qa ] fa], b as [[[[Qb _ ] δb ] qb ] fb].
    pose (Qc := map goed (prodList Qa Qb)).
    pose (qc := goed (qa,qb)).
    pose (fc := filter (fun x => let (sa,sb) := degoed x in f (inState sa fa) (inState sb fb)) Qc).
    pose (δc := fun x σ => let (sa,sb) := degoed x in goed (δa sa σ, δb sb σ)).
    exists (Qc,
       [],
       δc,
       qc,
       fc
      ).
    destruct H as (?&?&?),H0 as (?&?&?).
    split.
    {
      repeat split.
      - now apply in_map,prodIn.
      - intros x F. subst fc.
        apply filter_In in F as [].
        trivial.
      - intros.
        unfold δc.
        destruct degoed eqn: F.
        unfold Qc.
        unfold Qc in H5.
        rewrite <- goed_bij in F. apply injDegoed in F.
        rewrite F in H5.
        apply map_In in H5.
        apply prod_In in H5 as [].
        apply in_map,prodIn.
        + now apply H2.
        + now apply H4.
        + apply injGoed.
    }
    intros x.
    revert qa qb H H0 qc.
    induction x;intros qa qb H H0 qc; cbn.
    - subst qc fc.
      + destruct (inState (goed _)) as [F0|F0].
        * apply filter_In in F0 as [H5 H6].
          rewrite goed_bij in H6. rewrite <- H6 at 1.
          repeat destruct inState;cbn;congruence.
        * apply filter_Nin in F0 as [H5|H5].
          -- contradict H5. now apply in_map,prodIn.
          -- rewrite goed_bij in H5. rewrite <-H5 at 1.
             repeat destruct inState;cbn;congruence.
    - unfold qc. unfold δc. rewrite goed_bij.
      fold δc.
      apply IHx.
      + now apply H2.
      + now apply H4.
  Defined.

  Inductive regex : Type :=
    empty | epsilon | act (a:action) | plus (a b:regex) | concat (a b:regex) | star (a:regex).

  Coercion act : action >-> regex.

  Definition language := word -> Prop.

  Fixpoint power (M:language) (n:nat) (xs:word) :=
    match n with
      O => xs=[]
    | S m => exists ys zs, M ys /\ power M m zs
    end.

  Fixpoint L (r:regex) : language :=
    match r with
      empty => fun _ => False
    | epsilon => fun xs => xs = []
    | act a => fun xs => xs=[a]
    | plus a b => fun xs => L a xs \/ L b xs
    | concat a b => fun xs => exists ys zs, xs=ys++zs /\ L a ys /\ L b zs
    | star a => fun xs => exists n, power (L a) n xs
    end.

  Lemma notInEmpty {X:Type} s (A B:X) : (if inState s [] then A else B) = B.
  Proof.
    destruct inState.
    - destruct i.
    - reflexivity.
  Qed.

  Lemma isInState {X:Type} s xs (A B:X) : (if inState s (s::xs) then A else B) = A.
  Proof.
    destruct inState.
    - reflexivity.
    - contradict n. now left.
  Qed.

  Hint Constructors regex.
  Hint Resolve L notInEmpty isInState.
  Hint Unfold power.

  Goal forall (r:regex), L (star r) [].
  Proof.
    intros r.
    now exists 0.
  Qed.

  Goal L empty <> L epsilon.
  Proof.
    intros H.
    enough(L empty [] ) by tauto.
    rewrite H. reflexivity.
  Qed.

  Goal forall (r:regex), exists (d:DFA), valid d /\ forall xs, parse d xs = true <-> L r xs.
  Proof.
    induction r.
    - unfold DFA.
      exists ([s0],[],(fun _ _ => s0),s0,[]).
      split.
      + repeat split;eauto with *.
      + intros xs. split.
        * induction xs;cbn.
          -- destruct inState;cbn in *;congruence.
          -- cbn in IHxs. now intros H%IHxs.
        * intros [].
  Admitted.


  (* Definition nat2bool (n:nat) := if n then false else true. *)
  (* Coercion nat2bool : nat >-> bool. *)

End DFA.
