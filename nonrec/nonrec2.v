Require Import Program.
From Coq Require Import Arith Lia List.
Import ListNotations Nat.


Lemma size_induction X (f : X -> nat) (p : X -> Type) :
  (forall x, (forall y, f y < f x -> p y) -> p x) -> forall x, p x.
Proof.
  intros H x. apply H.
  enough (G : forall n y, f y < n -> p y) by apply G.
  intros n. induction n; intros y Hy.
  - exfalso. lia.
  - apply H. intros z HZ. apply IHn. lia.
Defined.

Lemma complete_induction (p : nat -> Type) :
  (forall x, (forall y, y < x -> p y) -> p x) -> forall x, p x.
Proof.
  apply (size_induction nat (fun n => n)).
Defined.


Open Scope nat.
Notation "x == y" := (Nat.eqb x y)(at level 71).
Ltac inv H := inversion H; subst; clear H.

Definition var := nat.

Inductive ifP :=
  wCon (n:var) (c:nat)
| wAdd (i j k:var)
| wSub (i j k:var)
| wIf (i:var) (P1: ifP) (* if equal 0 *)
| wSeq (P1 P2 : ifP).

Definition state := var -> nat.
Definition propState := var -> nat*nat.

Definition update {X} (x:var) (c:X) (s:nat->X) : (nat -> X) :=
  fun y => if x==y then c else s y.


Inductive ϕ (S:state) : ifP -> state -> Prop :=
  semAdd i j k: ϕ S (wAdd i j k) (update i (S j + S k) S)
| semSub i j k: ϕ S (wSub i j k) (update i (S j - S k) S)
| semCon i c: ϕ S (wCon i c) (update i c S)
| semSeq P1 P2 S2 S3: ϕ S P1 S2 -> ϕ S2 P2 S3 -> ϕ S (wSeq P1 P2) S3
| semIfP1 i P1 S2: S i = 0 -> ϕ S (P1) S2 -> ϕ S (wIf i P1) S2
| semIfP2 i P1: S i > 0 -> ϕ S (wIf i P1) S.

Definition initState n :state := fun x => if x then n else 0.

Fixpoint execute (S:state) (P:ifP) : state :=
  match P with
    wCon i c => update i c S
  | wAdd i j k => update i (S j + S k) S
  | wSub i j k => update i (S j - S k) S
  | wSeq P1 P2 => execute (execute S P1) P2
  | wIf i P1 => (if S i then execute S P1 else S)
  end.

Fixpoint stepExecute (s:state) (P:ifP) : nat*state :=
  match P with
    wCon i c => (1,update i c s)
  | wAdd i j k => (1,update i (s j + s k) s)
  | wSub i j k => (1,update i (s j - s k) s)
  | wSeq P1 P2 =>
    let (n1,s') := stepExecute s P1 in
    let (n2,s'') := stepExecute s' P2 in
    (n1+n2,s'')
  | wIf i P1 =>
    if s i then stepExecute s P1 else (0,s)
  end.

Fixpoint stepBound (P:ifP) : nat :=
  match P with
    wCon i c => 1
  | wAdd i j k => 1
  | wSub i j k => 1
  | wSeq P1 P2 => stepBound P1 + stepBound P2
  | wIf i P1 => stepBound P1
  end.

(* Notation "i = j 'w+' k" := (wAdd i j k)(at level 60). *)
(* Notation "i = j 'w-' k" := (wSub i j k)(at level 60). *)
(* Notation "i ':=' c" := (wCon i c)(at level 60). *)
(* Notation "P1 ; P2" := (wSeq P1 P2)(at level 70). *)
(* Notation "'ifP' i 'then' P1 'else' P2" := (wIf i P1 P2)(at level 80). *)

Definition steps s P := fst (stepExecute s P).

Lemma stepMax P s: steps s P <= stepBound P.
Proof.
  induction P in s |- *;cbn;trivial;unfold steps in *;cbn.
  - specialize (IHP s).
    destruct s.
    1: destruct stepExecute.
    all: cbn in *;lia.
  - specialize (IHP1 s).
    destruct stepExecute.
    specialize (IHP2 s0).
    destruct stepExecute;cbn in *.
    lia.
Qed.


Fixpoint forward (s:propState) (n:nat) (p:ifP) : list (propState * nat) :=
  match p with
    wCon i c => [(update i (c,c) s, S n)]
  | wAdd i j k => [(update i (fst(s j) + fst(s k),snd(s j)+snd(s k)) s, S n)]
  | wSub i j k => [(update i (fst(s j) - snd(s k),snd(s j)-fst(s k)) s, S n)]
  | wSeq P1 P2 =>
    let xs := forward s n P1 in
    concat (map (fun x => forward (fst x) (snd x) P2) xs)
  | wIf i P1 => match fst(s i) with 0 => forward (update i (0,0) s) n P1 | S _ => [] end ++
               match snd(s i) with 0 => [] | S _ => [(s,n)] end
  end.

Definition consistent (s:propState) := forall a, fst (s a) <= snd (s a).

Goal forall p s n, consistent s -> forall x, In x (forward s n p) -> consistent (fst x).
Proof.
  induction p;cbn;intros.
  - inv H0.
    + cbn. intros x.
      unfold update.
      destruct Nat.eqb.
      * constructor.
      * apply H.
    + contradict H1.
  - inv H0.
    + intros x.
      cbn. unfold update.
      destruct Nat.eqb;cbn.
      * specialize (H j) as H1.
        specialize (H k) as H2.
        lia.
      * apply H.
    + contradict H1.
  - inv H0.
    + intros x; unfold update;
        cbn; destruct Nat.eqb;cbn.
      * specialize (H j) as H1.
        specialize (H k) as H2.
        lia.
      * apply H.
    + contradict H1.
  - destruct fst eqn:H1, snd eqn: H2.
    1: rewrite app_nil_r in H0.
    2: apply in_app_or in H0 as [].
    (* 1 2 *)
    (* 3 5 *)
    1-2:
      apply IHp in H0;trivial;
      intros z; unfold update;
        destruct Nat.eqb;trivial.
    + inv H0.
      * cbn. apply H.
      * contradict H3.
    + contradict H0.
    + cbn in H0. inv H0.
      * cbn. apply H.
      * contradict H3.
  - admit.
Admitted.

Goal forall s, consistent s -> exists s', forall x, fst(s x) <= s' x <= snd (s x).
Proof.
  intros.
  exists (fun x => fst(s x)).
  intros x.
  constructor.
  - constructor.
  - apply H.
Qed.

Definition consistentWith (s':state) (s:propState)  := forall x, fst(s x) <= s' x <= snd (s x).

Goal forall p s n x, consistent s -> In x (forward s n p) -> exists s' y, stepExecute s' p = y /\ consistentWith (snd y) (fst x) /\ n+fst y = snd x.
Proof.
  induction p;cbn;intros.
  - inv H0.
    + cbn.
      do 2 eexists.
      split.
      * reflexivity.
      * split.
        -- cbn. intros x.
           unfold update.
           destruct Nat.eqb;auto.
           split. 1: constructor.
           apply H.
        -- cbn. lia.
    + contradict H1.
  - inv H0.
    + cbn.
      exists (fun x => fst(s x)).
      eexists.
      split.
      * reflexivity.
      * split.
        -- cbn. intros x.
           unfold update.
           destruct Nat.eqb;auto.
           cbn. split.
           ++ constructor.
           ++ specialize (H j) as H1.
              specialize (H k) as H2.
              lia.
        -- cbn. lia.
    + contradict H1.
  - inv H0.
    + cbn.
      exists (fun x => fst(s x)).
      eexists.
      split.
      * reflexivity.
      * split.
        -- cbn. intros x.
           unfold update.
           specialize (H j) as H1.
           specialize (H k) as H2.
           destruct Nat.eqb;auto.
           cbn. split;lia.
        -- cbn. lia.
    + contradict H1.
  - destruct fst eqn:H1, snd eqn: H2.
    1: rewrite app_nil_r in H0.
    2: apply in_app_or in H0 as [].
    + apply IHp in H0 as (s' & y & H3 & H4 & H5);trivial.
      * exists s'.
          (* (fun x => fst (s x)). *)
        eexists.
        split.
        -- reflexivity.
        -- split.
           ++ intros z. cbn.
              admit.
           ++ admit.
Admitted.

Goal forall p s x n s', consistentWith s' s -> stepExecute s' p = x -> exists y, In y (forward s n p) /\ consistentWith (snd x) (fst y) /\ n+(fst x) = snd y.
Proof.
Admitted.
