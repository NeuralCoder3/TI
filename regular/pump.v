Require Import List Lia.
Import ListNotations.

Definition Σ := bool.
Definition word := list Σ.
Definition language := word -> Prop.

Notation "| x |" := (length x)(at level 71).

Definition notPump (L:language) :=
  forall n, n>0 -> exists u v w, L (u++v++w) /\ forall x y z, v=x++y++z -> |y|>0 -> exists i, ~L (u ++ x ++ (concat (repeat y i)) ++ z ++ w).

Definition all :language := fun _ => True.
Definition revLang (L:language) := fun x => exists y, x=y++rev y /\ L y.
Definition revLangAll :language := fun x => exists y, x=y++rev y.

Definition nat2bool (n:nat) := if n then false else true.

Coercion nat2bool : nat >-> bool.






Goal (revLang all [false;true;true;false]).
Proof.
  exists [false;true]. cbn;now split.
Qed.

Goal ~(revLang all [false;true;false]).
Proof.
  intros [x [H _]].
  destruct x as [|[]];cbn in H;try congruence.
  induction x.
  - cbn in H;congruence.
Admitted.

Definition L01 : language := fun x => exists n, x=repeat false n ++ repeat true n.

Lemma repeat_inj {X} (x:X) n m: repeat x n = repeat x m -> n=m.
Proof.
  induction n in m |- *.
  - destruct m;cbn;congruence.
  - destruct m;cbn.
    + congruence.
    + intros [=].
      now apply IHn in H0 as ->.
Qed.

Goal forall X (xs ys:list X) a n m, ~In a xs -> ~In a ys -> xs ++ repeat a n = ys ++ repeat a m -> n=m.
Proof.
  induction xs;intros.
  - destruct ys.
    + cbn in H1.
      now apply repeat_inj in H1.
    + admit.
Abort.

Goal notPump (L01).
Proof.
  intros n H.
  exists [],(repeat false n),(repeat true n).
  split.
  - now exists n.
  - intros.
    exists 0;cbn. intros [].
    rewrite app_assoc in H2.
    assert(x0=n) as ->.
    {
      admit.
      (* induction x in z, H0, H2 |- *;cbn in H2. *)
      (* - induction z. *)
      (*   +  *)
      (* induction n;cbn in H2. *)
      (* - lia. *)
      (* - admit. *)
    }
    assert(|x++y++z|=n).
    {
      rewrite <- repeat_length with (x:=false).
      now rewrite H0.
    }
    do 2 rewrite app_length in H3.
    assert((|x|)+(|z|)<n) by lia.
    apply app_inv_tail in H2.
    assert((|x++z|)=n) by (now rewrite H2,repeat_length).
    rewrite app_length in H5.
    lia.
Admitted.


Scheme Equality for bool.
(* Definition count b xs := count_occ bool_eq_dec xs b. *)
Fixpoint count b xs :=
  match xs with
    [] => 0
  | x::xs => if bool_eq_dec b x then S(count b xs) else count b xs
  end.


Lemma countApp b xs ys : count b (xs++ys) = count b xs + count b ys.
Proof.
  induction xs in ys |- *;cbn.
  - reflexivity.
  - destruct bool_eq_dec;unfold count in *;rewrite IHxs;reflexivity.
Qed.

Lemma countRev b xs: count b xs = count b (rev xs).
Proof.
  induction xs;cbn.
  - reflexivity.
  - rewrite countApp;cbn. destruct bool_eq_dec;rewrite IHxs; lia.
Qed.

Lemma countRevDouble b xs: count b (xs++rev xs) = 2 * count b xs.
Proof.
  rewrite countApp,countRev. lia.
Qed.

Lemma countNotIn b xs: ~In b xs -> count b xs = 0.
Proof.
  induction xs;trivial;cbn.
  intros H. destruct bool_eq_dec.
  - rewrite e. contradict H. now left.
  - apply IHxs. contradict H. now right.
Qed.

Lemma notIn X (a b:X) n: a<>b -> ~In a (repeat b n).
Proof.
  induction n.
  - tauto.
  - cbn. intros H [->|H2];now apply IHn.
Qed.

Lemma revRepeat {X} (x:X) n: rev (repeat x n) = repeat x n.
Proof.
  induction n;trivial;cbn;rewrite IHn.
  clear IHn.
  induction n;trivial;cbn;now rewrite IHn.
Qed.

Lemma revInv {X} (xs ys:list X) : rev xs=rev ys -> xs=ys.
Proof.
  (* induction xs in ys |- *. *)
  (* - cbn. destruct ys. *)
  (*   + tauto. *)
  (*   + cbn. destruct rev;cbn;congruence. *)
  (* - cbn. *)
  induction xs in ys |- *;destruct ys;cbn.
  - trivial.
  - destruct rev;cbn;congruence.
  - destruct rev;cbn;congruence.
  - now intros [->%IHxs ->]%app_inj_tail.
Qed.

Goal notPump (revLangAll).
Proof.
  intros n H.
  exists [].
  exists (repeat true n).
  exists ([false;false] ++ (repeat true n) ++ []).
  split.
  - exists (repeat true n++[false]);cbn.
    rewrite rev_unit.
    rewrite <- app_assoc;cbn.
    assert(forall X (a:X) m, rev (repeat a m) = repeat a m).
    {
    intros. induction m;trivial;cbn. rewrite IHm.
    clear IHm. now induction m;trivial;cbn;rewrite IHm.
    }
    now rewrite H0, app_nil_r.
  - intros. exists 0;cbn. intros [].
    rewrite app_nil_r in H2.
    assert(|x++y++z|=n).
    {
      rewrite <- repeat_length with (x:=true).
      now rewrite H0.
    }
    do 2 rewrite app_length in H3.
    assert((|x|)+(|z|)<n) by lia.

    assert(count false x=0).
    {
      apply countNotIn.
      intros F.
      admit.
    }
    assert(count false z=0).
    {
      apply countNotIn.
      intros F.
      admit.
    }
    assert(count false (repeat true n)=0) by (now apply countNotIn,notIn).
    assert(count false (x++z++false::false::repeat true n)=2).
    {
      repeat rewrite countApp.
      rewrite H5, H6;cbn.
      now rewrite H7.
    }
    assert(count false (x0++rev x0)=2) by (now rewrite <- H2,H8).
    rewrite countRevDouble in H9.
    assert(count false x0=1) by lia.

    assert(x0=x++z++[false]).
    {
      admit.
    }
    (* assert(x0=x++z++[false] /\ rev x0 = false::repeat true n) as [] by admit. *)
    assert(x++z=repeat true n).
    {
      rewrite H11 in H2.
      assert( (x ++ z ++ [false]) ++ false :: repeat true n = (x ++ z ++ [false]) ++ rev (x ++ z ++ [false])).
      {
        now do 2 rewrite <- app_assoc.
      }
      apply app_inv_head in H12.
      rewrite app_assoc in H12.
      rewrite rev_app_distr in H12.
      cbn in H12.
      injection H12 as H13.
      rewrite <- revRepeat in H13.
      now apply revInv in H13.
    }

    assert((|x|)+(|z|)=n) by (now rewrite <- app_length,H12,repeat_length).
    lia.
Admitted.

