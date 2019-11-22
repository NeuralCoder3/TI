Require Import Lia.
(* From Hammer Require Import Hammer Reconstr. *)
Require Import List.
Import ListNotations Nat.

Definition pi (x y:nat) :nat :=
  ((x+y)*(x+y+1))/2+y.

Lemma inv (z:nat) : {x & {y & z=pi x y}}.
Proof.
  pose (w := (sqrt(8*z+1)-1)/2).
  pose (t := (w*w+w)/2).
  pose (y := z-t).
  exists (w-y). exists (y).
  unfold pi.
  (* subst w t y. cbn. *)
  assert(y<=w) by admit.
  assert(t<=z) by admit.
  replace (w-y+y) with w by lia.
  subst y.
  assert(w*(w+1)/2=t).
  {
    subst t.
    now replace (w*(w+1)) with (w*w+w) by nia.
  }
  nia.
Admitted.

Definition goed (xy:nat*nat) :=
  let (x,y) := xy in
  pi x y.

Definition degoed (n:nat) :=
  let (x,z) := inv n in
  let (y,_) := z in
  (x,y).

Goal forall x y, degoed(goed(x,y))=(x,y).
Proof.
  intros.
  cbn.
  pose proof (PeanoNat.Nat.divmod_spec ((x+y)*(x+y+1)) 1 0 1).
  destruct divmod.
  destruct H;trivial;cbn.
  destruct n0 as [|[]].
  - assert((x+y)*(x+y+1)=2*n+1) by nia.
    unfold degoed.
    unfold inv.
