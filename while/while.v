Require Import Lia.
Require Import List.
Require Import Program Arith.
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

(* Definition var := nat. *)
Notation var := nat.

Inductive whileP :=
  wCon (n:var) (c:nat)
| wAdd (i j k:var)
| wSub (i j k:var)
| wWhile (i:var) (P1:whileP)
| wSeq (P1 P2 : whileP).

Definition isSimple w :=
  match w with
    wCon _ _ => true
  | wAdd _ _ _ => true
  | wSub _ _ _ => true
  | _ => false
  end.

Inductive W : nat -> whileP -> Prop :=
  | wPBaseCon n c : W 0 (wCon n c)
  | wPBaseAdd i j k : W 0 (wAdd i j k)
  | wPBaseSub i j k : W 0 (wSub i j k)
  | wSuccLift n w : W n w -> W (S n) w
  | wSuccWhileP n i P1 : W n P1 -> W (S n) (wWhile i P1)
  | wSuccSeq n j k P1 P2 : W j P1 -> W k P2 -> j+k<=n -> W (S n) (wSeq P1 P2).

Inductive forP :=
  fCon (n:var) (c:nat)
| fAdd (i j k:var)
| fSub (i j k:var)
| fFor (i:var) (P1:forP)
| fSeq (P1 P2 : forP).

Definition state := var -> nat.

Definition update (x:var) (c:nat) (s:state) : state :=
  fun y => if x==y then c else s y.

Inductive ϕ (S:state) : whileP -> state -> Prop :=
  semAdd i j k: ϕ S (wAdd i j k) (update i (S j + S k) S)
| semSub i j k: ϕ S (wSub i j k) (update i (S j - S k) S)
| semCon i c: ϕ S (wCon i c) (update i c S)
| semSeq P1 P2 S2 S3: ϕ S P1 S2 -> ϕ S2 P2 S3 -> ϕ S (wSeq P1 P2) S3
| semWhileP i P1: S i = 0 -> ϕ S (wWhile i P1) S
| semWhileP2 i P1 S2 S3: S i > 0 -> ϕ S P1 S2 -> ϕ S2 (wWhile i P1) S3 -> ϕ S (wWhile i P1) S3.

Section totalSem.

  Fixpoint itF {X} f n x : X :=
    match n with
    | 0 => x
    | S n'=> f (itF f n' x)
    end.

  Axiom (XM: forall (X:Type), X + (X -> False)).

  Print sig.

  (* need minimal and at position 0 *)
  Fixpoint sem (s:state) (w:whileP) : option state :=
    match w with
      wAdd i j k => Some (update i (S j + S k) S)
    | wSub i j k => Some (update i (S j - S k) S)
    | wCon i c => Some (update i c S)
    | wSeq P1 P2 => match sem s P1 with
                     None => None
                   | Some s2 => sem s2 P2
                   end
    | wWhile i P1 => match XM ({r & { s2 & itF (fun s => match s with None => None | Some s' => sem s' P1 end) r (Some s) = Some s2 }}) with
                      | inl _ => None
                      | inr _ => None
                    end
    end.

End totalSem.

Section itSem.

  (* min fehlt *)
  Fixpoint it n f (s:state) (s3:state) : Prop :=
    match n with
    | 0 => s=s3
    | S n'=> exists s2, f s s2 /\ it n' f s2 s3
    end.

  (* Fixpoint it2 n := *)
  (*   match n with *)
  (*   | 0 => fun f (s:state) (s3:state) => s=s3 *)
  (*   | S n'=> fun f (s:state) (s3:state) => exists s2, f s s2 /\ it2 n' f s2 s3 *)
  (*   end. *)

  (* Fixpoint it3 n f (s:state) (s3:state) : Prop := *)
  (*   match n with *)
  (*   | 0 => s=s3 *)
  (*   | S n'=> (fun H => exists s2, f s s2 /\ H s2) (fun a => it n' f a s3) *)
  (*   end. *)

  (* Lemma itAlt n f s s3: it n f s s3 <-> it2 n f s s3. *)
  (* Proof. *)
  (*   intros. split. *)
  (*   - induction n in s |- *;intros H. *)
  (*     + exact H. *)
  (*     + cbn. destruct H as (S2&H&H1). *)
  (*       exists S2. split;trivial. now apply IHn. *)
  (*   - induction n in s |- *. *)
  (*     + trivial. *)
  (*     + cbn. intros [S2 []]. *)
  (*       exists S2. split;trivial. *)
  (*       now apply IHn. *)
  (* Qed. *)

  (* Inductive ϕ2 (S:state) : whileP -> state -> Prop := *)
  (*   sem2Add i j k: ϕ2 S (wAdd i j k) (update i (S j + S k) S) *)
  (* | sem2Sub i j k: ϕ2 S (wSub i j k) (update i (S j - S k) S) *)
  (* | sem2Con i c: ϕ2 S (wCon i c) (update i c S) *)
  (* | sem2Seq P1 P2 S2 S3: ϕ2 S P1 S2 -> ϕ2 S2 P2 S3 -> ϕ2 S (wSeq P1 P2) S3 *)
  (* | sem2WhileP i P1 r S2: it r (fun x y => ϕ2 x P1 y) S S2 -> S2 i = 0 -> ϕ2 S (wWhile i P1) S2. *)

  (* Lemma extendIt S S2 S3 (f:state->state->Prop) r: f S S2 -> it r f S2 S3 -> it (S r) f S S3. *)
  (* Admitted. *)

  (* Goal forall w s s2, ϕ s w s2 <-> ϕ2 s w s2. *)
  (* Proof. *)
  (*   intros w s s2. *)
  (*   destruct w;split;try (intros H;inv H;constructor). *)
  (*   - intros H. remember (wWhile i w);induction H;try congruence;subst. *)
  (*     + apply sem2WhileP with (r:=0);trivial. *)
  (*       reflexivity. *)
  (*     + apply IHϕ2 in Heqw0. *)
  (*       inv Heqw0. *)
  (*       apply sem2WhileP with (r:=S r). *)
  (*       * eapply extendIt;eassumption. *)
  (*       * exact H6. *)
  (*   - intros H. inv H. induction r. *)
  (*     + rewrite H2. now constructor. *)
  (* Admitted. *)

End itSem.

Lemma WhilePSeqKomm S S' P1 P2 P3: ϕ S (wSeq P1 (wSeq P2 P3)) S' <-> ϕ S (wSeq (wSeq P1 P2) P3) S'.
Proof.
  split;intros H;inv H.
  - inv H4. econstructor;try eassumption.
    + econstructor;eassumption.
  - inv H2. econstructor;try eassumption.
    + econstructor;eassumption.
Qed.

(* Inductive ϕF (S:state) : forP -> state -> Prop := *)
(*   semFAdd i j k: ϕF S (fAdd i j k) (update i (S j + S k) S) *)
(* | semFSub i j k: ϕF S (fSub i j k) (update i (S j - S k) S) *)
(* | semFCon i c: ϕF S (fCon i c) (update i c S) *)
(* | semFSeq P1 P2 S2 S3: ϕF S P1 S2 -> ϕF S2 P2 S3 -> ϕF S (fSeq P1 P2) S3 *)
(* | semFFor i P1 S2: it (S i) (fun x y => ϕF x P1 y) S S2 -> ϕF S (fFor i P1) S2. *)

Definition goed5 (r m : nat) : nat := 5*m+r.
Definition pi15 (n:nat) : nat := n mod 5.
Definition pi25 (r:nat) : nat := div r 5.

Lemma divmodSpec x y q:
  let (q', u') := PeanoNat.Nat.divmod x y q y in x + S y * q = S y * q' + (y - u') /\ u' <= y.
Proof.
  pose proof (PeanoNat.Nat.divmod_spec x y q y).
  assert(y<=y) by constructor.
  apply H in H0. clear H.
  destruct divmod, H0.
  lia.
Qed.

Lemma goed5Bij2: forall r m, r<5 -> pi15(goed5 r m)=r /\ pi25(goed5 r m)=m.
Proof.
  intros r m H.
  pose proof (divmodSpec (5*m+r) 4 0).
  cbn in *.
  destruct divmod.
  cbn.
  destruct H0.
  destruct n0 as [|[|[|[|[]]]]];try nia.
Qed.

Lemma goed5Bij: forall n, goed5 (pi15 n) (pi25 n) = n.
Proof.
  intros n.
  cbn.
  pose proof (divmodSpec n 4 0).
  destruct divmod;cbn.
  destruct H.
  destruct n1 as [|[|[|[|[]]]]];try nia.
Qed.

Definition goed (x1 x2:nat) := div ((x1+x2)*(x1+x2+1)) 2 + x2.

(* Compute (goed 2566 12353). *)

Lemma gauss z: div ((z+1)*(z+2)) 2 - div (z*(z+1)) 2 = z+1.
Proof.
  cbn.
  pose proof(divmodSpec ((z + 1) * (z + 2)) 1 0 ).
  pose proof(divmodSpec (z * (z + 1)) 1 0 ).
  destruct divmod, divmod, H,H0.
  cbn.
  destruct n0 as [|[]], n2 as [|[]];nia.
Qed.

Lemma pi (p:nat) : {x1 & {x2 | goed x1 x2 = p}}.
Proof.
  assert({z|div (z*(z+1)) 2 <= p /\ div (S z * (S z +1)) 2 > p}) as [z [H1 H2]].
  {
    admit.
  }
  set (x2:=p-div (z*(z+1)) 2).
  set (x1:=z-x2).
  exists x1, x2.
  cbn. pose proof (divmodSpec ((x1 + x2) * (x1 + x2 + 1)) 1 0).
  destruct divmod, H. cbn.
  subst x2. subst x1.
  destruct n0 as [|[]].
  - admit.
  - admit.
  - lia.
Admitted.

Fixpoint getLargestZ (p:nat) (z:nat) :=
  match z with
    O => O
  | S z' => if Nat.leb (div (z*(z+1)) 2) p then z else getLargestZ p z'
  end.

Lemma gaussMax p: p <= div (p*(p+1)) 2.
Proof.
  cbn. pose proof (divmodSpec (p*(p+1)) 1 0).
  destruct divmod, H;cbn. nia.
Qed.

Lemma gaussZ2 p x:
  let z := getLargestZ p x in
  div (z*(z+1)) 2 <= p.
Proof.
  induction x.
  - cbn. lia.
  - cbv [getLargestZ].
    destruct Nat.leb eqn: H.
    + now apply Compare_dec.leb_complete in H.
    + apply IHx.
Qed.

Lemma gaussZ p x: p <= div (x*(x+1)) 2 ->
                  let z := getLargestZ p x in
                  div (z*(z+1)) 2 <= p /\ div (S z * (S z +1)) 2 > p.
Proof.
  cbn.
  intros H.
  split. apply gaussZ2.
  admit.
Admitted.

Definition pi1 (z:nat) :=
  let w := div (sqrt(8*z+1)-1) 2 in
  let t := div (w*w+w) 2 in
  let y := z-t in
  let x := w-y in
  x.

Definition pi2 (z:nat) :=
  let w := div (sqrt(8*z+1)-1) 2 in
  let t := div (w*w+w) 2 in
  let y := z-t in
  y.

Definition pi2_2 (p:nat) :=
  let z := getLargestZ p p in
  p-div (z*(z+1)) 2.

Definition pi1_2 (p:nat) :=
  let z := getLargestZ p p in
  z-pi2 p.

Compute (pi1 (goed 5 8)).
Compute (pi2 (goed 5 8)).

Lemma goedBij: forall p, goed (pi1 p) (pi2 p) = p.
Admitted.

Lemma goedBij2: forall x1 x2, pi1 (goed x1 x2) = x1 /\ pi2 (goed x1 x2) = x2.
Admitted.

Compute (goed 4 2).
Compute (pi1 23).
Compute (pi2 23).

Fixpoint goedWhileP (w:whileP) :=
  match w with
    wAdd i j k => goed5 0 (goed i (goed j k))
  | wSub i j k => goed5 1 (goed i (goed j k))
  | wCon i c => goed5 2 (goed i c)
  | wWhile i P1 => goed5 3 (goed i (goedWhileP P1))
  | wSeq P1 P2 => goed5 4 (goed (goedWhileP P1) (goedWhileP P2))
  end.

Definition goedSize (sx1 sx2:nat) : nat :=
  let m := max sx1 sx2 in
  2*m.

Lemma size (x:nat) : nat.
Proof.
  induction x using complete_induction.
  destruct (Nat.leb x 9) eqn: H1.
  - exact 1.
  - specialize (H (div x 10)).
    assert(x/10 < x).
    apply leb_complete_conv in H1.
    cbn. pose proof (divmodSpec x 9 0).
    destruct divmod,H0. cbn. lia.
    specialize (H H0).
    exact (S H).
Defined.

Eval vm_compute in (size 513).

(* Program Fixpoint size (x:nat) {size2 x} : nat := *)
(*   if x <? 10 then 1 else *)
(*     S (size (div x 10)) *)
(* . *)

Compute (size 1235).

Fixpoint goedWhilePSize (w:whileP) :=
  match w with
    wAdd i j k => (goedSize (size i) (goedSize (size j) (size k)))
  | wSub i j k => (goedSize (size i) (goedSize (size j) (size k)))
  | wCon i c => (goedSize (size i) (size c))
  | wWhile i P1 => (goedSize (size i) (goedWhilePSize P1))
  | wSeq P1 P2 => (goedSize (goedWhilePSize P1) (goedWhilePSize P2))
  end.

Fixpoint whileInstruction (w:whileP) :=
  match w with
  | wWhile _ P1 => S (whileInstruction P1)
  | wSeq P1 P2 => (whileInstruction P1) + (whileInstruction P2)
  | _ => 1
  end.

Lemma boundPi15 n: ~ (5<=pi15 n).
Proof.
  intros H.
  cbn in H.
  pose proof (divmodSpec n 4 0).
  destruct divmod, H0. cbn in *.
  destruct n1 as [|[|[|[|[]]]]];lia.
Qed.

Lemma greater5 n: 5<=S(S(S(S(S n)))).
Proof.
  lia.
Qed.

(* Lemma strucPi2 n: n=0 \/ pi2 n < n. *)

(* Program Lemma goedInv : forall (n:nat), whileP. *)
(*   refine(fix f n {meassure n} := match pi15 n, pi25 n with *)
(*     0,m => let i := pi1 m in *)
(*           let x := pi2 m in *)
(*           let j := pi1 x in *)
(*           let k := pi2 x in *)
(*           wAdd i j k *)
(*   | 1,m => let i := pi1 m in *)
(*           let x := pi2 m in *)
(*           let j := pi1 x in *)
(*           let k := pi2 x in *)
(*           wSub i j k *)
(*   | 2,m => let i := pi1 m in *)
(*           let c := pi2 m in *)
(*           wCon i c *)
(*   | 3,m => let i := pi1 m in *)
(*           let P1 := f (pi2 m) in *)
(*           wWhile i P1 *)
(*   | 4,m => let x := pi1 m in *)
(*           let y := pi2 m in *)
(*           wSeq (f x) (f y) *)
(*   | S(S(S(S(S n)))),_ => _ *)
(*   end). *)

From Equations Require Import Equations.

Lemma strucPi1 n : pi1 n < n.
Admitted.
Lemma strucPi2 n : pi2 n < n.
Admitted.
Lemma strucPi15 n : pi15 n < n.
Admitted.
Lemma strucPi25 n : pi25 n < n.
Admitted.

Lemma goedInv (n:nat) :whileP.
Proof.
  induction n using complete_induction.
  remember (pi15 n) as x.
  revert Heqx.
  refine(
  match x as y, pi25 n with
    0,m => fun _ => let i := pi1 m in
          let x := pi2 m in
          let j := pi1 x in
          let k := pi2 x in
          wAdd i j k
  | 1,m => fun _ => let i := pi1 m in
          let x := pi2 m in
          let j := pi1 x in
          let k := pi2 x in
          wSub i j k
  | 2,m => fun _ => let i := pi1 m in
          let c := pi2 m in
          wCon i c
  | 3,m => fun _ => let i := pi1 m in
          let P1 := H (pi2 m) _ in
          wWhile i P1
  | 4,m => fun _ =>let x := pi1 m in
          let y := pi2 m in
          wSeq (H x _) (H y _)
  | S(S(S(S(S n)))),_ => _
  end
    ).
  - subst i m.
    pose proof (strucPi25 n).
    pose proof (strucPi2 (pi25 n)).
    lia.
  - subst x y m.
    pose proof (strucPi25 n).
    pose proof (strucPi1 (pi25 n)).
    lia.
  - subst x y m.
    pose proof (strucPi25 n).
    pose proof (strucPi2 (pi25 n)).
    lia.
  - intros F. pose proof (greater5 n).
    rewrite F in H0.
    now apply boundPi15 in H0.
Defined.

(* Program Fixpoint goedInv (n:nat) { n} :whileP := *)
(*   match pi15 n, pi25 n with *)
(*     0,m => let i := pi1 m in *)
(*           let x := pi2 m in *)
(*           let j := pi1 x in *)
(*           let k := pi2 x in *)
(*           wAdd i j k *)
(*   | 1,m => let i := pi1 m in *)
(*           let x := pi2 m in *)
(*           let j := pi1 x in *)
(*           let k := pi2 x in *)
(*           wSub i j k *)
(*   | 2,m => let i := pi1 m in *)
(*           let c := pi2 m in *)
(*           wCon i c *)
(*   | 3,m => let i := pi1 m in *)
(*           let P1 := goedInv (pi2 m) in *)
(*           wWhile i P1 *)
(*   | 4,m => let x := pi1 m in *)
(*           let y := pi2 m in *)
(*           wSeq (goedInv x) (goedInv y) *)
(*   | S(S(S(S(S n)))),_ => wAdd 0 0 0 (* to contradict *) *)
(*   end. *)
(* Obligations. *)
(* Next Obligation. *)
(*   exact nat. *)
(* Qed. *)
(* Next Obligation. *)
(*   admit. *)
(* Next Obligation. *)

Definition seqS (f g: state -> option state) s : option state :=
  match f s  with
    None => None
  | Some s' => g s'
  end.

Definition sigma' F c s : option state :=
  match c with
    wAdd i j k => Some (update i (s j + s k) s)
  | wSub i j k => Some (update i (s j - s k) s)
  | wCon i c => Some (update i c s)
  | wSeq P1 P2 => seqS (F P1) (F P2) s
  | wWhile i P1 => if s i then Some s else seqS (F P1) (F (wWhile i P1)) s
  end.

Fixpoint sigma n : whileP -> state -> option state :=
  match n with
    0 => fun _ _ => None
  | S n' => sigma' (sigma n')
  end.

Goal forall w, goedInv(goedWhileP w) = w.
Admitted.

Notation "i = j 'w+' k" := (wAdd i j k)(at level 60).
Notation "i = j 'w-' k" := (wSub i j k)(at level 60).
Notation "i ':=' c" := (wCon i c)(at level 60).
Notation "P1 ; P2" := (wSeq P1 P2)(at level 70).
Notation "'while' i 'do' P1 'od' " := (wWhile i P1)(at level 80).
Check (while 1 do 1 := 1 od).

(* Notation "'whileP' i 'do' P1 'od' " := (wWhile i P1)(at level 90). *)
(* Check (whileP 1 do 1 := 1 od). *)

(* Notation "'whileP' i 'do' P1" := (wWhile i P1)(at level 90). *)
(* Check (whileP 1 do (1 := 1)). *)
(* Notation "'whileP' i <> 'do' P1 'od'" := (wWhile i P1)(at level 90). *)
(* Check (whileP 1 <> do (1 := 1) od). *)
Check (1 = 2 w- 3).
Check (1 = 2 w+ 3).
Check (2 := 2).
Check (1 = 2 w+ 3;1 := 2).


Definition wAssign (i j:var) :=
  (i := 0;i = i w+ j).

Definition wDec (i:var) (tmp:var) :=
  (
    tmp := 1;
    i = i w- tmp
  ).

Definition wInc (i:var) (tmp:var) :=
  (
    tmp := 1;
    i = i w+ tmp
  ).

Definition wFor' (i:var) (P1:var -> whileP) (tmp: var) :=
  let t1 := tmp in
  let tmp' := S tmp in
  (
    wAssign t1 i;
    while t1 do
      wDec t1 tmp';
      P1 tmp'
    od
  ).

Definition wFor (i:var) (P1:whileP) := wFor' i (fun _ => P1).

Definition wIf0' (i:var) (P1 P2:var -> whileP) (tmp : var) :=
  let t1 := tmp in
  let t2 := S tmp in
  let tmp' := 2+tmp in
  (t1 := 1;
   t2 := 0;
   let P3 := fun _ => (t1 := 0;t2 := 1) in
   wFor' i P3 tmp';
   wFor' t1 P1 tmp';
   wFor' t2 P2 tmp'
  ).

Definition wIf0 (i:var) (P1 P2: whileP) := wIf0' i (fun _ => P1) (fun _ => P2).

Definition wMul (i j k:var) (tmp:var) :=
  (
    wAssign tmp j;(* if i==j *)
    i := 0;
    wFor tmp (
      i = i w+ k
         ) (S tmp)
  ).

Definition wPow (i j k:var) (tmp:var) :=
  (
    i := 1;
    wFor' k (wMul i i j) tmp
  ).

Definition nop (tmp:var) := (tmp:=0).

Definition wAddCon (i j:var) (c:nat) (tmp:var) :=
  (
    tmp := c;
    i = j w+ tmp
  ).

Definition wDiv (i j k:var) (tmp:var) :=
  let set := tmp in
  let acc := 1+tmp in
  let count := 2+tmp in
  let comp := 3+tmp in
  let tmp' := 4+tmp in
  (
    i := 0;
    set := 0;
    wAssign acc j;
    count := 0;
    wFor' j (fun tmp2 =>
      wAddCon count count 1 tmp2;
      acc = acc w- k;
      wAddCon comp acc 1 tmp2;
      comp = comp w- k;
      wIf0' comp
            (fun tmp3 =>
               wIf0' set
                     (fun tmp4 =>
                        wAssign i count;
                        set := 1
                     )
                     (fun tmp4 => nop tmp4)
                     tmp3
            )
            (fun tmp3 => nop tmp3)
            tmp2
            ) tmp'
  ).

Definition wMod (i j k:var) (tmp:var) :=
  let x1 := tmp in
  let x2 := 1+tmp in
  let tmp' := 2+tmp in
  (
    wDiv x1 j k tmp';
    wMul x2 x1 k tmp';
    i = j w- x2
  ).

Definition wIfLe' (i j:var) (P1 P2:nat -> whileP) (tmp:var) :=
  let comp := tmp in
  let tmp' := S tmp in
  (
    comp = i w- j;
    wIf0' comp P1 P2 tmp'
  ).

Definition wIfLe (i j:var) (P1 P2: whileP) := wIfLe' i j (fun _ => P1) (fun _ => P2).

Definition wIfLt' (i j:var) (P1 P2:nat -> whileP) (tmp:var) :=
  let comp := tmp in
  let tmp' := S tmp in
  (
    wAddCon comp i 1 tmp';
    comp = comp w- j;
    wIf0' comp P1 P2 tmp'
  ).

Definition wIfLt (i j:var) (P1 P2: whileP) := wIfLt' i j (fun _ => P1) (fun _ => P2).

Definition wIfGe' (i j:var) := wIfLe' j i.
Definition wIfGe (i j:var) := wIfLe j i.
Definition wIfGt' (i j:var) := wIfLt' j i.
Definition wIfGt (i j:var) := wIfLt j i.

Definition wIfEq' (i j:var) (P1 P2:nat -> whileP) (tmp:var) :=
  let le := tmp in
  let ge := 1+tmp in
  let comp := 2+tmp in
  let tmp' := 3+tmp in
  (
    le = i w- j;
    ge = j w- i;
    comp = le w+ ge;
    wIf0' comp P1 P2 tmp'
  ).

Definition wIfEq (i j:var) (P1 P2: whileP) := wIfEq' i j (fun _ => P1) (fun _ => P2).

Definition wIfNeq' (i j:var) (P1 P2:nat -> whileP) := wIfEq' i j P2 P1.
Definition wIfNeq (i j:var) (P1 P2:whileP) := wIfEq i j P2 P1.

Definition wGoed (i j k:var) (tmp:var) :=
  let sum := tmp in
  let s1 := 1+tmp in
  let p := 2+tmp in
  let z := 3+tmp in
  let t1 := 4+tmp in
  let tmp' := 5+tmp in
  (
    sum  = j w+ k;
    wAddCon s1 sum 1 tmp';
    wMul p sum s1 tmp';
    z := 2;
    wDiv t1 p z tmp';
    i = t1 w+ k
  ).

Print getLargestZ.

(* for formulation *)
Definition wGetZ (i j:var) (tmp:var) :=
  let z := tmp in
  let z2 := 1+tmp in
  let zi := 2+tmp in
  let mul := 3+tmp in
  let ze := 4+tmp in
  let set := 5+tmp in
  let tmp' := 6+tmp in
  (
    wAssign z j;
    z2 := 2;
    set := 0;
    wFor' z
      (fun tmp2 =>
         wIf0' set
               (fun tmp3 =>
                  wAddCon zi z 1 tmp3;
                  wMul mul z zi tmp3;
                  wDiv ze mul z2 tmp3;
                  wIfLe' ze j
                        (fun tmp4 => wAssign i z;set := 1)
                        (fun tmp4 => nop tmp4)
                        tmp3
               )
               (fun tmp3 => nop tmp3)
               tmp2
            ;
        wDec z tmp2
      )
      tmp'
  ).

(* in while formulation *)
Definition wGetZ2 (i j:var) (tmp:var) :=
  let z := tmp in
  let z2 := 1+tmp in
  let zi := 2+tmp in
  let mul := 3+tmp in
  let ze := 4+tmp in
  let tmp' := 5+tmp in
  (
    wAssign z j;
    z2 := 2;
    while z do
      wAddCon zi z 1 tmp';
      wMul mul z zi tmp';
      wDiv ze mul z2 tmp';
      wIfLe' ze j
            (fun tmp2 => wAssign i z;z := 0)
            (fun tmp2 => nop tmp2)
            tmp'
            ;
      wDec z tmp'
    od
  ).

Definition wPi2 (i j:var) (tmp:var) :=
  let z := tmp in
  let z1 := 1+tmp in
  let zp := 2+tmp in
  let z2 := 3+tmp in
  let t2 := 4+tmp in
  let tmp' := 5+tmp in
  (
    wGetZ z j tmp';
    wAddCon z1 z 1 tmp';
    wMul zp z z1 tmp';
    z2 := 2;
    wDiv t2 zp z2 tmp';
    i = j w- t2
  ).

Definition wPi1 (i j:var) (tmp:var) :=
  let p := tmp in
  let tmp' := S tmp in
  (
    wPi2 p j tmp';
    i = j w- p
  ).

Definition wPush (S x : var) (tmp:var) :=
  let t := tmp in
  let Y := 1+tmp in
  let tmp' := 2+tmp in
  (
    wPi2 t S tmp';
    wGoed Y x t tmp';
    wPi1 t S tmp';
    wAddCon t t 1 tmp';
    wGoed S t Y tmp'
  ).

Definition wPop (S : var) (tmp:var) :=
  let n := tmp in
  let t := 1+tmp in
  let tmp' := 2+tmp in
  (
    wPi1 n S tmp';
    wIf0' n
      (fun tmp2 => nop tmp2)
      (fun tmp2 =>
         wDec n tmp2;
         wPi2 t S tmp2;
         wPi2 t S tmp2;
         wGoed S n t tmp2
      )
      tmp'
  ).

Definition wTop (x S:var) (tmp:var) :=
  (
    wPi2 x S tmp;
    wPi1 x S tmp
  ).

Definition wIsEmpty (b S:var) (tmp:var) :=
  let n := tmp in
  let t := 1+tmp in
  let tmp' := 2+tmp in
  (
    wPi1 n S tmp';
    t := 0;
    wIfGt' n t
      (fun tmp2 => b:=0)
      (fun tmp2 => b:=1)
      tmp'
  ).

(* Seite 73 *)
Definition wGeti (x A i m:var) (tmp:var) :=
  let B := tmp in
  let tmp' := 1+tmp in
  (
    wAssign B A;
    wAssign x m;
    wDec x tmp';
    wSub x x i;
    wFor' x
      (fun tmp2 => wPop B tmp2)
      tmp';
    wTop x B tmp'
  ).

Definition wSeti (A i b m:var) (tmp:var) :=
  let B := tmp in
  let z := 1+tmp in
  let t := 2+tmp in
  let t2 := 3+tmp in
  let tmp' := 4+tmp in
  (
    z := 0;
    wGoed B z z tmp';
    wAssign t m;
    wDec t tmp';
    wSub t t i;
    wFor' t
      (fun tmp2 =>
         wTop t2 A tmp2;
         wPush B t2 tmp2;
         wPop A tmp2
      )
      tmp';
    wPop A tmp';
    wPush A b tmp';
    wFor' t
      (fun tmp2 =>
         wTop t2 B tmp2;
         wPush A t2 tmp2;
         wPop B tmp2
      )
      tmp'
  ).

Definition wSize (x S:var) (tmp:var) :=
  (
    wPi1 x S tmp
  ).

(* Definition wAck (x y:var) (tmp:var) := *)
(*   ( *)
(*     S := 0; *)
(*     wPush S x tmp'; *)
(*     wPush S y tmp'; *)
(*     wSize s S tmp'; *)
(*     t := 1; *)
(*     while  *)
(*   ) *)

Definition wUniversal (g m vars:var) (tmp:var) :=
  let X := tmp in
  let z := 2+tmp in
  let S := 3+tmp in
  let two := 4+tmp in
  let three := 5+tmp in
  let four := 6+tmp in
  let term := 7+tmp in
  let type := 8+tmp in
  let t := 9+tmp in
  let cur := 10+tmp in
  let i := 11+tmp in
  let t2 := 12+tmp in
  let x3 := 13+tmp in
  let x4 := 14+tmp in
  let x5 := 15+tmp in
  let tmp' := 16+tmp in
  (
    X := 0;
    z := 0;
    wSeti X z m vars tmp';
    S := 0;
    term := 1;
    wAssign cur g;
    one := 1;
    two := 2;
    three := 3;
    four := 4;
    while term do
      wPi1 type cur tmp';
      wIf0' type
           (fun tmp2 =>
              wPi2 cur cur tmp2;
              wPi1 x3 cur tmp2;
              wPi2 t2 cur tmp2;
              wPi1 x4 t2 tmp2;
              wPi2 x5 t2 tmp2;
              wGeti t X x4 vars tmp2;
              wGeti t2 X x5 vars tmp2;
              t = t w+ t2;
              wSeti X x3 t vars tmp2
           )
           (fun tmp2 => nop tmp2)
           tmp';
      wIfEq' type one
           (fun tmp2 =>
              wPi2 cur cur tmp2;
              wPi1 x3 cur tmp2;
              wPi2 t2 cur tmp2;
              wPi1 x4 t2 tmp2;
              wPi2 x5 t2 tmp2;
              wGeti t X x4 vars tmp2;
              wGeti t2 X x5 vars tmp2;
              t = t w- t2;
              wSeti X x3 t vars tmp2
           )
           (fun tmp2 => nop tmp2)
           tmp';
      wIfEq' type two
           (fun tmp2 =>
              wPi2 cur cur tmp2;
              wPi1 t cur tmp2;
              wPi2 t2 cur tmp2;
              wSeti X t t2 vars tmp2
           )
           (fun tmp2 => nop tmp2)
           tmp';
      wIfEq' type three
           (fun tmp2 =>
              wPi2 i cur tmp2;
              wPi1 i i tmp2;
              wGeti t X i vars tmp2;
              wIfNeq'
                t z
                (fun tmp3 =>
                   wPush S cur tmp3;
                   wPi2 t cur tmp3;
                   wPi2 t t tmp3;
                   wPush S t tmp3
                )
                (fun tmp3 => nop tmp3)
                tmp2
           )
           (fun tmp2 => nop tmp2)
           tmp';
      wIfEq' type four
           (fun tmp2 =>
              wPi2 t cur tmp2;
              wPi2 t2 t tmp2;
              wPush S t2 tmp2;
              wPi1 t2 t tmp2;
              wPush S t2 tmp2
           )
           (fun tmp2 => nop tmp2)
           tmp';
      wIsEmpty t S tmp';
      wIf0' t
           (fun tmp2 => wTop cur S tmp2;wPop S tmp2)
           (fun tmp2 => term := 0)
           tmp'
    od;
    wGeti 0 X z vars tmp'
  ).


Definition emptyState := fun (_:var) => 0.

Definition wTest (P:whileP) (n:nat) :=
  match sigma n P emptyState with
    None => 42
  | Some s => s 0
  end.

Compute (whileInstruction (wUniversal 0 1 2 3)).
(* Compute (goedWhilePSize (wUniversal 0 1 2 3)). *)

Section Test.

  Definition wZTestProgram := (1 := 39;wGetZ 0 1 2).
  Definition wPi1TestProgram := (1 := 39;wPi1 0 1 2).
  Definition wPi2TestProgram := (1 := 39;wPi2 0 1 2).

  (* Z *)
  Compute (getLargestZ 39 39).
  (* Compute (goedWhileP (1 := 39)). *)
  (* Compute (goedWhileP (1 := 39;wPi1 0 1 2)). *)
  (* Compute (match *)
  (*             sigma 1583 *)
  (*                   (1 := 39;wGetZ 0 1 3) *)
  (*                   emptyState with *)
  (*             None => 42 *)
  (*           | Some s => s 0 *)
  (*           end). *)

  Definition wGoedTestProgram := (1 := 5;2:=3;wGoed 0 1 2 3).

  (* goed *)
  Compute (goed 5 3).
  Compute (wTest wGoedTestProgram 500).

  (* = *)
  Compute (match
              sigma 500
                    (1 := 38;2:=37;wIfEq 1 2 (0 := 13) (0 := 14) 3)
                    emptyState with
              None => 42
            | Some s => s 0
            end).

  (* < *)
  Compute (match
              sigma 500
                    (1 := 37;2:=37;wIfLt 1 2 (0 := 13) (0 := 14) 3)
                    emptyState with
              None => 42
            | Some s => s 0
            end).

  (* Mod *)
  Compute (match
              sigma 500
                    (1 := 180;2:=37;wMod 0 1 2 3)
                    emptyState with
              None => 42
            | Some s => s 0
            end).

  (* Div *)
  Compute (match
              sigma 50
                    (1 := 10;2:=2;wDiv 0 1 2 3)
                    emptyState with
              None => 42
            | Some s => s 0
            end).

  (* =0 *)
  Compute (match
              sigma 50
                    (2 := 1;
                    wIf0 2 (0:=42) (0:=43) 100)
                    emptyState with
              None => 0
            | Some s => s 0
            end).

  (* Mul *)
  Compute (match
              sigma 500
                    (0 := 2;1 := 3;
                    wMul 0 0 1 100)
                    emptyState with
              None => 42
            | Some s => s 0
            end).

  (* Pow *)
  Compute (match
              sigma 5000
                    (1 := 2;2:=10;wPow 0 1 2 3)
                    emptyState with
              None => 42
            | Some s => s 0
            end).

End Test.

Definition initState (n:nat) := fun (x:var) => if x then n else 0.
Definition evals (p:whileP) (i o:nat) := exists s, ϕ (initState i) p s /\ eq (s 0) o.
Definition computes (p:whileP) (f:nat->nat) := forall x, evals p x (f x).

Definition language := nat -> Prop.
Definition reducible (A B:language) := exists (f:nat->nat), (exists p, computes p f) /\ forall x, A x <-> B (f x).

Definition H0 := fun x => exists o, ϕ (initState x) (goedInv x) o.
Definition H := fun x => exists o, ϕ (initState (pi2 x)) (goedInv (pi1 x)) o.

Lemma compPi1: computes (wPi1 0 0 1) pi1.
Admitted.
Lemma compPi2: computes (wPi2 0 0 1) pi2.
Admitted.

(* Lemma compGoed: computes ( *)

Goal reducible H0 H.
Proof.
  exists (fun x => goed x x);split.
  - exists (wGoed 0 0 0 1). intros x. admit.
  - intros x. split.
    + intros []. cbv [H].
      exists x0.
      now destruct (goedBij2 x x) as [-> ->].
    + intros []. exists x0.
      now destruct (goedBij2 x x) as [-> ->] in H1.
Admitted.

(* S m n *)
(* Rice *)
(* fixpoint *)


From Coq Require Extraction.
From Coq Require Import ExtrHaskellNatInt.
From Coq Require Import ExtrHaskellBasic.

From Coq Require Import ExtrHaskellBasic.
From Coq Require Import ExtrHaskellNatNum.
(* From Coq Require Import ExtrHaskellNatInt. *)
From Coq Require Import ExtrHaskellNatInteger.
Extraction Language Haskell.

(* Extract Constant div => "div". *)

Extract Constant sqrt => "Prelude.floor Prelude.. Prelude.sqrt Prelude.. Prelude.fromIntegral".

Set Extraction Flag 2047.

(* Compute (goedWhilePSize wGoedTestProgram). *)

Extraction "WhileP" goedInv goedWhileP sigma emptyState
           wTest wGoed wPi1 wPi2 goedWhilePSize
           wPow wUniversal whileInstruction
           wGoedTestProgram wPi1TestProgram wPi2TestProgram wZTestProgram.




(*

data WhileP =
   WCon Var Prelude.Int
 | WAdd Var Var Var
 | WSub Var Var Var
 | WWhileP Var WhileP
 | WSeq WhileP WhileP deriving Prelude.Show



import Prelude

instance Show WhileP where
  show (WAdd i j k) = "x" ++ show i ++ " := x" ++ show j ++ " + x" ++ show k
  show (WSub i j k) = "x" ++ show i ++ " := x" ++ show j ++ " - x" ++ show k
  show (WCon i c) = "x" ++ show i ++ " := " ++ show c
  show (WSeq p1 p2) = show p1 ++ ";\n" ++ show p2
  show (WWhile i p1) = "whileP x" ++ show i ++ " != 0 do\n" ++ show p1 ++ "\nod"

main = do
  print (wTest wGoedTestProgram 500)

  print (goedWhileP wGoedTestProgram)


main = do
  Prelude.print (goedWhileP (WCon 0 42))
  Prelude.print (goedInv 4727);
  putStrLn (case sigma 5 (goedInv 4727) (\_ -> 0) of { Nothing -> "NonTerm"; Just s -> show (s 0) ++ "\n" ++ show (s 1)})



main = do
  Prelude.print (goedWhileP (WAdd 1 2 3))
  Prelude.putStrLn ("add: " ++ show (goedWhilePSize (WAdd 1 2 3)))
  Prelude.putStrLn ("mul: " ++ show (goedWhilePSize (wMul 0 1 2 3)))
  Prelude.putStrLn ("div: " ++ show (goedWhilePSize (wDiv 0 1 2 3)))
  Prelude.putStrLn ("pow: " ++ show (goedWhilePSize (wPow 0 1 2 3)))
  Prelude.putStrLn ("goed: " ++ show (goedWhilePSize wGoedTestProgram))
  Prelude.putStrLn ("pi2: " ++ show (goedWhilePSize wPi2TestProgram))
  Prelude.putStrLn ("pi1: " ++ show (goedWhilePSize wPi1TestProgram))

-- add: 4
-- mul: 128
-- div: 2097152
-- pow: 2048
-- goed: 33.554.432
-- pi2: 2.199.023.255.552
-- pi1: 4.398.046.511.104
 *)

(* Lemma goedWhilePInj  *)
