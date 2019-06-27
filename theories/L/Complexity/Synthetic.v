From Undecidability.L Require Import Tactics.LTactics Computability.Synthetic Prelim.MoreList Prelim.MoreBase Datatypes.LBinNums.
Require Import CMorphisms.
From Undecidability.L.Complexity Require Import Monotonic.
Record inO (f g : nat -> nat) : Type :=
  {
    c__inO : nat;
    n__inO : nat;
    inO__correct : forall n, n__inO <= n -> f n <= c__inO * g n
  }.

Arguments inO__correct : clear implicits.
Arguments inO__correct {_ _}.

Notation " f ∈O g" := (inO f g) (at level 70).

Instance inO_PreOrder : PreOrder inO.
Proof.
  split.
  -exists 1 0. intros. Lia.lia.
  -intros f g h [c n0 H] [c' n0' H'].
   exists (c*c') (max n0 n0').
   intros n Hn.
   rewrite H,H'. all:Lia.lia.
Qed.

Record ino (f g : nat -> nat) : Type :=
  {
    ino__correct : forall c__ino, 0 < c__ino -> {n__ino | forall n, n__ino <= n -> f n < c__ino * g n}
  }.

Arguments ino__correct : clear implicits.
Arguments ino__correct {_ _}.

Notation " f ∈o g" := (ino f g) (at level 70).

Definition n__ino f g (H:f ∈o g) c0 (H' : 0 < c0) : nat := proj1_sig (ino__correct H c0 H').

Definition correct_n__ino f g (H:f ∈o g) c0 (H' : 0 < c0)
  : forall n, n__ino H H' <= n -> f n < c0 * g n := proj2_sig (ino__correct H c0 H').

Lemma ino_inO_incl f g :
  f ∈o g -> f ∈O g.
Proof.
  intros [H].
  specialize (H 1 ltac:(Lia.lia)) as (c__ino&H).
  exists 1 c__ino. intros. apply Nat.lt_le_incl. easy.
Qed.

Inductive is_computable_time {A} {t : TT A} (a : A) fT : Prop :=
  C : computableTime' a fT -> is_computable_time a fT.

Definition L_decidable_inTime {X} `{R :registered X} (P : X -> Prop) (fT : nat -> nat) :Prop := Eval cbn [timeComplexity] in
  exists f : X -> bool, is_computable_time (t:=TyArr (TyB X) (TyB bool)) f
                                  (fun x _ => (fT (L.size (enc x)),tt)) /\ forall x, P x <-> f x = true.

Definition inTimeO {X} `{R :registered X} P f :=
  exists f', L_decidable_inTime P f' /\ inhabited (f' ∈O f).

Notation "P ∈TimeO f" := (inTimeO P f) (at level 70).

Definition inTimeo {X} `{R :registered X} P f :=
  exists f', L_decidable_inTime P f' /\ inhabited (f' ∈o f).

Notation "P ∈Timeo f" := (inTimeo P f) (at level 70).


(** Properties *)


(** Inclusion *)
Lemma inTime_mono f g X (_ : registered X):
  f ∈O g -> forall (P : X -> Prop), P ∈TimeO f -> P ∈TimeO g.
Proof.
  intros H P [? [? []]]. unfold inTimeO.
  eexists _. split. 2:constructor.
  2:setoid_rewrite <- H. all:eassumption.
Qed.

Lemma inO_add_l f1 f2  g:
  f1 ∈O g -> f2 ∈O g -> (fun n => f1 n + f2 n) ∈O g.
Proof.
  intros [c1 n1 H1] [c2 n2 H2].
  eexists (c1 + c2) (max n1 n2).
  intros.
  rewrite H1,H2.
  all:Lia.lia.
Qed.

Require Import CMorphisms.
Instance inO_pointwise_leq : Proper ( flip (pointwise_relation _ le)  ==> eq ==> Basics.arrow) inO.
Proof.
  intros ? ? R1 ? ? <- [c1 n1 H'].
  eexists c1 n1. hnf in R1. intros. rewrite R1,H'. all:easy.
Qed.

Lemma inO_mul_c_l c f1  g:
  f1 ∈O g -> (fun n => c * f1 n) ∈O g.
Proof.
  intros [c1 n1 H1].
  eexists (c1*c) (n1).
  intros.
  rewrite H1.
  all:Lia.lia.
Qed.

Lemma inO_mul_c_r c f1  g:
  f1 ∈O g -> (fun n => f1 n * c) ∈O g.
Proof.
  intros [c1 n1 H1].
  eexists (c1*c) (n1).
  intros.
  rewrite H1.
  all:Lia.lia.
Qed.

Lemma inO_c c n0 f':
  (forall n', n0 <= n' -> 1 <= f' n') ->  
  (fun _ => c ) ∈O f'.
Proof.
  eexists (c) (n0).
  intros. rewrite <- H. all:Lia.nia.
Qed.

Lemma inO_leq n0 f' g:
  (forall n', n0 <= n' -> f' n' <= g n') ->  
  f' ∈O g.
Proof.
  eexists 1 (n0).
  intros. rewrite <- H. all:Lia.nia.
Qed.

Lemma inO_mul_l f1 f2  g1 g2:
  f1 ∈O g1 -> f2 ∈O g2 -> (fun n => f1 n * f2 n) ∈O (fun n => g1 n * g2 n).
Proof.
  intros [c1 n1 H1] [c2 n2 H2].
  eexists (c1 * c2) (max n1 n2).
  intros.
  rewrite H1,H2.
  all:Lia.lia.
Qed.

Lemma inO_comp_l f1 f2  g1 g2:
  f1 ∈O g1 -> f2 ∈O g2 ->
  monotonic f1 ->
  (forall x, x <= g2 x ) ->
  (forall c, (fun x => g1 (c*x)) ∈O g1) -> (fun n => f1 (f2 n)) ∈O (fun n => g1 (g2 n)).
Proof.
  intros [c1 n1 H1] [c2 n2 H2] mono2 H' H.
  specialize (H (c2+n1)) as [c2' n2' H].
  eexists (c1 * c2') (max (max 1 n2') n2).
  intros.
  etransitivity.
  {hnf in mono2. rewrite mono2. reflexivity. transitivity ((c2+n1)*(g2 n)). 2:reflexivity. rewrite H2. Lia.nia. easy. }
  specialize (H' n).
  setoid_rewrite H1. 2:Lia.nia.
  rewrite H. Lia.nia. Lia.nia.
Qed.
  
(** Only possible with the non-Prop-version of bigO, but not needed in our proofs*)
Lemma inO__bound f g (H:f ∈O g) : { c0 & forall n, f n <= c0 + c__inO H * g n}.
Proof.
  destruct H as [c0 n0 H]. cbn.
  exists (maxl (map f (natsLess n0))).
  intros n.
  decide (n0<=n).
  -rewrite H. all:Lia.nia.
  -rewrite (@maxl_leq (f n) (map f (natsLess n0))). Lia.nia. apply in_map_iff. setoid_rewrite natsLess_in_iff. exists n. intuition.          
Qed.

(** *** Time Constructibility *)
(** TODO: As we might want to project out the term, we don't use inTimeO to avoid the elim-restriction... *)
Definition timeConstructible (f:nat -> nat) := Eval cbn [timeComplexity] in
      { f' : nat -> nat &
                 (f' ∈O f)
                 * computableTime' (fun n => N.of_nat (f n)) (fun n _ => (f' n,tt))}%type.

Definition timeConstructible_computableTime' f (H:timeConstructible f) :
  computableTime' (fun n => N.of_nat (f n)) (fun n _ => (projT1 H n,tt))
  := snd (projT2 H).

Definition timeConstructible_inO f (H:timeConstructible f) :
  projT1 H ∈O f := fst (projT2 H).
