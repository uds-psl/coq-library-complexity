From Undecidability Require Import PSL.Prelim L.Prelim.MoreBase.
From Complexity.Complexity Require Import Monotonic.
Require Import smpl.Smpl.
Require Import Nat Lia.

(** ** O notation *)

Definition inO (f g : nat -> nat) : Prop := exists c n0, forall n, n0 <= n -> f n <= c * g n.

Notation " f ∈O g" := (inO f g) (at level 70).

#[export]
Instance inO_PreOrder : PreOrder inO.
Proof.
  split.
  -exists 1,0. intros. Lia.lia.
  -intros f g h (c&n0&H) (c'&n0'&H').
   exists (c*c'),(max n0 n0').
   intros n Hn.
   rewrite H,H'. all:Lia.lia.
Qed.


#[export]
Instance inO_pointwise_leq : Proper ( Basics.flip (pointwise_relation _ le)  ==>  (pointwise_relation _ le) ==> Basics.impl) inO.
Proof.
  intros ? ? R1 ? ? R2. unfold inO. hnf in R1,R2|-*.
  setoid_rewrite R1. setoid_rewrite R2. easy. 
Qed.

#[export]
Instance inO_pointwise_eq: Proper ((pointwise_relation _ eq) ==> (pointwise_relation _ eq) ==> iff) inO.
Proof.
  intros ? ? R1 ? ? R2. hnf in R1,R2.
  unfold inO. setoid_rewrite R1. setoid_rewrite R2. easy.
Qed.


Lemma inO_add_l f1 f2  g:
  f1 ∈O g -> f2 ∈O g -> (fun n => f1 n + f2 n) ∈O g.
Proof.
  intros (c1&n1&H1) (c2&n2&H2).
  eexists (c1 + c2),(max n1 n2).
  intros.
  rewrite H1,H2.
  all:Lia.lia.
Qed.

Lemma inO_mul_c_l c f1  g:
  f1 ∈O g -> (fun n => c * f1 n) ∈O g.
Proof.
  intros (c1&n1&H1).
  eexists (c1*c), (n1).
  intros.
  rewrite H1.
  all:Lia.lia.
Qed.

Lemma inO_mul_c_r c f1  g:
  f1 ∈O g -> (fun n => f1 n * c) ∈O g.
Proof.
  intros (c1&n1&H1).
  eexists (c1*c),(n1).
  intros.
  rewrite H1.
  all:Lia.lia.
Qed.


Lemma inO_c c f':
  (fun _ => 1) ∈O f' ->  
  (fun _ => c ) ∈O f'.
Proof.
  intros H'.
  assert (H:c<= 1*c) by lia.
  setoid_rewrite H. eapply inO_mul_c_r. easy.
Qed.
(*
Lemma inO_c c n0 f':
  (forall n', n0 <= n' -> 1 <= f' n') ->  
  (fun _ => c ) ∈O f'.
Proof.
  eexists (c),(n0).
  intros. rewrite <- H. all:Lia.nia.
Qed. *)

Lemma inO_leq n0 f' g:
  (forall n', n0 <= n' -> f' n' <= g n') ->  
  f' ∈O g.
Proof.
  eexists 1,(n0).
  intros. rewrite <- H. all:Lia.nia.
Qed.

Smpl Create inO.

Smpl Add 11 (smpl monotonic) : inO.

Smpl Add 10 (first [ simple eapply inO_add_l | simple eapply inO_mul_c_l | simple eapply inO_mul_c_r | progress (eapply inO_c) | reflexivity]) (*
                    | simple eapply inO_c with (n0:=1);intro;try rewrite <- !f_geq_n;Lia.nia
                                 | inO_leq 1])*) : inO.

Ltac smpl_inO := repeat (smpl inO).

Lemma inO_mul_l f1 f2  g1 g2:
  f1 ∈O g1 -> f2 ∈O g2 -> (fun n => f1 n * f2 n) ∈O (fun n => g1 n * g2 n).
Proof.
  intros (c1&n1&H1) (c2&n2&H2).
  eexists (c1 * c2),(max n1 n2).
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
  intros (c1&n1&H1) (c2&n2&H2) mono2 H' H.
  specialize (H (c2+n1)) as (c2'&n2'&H).
  eexists (c1 * c2'),(max (max 1 n2') n2).
  intros.
  etransitivity.
  {hnf in mono2. rewrite mono2. reflexivity. transitivity ((c2+n1)*(g2 n)). 2:reflexivity. rewrite H2. Lia.nia. lia. }
  specialize (H' n).
  setoid_rewrite H1. 2:Lia.nia.
  rewrite H. Lia.nia. Lia.nia.
Qed.



Lemma inO__bound f g (H:f ∈O g) : exists c, forall n, f n <= c + c * g n.
Proof.
  destruct H as (c0&n0&H). cbn.
  exists (max c0 (maxl (map f (natsLess n0)))).
  intros n.
  decide (n0<=n).
  -rewrite H. all:Lia.nia.
  -rewrite (@maxl_leq (f n) (map f (natsLess n0))). Lia.nia. apply in_map_iff. setoid_rewrite natsLess_in_iff. exists n. lia.
Qed.

(** *** smallO *)

(** This variant of smallo does not need real nubers, as we moved the constant to the other side *)
Definition ino (f g : nat -> nat) : Prop := forall c__inv, exists n0 , forall n, n0 <= n -> c__inv * f n < g n.

Notation " f ∈o g" := (ino f g) (at level 70).

(*Definition n__ino f g (H:f ∈o g) c0 (H' : 0 < c0) : nat := proj1_sig (ino__correct H c0 H').

Definition correct_n__ino f g (H:f ∈o g) c0 (H' : 0 < c0)
  : forall n, n__ino H H' <= n -> f n < c0 * g n := proj2_sig (ino__correct H c0 H').
 *)

Lemma ino_inO_incl f g :
  f ∈o g -> f ∈O g.
Proof.
  intros H.
  specialize (H 1) as (c__ino&H).
  exists 1,c__ino. intros ? ?%H. lia.
Qed.


(** ** O(poly)*)

Definition inOPoly (f : nat -> nat) : Prop :=
  exists n, f ∈O (fun x => x ^ n).


Lemma inOPoly_c c: inOPoly (fun _ => c).
Proof.
  exists 1. eapply inO_c. cbn. eapply (inO_leq (n0:=1)). intros. lia.
Qed.

Lemma inOPoly_x: inOPoly (fun x => x).
Proof.
  exists 1. cbn. eapply (inO_leq (n0:=1)). intros. lia.
Qed.

Lemma inOPoly_add f1 f2: inOPoly f1 -> inOPoly f2 -> inOPoly (fun x => f1 x + f2 x).
Proof.
  intros (n1&?) (n2&?).
  exists (max n1 n2). 
  eapply inO_add_l.
  all:etransitivity;[eassumption|].
  all:eapply inO_leq with (n0:=1).
  all:intros ? ?.
  all:eapply Nat.pow_le_mono_r. all:Lia.nia.
Qed.

Lemma inOPoly_mul f1 f2: inOPoly f1 -> inOPoly f2 -> inOPoly (fun x => f1 x * f2 x).
Proof.
  intros (n1&?) (n2&?).
  exists (n1+n2). 
  transitivity (fun x : nat => x ^ n1 * x^n2).
  1:now eauto using inO_mul_l.
  all:eapply inO_leq with (n0:=0).
  all:intros ? _.
  rewrite Nat.pow_add_r. Lia.nia.
Qed.

Lemma inOPoly_pow f c: inOPoly f -> inOPoly (fun x => f x ^ c).
Proof.
  intros (n&H). exists (n*c).
  destruct H as (n0 & n1&H).
  eexists _, n1.
  intros ? H'%H. rewrite Nat.pow_le_mono_l. 2:eassumption.
  rewrite Nat.pow_mul_l,Nat.pow_mul_r. reflexivity.
Qed.

Lemma inOPoly_S f : inOPoly f -> inOPoly (fun x => S (f x)). 
Proof. 
  intros H. eapply (@inOPoly_add (fun _ => 1) f). 2: apply H. 
  apply inOPoly_c. 
Qed.

Lemma inOPoly_comp f1 f2: monotonic f1 -> inOPoly f1 -> inOPoly f2 -> inOPoly (fun x => f1 (f2 x)).
Proof.
  intros ? (n1&?) (n2&?).
  exists ((max 1 n2)*n1). 
  etransitivity.
  {eapply inO_comp_l with (g2:=(fun x => x ^(max 1 n2))).
   1,3:eassumption.
   -rewrite H1. apply inO_leq with (n0:=1). intros.
    eapply Nat.pow_le_mono;lia.
   -intros. replace x with (x^1) at 1 by (cbn;Lia.nia).
    decide (x=0). 2:now eapply Nat.pow_le_mono;Lia.nia.
    subst x. rewrite !Nat.pow_0_l. all:Lia.nia.
   -cbn beta. intros c.
    exists (c^n1),0. intros.
    rewrite Nat.pow_mul_l. reflexivity.
  }
  cbn beta.
  eapply inO_leq with (n0:=0). intros.
  rewrite Nat.pow_mul_r. reflexivity.
Qed.

Smpl Add 10 (first [ simple eapply inOPoly_add | simple eapply inOPoly_S | simple eapply inOPoly_mul | simple eapply inOPoly_c | simple eapply inOPoly_pow | simple eapply inOPoly_x | eassumption])  : inO.


#[export]
Instance inO_inOPoly_trans : Proper (Basics.flip inO ==> Basics.impl) inOPoly.
Proof.
  intros ? ? ? [? R2]. unfold inOPoly. eexists. setoid_rewrite <- R2. easy.
Qed.


#[export]
Instance inOPoly_pointwise_leq: Proper (Basics.flip (pointwise_relation _ le) ==> Basics.impl) inOPoly.
Proof.
  unfold inOPoly.
  intros ? ? R1. hnf in |-*. setoid_rewrite R1. easy.
Qed.

#[export]
Instance inOPoly_pointwise_eq: Proper ((pointwise_relation _ eq) ==> iff) inOPoly.
Proof.
  unfold inOPoly. intros ? ? R1. hnf. setoid_rewrite R1. easy.
Qed.
