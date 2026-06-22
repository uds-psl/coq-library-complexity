Require Export Undecidability.Shared.Libs.PSL.Base Lia Arith PArith.
From Complexity.Libs Require Export MoreList.

(* * Preliminaries *)

#[global]
Instance le_preorder : PreOrder le.
Proof.
  constructor. all:cbv. all:intros;lia. 
Qed.

#[global]
Instance S_le_proper : Proper (le ==> le) S.
Proof.
  cbv. fold plus. intros. lia.
Qed.

#[global]
Instance plus_le_proper : Proper (le ==> le ==> le) plus.
Proof.
  cbv. fold plus. intros. lia.
Qed.

#[global]
Instance mult_le_proper : Proper (le ==> le ==> le) mult.
Proof.
  cbv. intros. 
  apply Nat.mul_le_mono. all:eauto. 
Qed.

#[global]
Instance pow_le_proper : Proper (le ==> eq ==> le) Nat.pow.
Proof.
  cbv - [Nat.pow]. intros. subst. apply Nat.pow_le_mono_l. easy.
Qed.

#[export]
Instance proper_lt_mul : Proper (lt ==> eq ==> le) Nat.mul. 
Proof. 
  intros a b c d e f. nia.
Qed. 

#[export]
Instance proper_lt_add : Proper (lt ==> eq ==> le) Nat.add.
Proof. 
  intros a b c d e f. nia. 
Qed. 

#[export]
Instance proper_le_pow : Proper (le ==> eq ==> le) Nat.pow.
Proof. 
  intros a b H1 d e ->. apply Nat.pow_le_mono_l, H1. 
Qed. 

#[export]
Instance mult_lt_le : Proper (eq ==> lt ==> le) mult. 
Proof. 
  intros a b -> d e H. nia. 
Qed.

#[export]
Instance add_lt_lt : Proper (eq ==> lt ==> lt) Nat.add. 
Proof. 
  intros a b -> c d H. lia.
Qed.

#[export]
Instance le_lt_impl : Proper (le --> eq ==> Basics.impl) lt. 
Proof. 
  intros a b H d e ->. unfold Basics.flip in H. unfold Basics.impl. lia. 
Qed.

#[export]
Instance lt_le_impl : Proper (lt --> eq ==> Basics.impl) le. 
Proof. 
  intros a b H d e ->. unfold Basics.flip in H. unfold Basics.impl. lia.  
Qed.


#[global]
Instance max_le_proper : Proper (le ==> le ==> le) max.
Proof.
repeat intro. repeat eapply Nat.max_case_strong;lia.
Qed.

#[global]
Instance min_le_proper : Proper (le ==> le ==> le) min.
Proof.
repeat intro. repeat eapply Nat.min_case_strong;lia.
Qed.

#[global]
Instance Nat_log2_le_Proper : Proper (le ==> le) Nat.log2.
Proof.
  repeat intro. apply Nat.log2_le_mono. assumption.
Qed.

#[global]
Instance Pos_to_nat_le_Proper : Proper (Pos.le ==> le) Pos.to_nat.
Proof.
  repeat intro. apply Pos2Nat.inj_le. assumption.
Qed.

#[global]
Instance Pos_add_le_Proper : Proper (Pos.le ==> Pos.le ==>Pos.le) Pos.add.
Proof.
  repeat intro. eapply Pos.add_le_mono. 3:eauto. all:eauto. 
Qed.

Lemma nth_error_Some_lt A (H:list A) a x : nth_error H a = Some x -> a < |H|.
Proof.
  intros eq. revert H eq. induction a;intros;destruct H;cbn in *;inv eq. lia. apply IHa in H1. lia.
Qed.

Definition maxP (P:nat -> Prop) m := P m /\ (forall m', P m' -> m' <= m). 

Lemma sumn_le_bound l c :
  (forall n, n el l -> n <= c) -> sumn l <= length l * c.
Proof.
  induction l;cbn. easy.
  intros H.
  rewrite <- IHl,<- H. all:now eauto.
Qed.

Lemma sumn_map_le_pointwise X (xs:list X) f1 f2:
  (forall x, x el xs -> f1 x <= f2 x) -> sumn (map f1 xs) <= sumn (map f2 xs).
Proof.
  intros Hle. 
  induction xs. easy.
  cbn. rewrite Hle. 2:now trivial with datatypes.
  rewrite IHxs. easy. intros. eauto with datatypes.
Qed.

Lemma sumn_map_mono (X : Type) (f1 f2 : X -> nat) l : (forall x, x el l -> f1 x <= f2 x) -> sumn (map f1 l) <= sumn (map f2 l).
Proof. 
  intros H. induction l; cbn; [lia | ]. 
  rewrite IHl, H by auto. lia. 
Qed.

Lemma sumn_map_const (X : Type) c (l : list X) : sumn (map (fun _ => c) l) = |l| * c. 
Proof. 
  induction l; cbn; [lia | ]. 
  rewrite IHl. lia. 
Qed.
