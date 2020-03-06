Require Import PslBase.Base.
Require Import Lia. 
From Undecidability.L Require Import L.
From Undecidability.Shared Require Import Prelim.
From Undecidability.L.Complexity Require Import Tactics.

(** *Results regarding lists *)
Section tabulate.
  Variable (A : Type).
  Fixpoint tabulate (f : nat -> A) (n : nat): list A := match n with 0 => []
                                                                      | S n => tabulate f n ++ [f n]
                                                                end. 

  Lemma tabulate_length (f : nat -> A)  (n : nat) : |tabulate f n| = n. 
  Proof. 
    induction n; cbn.
    - reflexivity. 
    - rewrite app_length, IHn. cbn;lia. 
  Qed. 

  Lemma tabulate_nth (f : nat -> A) (n : nat) : forall k, k < n -> nth_error (tabulate f n) k = Some (f k). 
  Proof.
    intros. induction n. 
    - lia. 
    - destruct (Nat.eqb k n) eqn:H1; dec_bool.
      + rewrite H1 in *; clear H1. cbn. rewrite nth_error_app2, tabulate_length. 2: specialize (tabulate_length f n); lia. 
        rewrite Nat.sub_diag; cbn; reflexivity.  
      + assert (k < n) by lia. clear H1 H. cbn. rewrite nth_error_app1. 2: now rewrite tabulate_length. 
        now apply IHn. 
  Qed. 

  Lemma tabulate_In (f : nat -> A) (n : nat) : forall a, a el tabulate f n <-> exists k, k < n /\ f k = a. 
  Proof.
    specialize (@tabulate_nth f n) as H1. 
    intros a. split.
    - intros (n0 & H2)%In_nth_error.
      assert (n0 < n). { rewrite <- tabulate_length with (f := f). now apply nth_error_Some_lt with (x:=a). }
      exists n0. split; [assumption|]. 
      specialize (H1 n0 H). congruence. 
    - intros (k & H2 & H3). specialize (H1 k H2).  
      rewrite <- H3; eapply nth_error_In, H1. 
  Qed. 
End tabulate. 

Section subsequence.
  Variable (X : Type).
  Definition subsequence (A B : list X) := exists C D, B = C ++ A ++ D.
  Notation "A 'subs' B" := (subsequence A B)(at level 70).

  Lemma subsequence_incl (A B : list X) : A subs B -> incl A B.
  Proof. 
    induction B. 
    - unfold subsequence. destruct A; cbn; try firstorder.
      intros (C & D & H). destruct C; cbn in H; congruence.   
    - intros (C & D & H). intros x xel. destruct C. 
      + cbn in H. rewrite H. firstorder. 
      + cbn in H. assert (x0 = a) as -> by congruence.  
        right. apply IHB; [|assumption]. exists C,D. congruence. 
  Qed.
End subsequence. 

Lemma dupfree_nthe (X : Type) (l : list X) : dupfree l <-> forall i j a b, nth_error l i = Some a -> nth_error l j = Some b -> i <> j -> a <> b.
Proof. 
  split.
  - induction 1. 
    + intros. destruct i; cbn in H; congruence.  
    + intros. destruct i, j. 
      * congruence. 
      * cbn in H1, H2. apply nth_error_In in H2. assert (x = a) by congruence. rewrite H4 in H. congruence. 
      * cbn in H1, H2. apply nth_error_In in H1. assert (x = b) by congruence. rewrite H4 in H. congruence. 
      * cbn in H1, H2. apply IHdupfree with (i:= i) (j:=j); [assumption | assumption | congruence]. 
  - induction l. 
    + intros. constructor. 
    + intros. constructor. 
      * intros Hel%In_nth_error.  destruct Hel as (j & Hel). 
        specialize (H 0 (S j) a a). cbn in H. apply H; firstorder. 
      * apply IHl. firstorder. apply H with (i := S i) (j:= S j); firstorder. 
Qed. 

Section remove.
  Variable (X : Type).
  Context (eqdec : (forall x y: X, dec (x = y))).
  Lemma in_remove_iff (l : list X) (a b : X) : a el remove eqdec b l <-> a el l /\ a <> b.
  Proof.
    revert a. induction l; intros; cbn.
    - tauto. 
    - destruct (eqdec b a).
      + split; [firstorder | ]. intros [[-> | H1] H2]; [congruence|]. now apply IHl. 
      + split; [ firstorder; congruence | firstorder ].
  Qed. 

  Lemma remove_length (l : list X) (a : X) : |remove eqdec a l| <= |l|.
  Proof.
    induction l; cbn.
    - lia.
    - destruct eqdec; cbn; lia. 
  Qed. 

  Lemma remove_length_el (l : list X) (a : X) : a el l -> |remove eqdec a l| < |l|.
  Proof.
    induction l.
    - intros [].
    - intros [-> | H1].
      + cbn. destruct (eqdec a a); [specialize (remove_length l a); lia | congruence].
      + cbn. destruct (eqdec a a0); [specialize (remove_length l a); lia | cbn; firstorder ].  
  Qed. 
End remove.
