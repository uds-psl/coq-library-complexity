From PslBase Require Import Base. 
From PslBase Require Import Vectors.Vectors. 
From Undecidability.L.Complexity.Cook Require Import Prelim FlatPR PR_homomorphisms. 
From Undecidability.L.Complexity.Cook Require Import BinaryPR.
Require Import Lia.

Section fixInstance. 
  Variable (fpr : FlatPR). 

  Notation Sigma := (Sigma fpr).
  Notation offset := (offset fpr).
  Notation width := (width fpr).
  Notation init := (init fpr).
  Notation windows := (windows fpr).
  Notation final := (final fpr).
  Notation steps := (steps fpr). 

  (*we first do the reduction for wellformed instances, satisfying the syntactic requirements *)
  Context (A : FlatPR_wellformed fpr). 
  Context (A1 : Sigma > 0). (*instances without this property are trivial no instances *)
  
  Definition h' (x : nat) := if leb (S x) Sigma then repEl x false ++ [true] ++ repEl (Sigma - x -1) false
                                                else repEl Sigma false. 

  Lemma h'_length (x : nat) : |h' x| = Sigma. 
  Proof. 
    unfold h'. destruct leb eqn:H. 
    - rewrite !app_length, !repEl_length. apply leb_complete in H. cbn. nia. 
    - now rewrite repEl_length.
  Qed. 

  Lemma repEl_app_inv (X : Type) (a : X) s1 s2 n : repEl n a = s1 ++ s2 -> exists n1 n2, s1 = repEl n1 a /\ s2 = repEl n2 a /\ n1 + n2 = n. 
  Proof. 
    revert s1 s2.  induction n. 
    - cbn. destruct s1, s2; cbn; try congruence. intros _. exists 0, 0; now cbn.  
    - cbn. destruct s1. 
      + cbn. destruct s2; cbn; [ congruence | ]. 
        intros H. inv H. exists 0, (S n); now cbn. 
      + intros. cbn in H. inv H. apply IHn in H2 as (n1 & n2 & -> & -> & <-). 
        exists (S n1), n2; now cbn. 
  Qed. 

  Lemma h'_inv1 (x n : nat) : h' x = repEl n false ++ [true] ++ repEl (Sigma - n -1) false -> x = n. 
  Proof. 
    intros. unfold h' in H. 
    destruct leb eqn:H1. 
    - clear H1. revert H.  generalize (Sigma - x- 1). generalize (Sigma - n -1). 
      revert n. induction x; intros. 
      + destruct n; cbn in H; [reflexivity | congruence]. 
      + destruct n; cbn in H; [ congruence | ]. inv H. now apply IHx in H1.
    - destruct (le_lt_dec n Sigma). 
      + assert (|repEl n false| <= |repEl Sigma false|) by (now rewrite !repEl_length). 
        apply list_length_split1 in H0 as (s1 & s2 & H0 & _ & H2). rewrite H2 in H. 
        apply app_eq_length in H as (_ & H); [ | apply H0]. 
        apply repEl_app_inv in H2 as (n1 & n2 & -> & -> & H2).   
        destruct n2; cbn in H; congruence. 
      + match type of H with ?a = ?b => assert (|a| = |b|) by congruence end. 
        rewrite !app_length, !repEl_length in H0. cbn in H0. lia. 
  Qed. 

  Definition h (x : list nat) := concat (map h' x). 

  Lemma h_uniform_homomorphism : uniform_homomorphism h. 
  Proof. 
    split; [ | split].
    + unfold homomorphism. intros. unfold h. now rewrite map_app, concat_app. 
    + intros. unfold h. cbn. rewrite !app_nil_r. now rewrite !h'_length. 
    + intros. cbn. rewrite app_length, h'_length. cbn. lia. 
  Qed. 

  Lemma h_bounded_injective : bounded_injectivity Sigma (hsingle h). 
  Proof. 
    unfold bounded_injectivity. intros. 
    unfold hsingle in H0. cbn in H0. rewrite !app_nil_r in H0. 
    symmetry in H0. unfold h' in H0. SearchAbout leb. erewrite (leb_correct (S n1)) in H0.  
    - now apply h'_inv1 in H0. 
    - lia. 
  Qed. 

  (*we now get the reduction for the case that the instance we reduce from is wellformed *)
  Lemma reduction_wf : FlatPRLang fpr <-> BinaryPRLang (hBinaryPR h fpr). 
  Proof. 
    specialize (h_bounded_injective) as F1. 
    specialize (h_uniform_homomorphism) as F2. 
    split; intros. 
    - destruct H as (_ & sf & H1 & H2 & H3).
      split; [ apply FlatPR_homomorphism_wf; auto | ]. 
      apply FlatPR_homomorphism_iff; eauto. 
    - destruct H as (_ & H1).
      split; [ apply A | ]. 
      apply FlatPR_homomorphism_iff in H1; eauto. 
  Qed. 
End fixInstance. 


