From PslBase Require Import Base. 
From PslBase Require Import Vectors.Vectors. 
From Undecidability.L.Complexity.Cook Require Import Prelim BinaryPR FlatPR FlatPR_homomorphisms. 
From Undecidability.L.Complexity.Cook Require Import FlatPR.
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
    symmetry in H0. unfold h' in H0. erewrite (leb_correct (S n1)) in H0.  
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

Definition ofFlatType_dec (b a : nat) := leb (S a) b.
Definition list_ofFlatType_dec (t : nat)  (s : list nat) := forallb (ofFlatType_dec t) s. 

Definition PRWin_of_size_dec width (win : PRWin nat) := Nat.eqb (|prem win|) width && Nat.eqb (|conc win|) width.
Definition PRWin_ofFlatType_dec (Sigma : nat) (win : PRWin nat) := list_ofFlatType_dec Sigma (prem win) && list_ofFlatType_dec Sigma (conc win). 

Lemma leb_iff a b : leb a b = true <-> a <= b. 
Proof. 
  split; intros. 
  - now apply leb_complete. 
  - now apply leb_correct. 
Qed.

Lemma list_ofFlatType_dec_correct s t : list_ofFlatType_dec t s = true <-> list_ofFlatType t s. 
Proof. 
  unfold list_ofFlatType_dec, list_ofFlatType. rewrite forallb_forall. 
  unfold ofFlatType_dec. setoid_rewrite leb_iff. 
  split; intros H; intros; now apply H.
Qed. 

Lemma PRWin_of_size_dec_correct width win : PRWin_of_size_dec width win = true <-> PRWin_of_size win width. 
Proof. 
  unfold PRWin_of_size, PRWin_of_size_dec. rewrite andb_true_iff. rewrite <- !(reflect_iff _ _ (Nat.eqb_spec _ _ )). easy.
Qed. 

Lemma PRWin_ofFlatType_dec_correct win Sigma : PRWin_ofFlatType_dec Sigma win = true <-> PRWin_ofFlatType Sigma win. 
Proof. 
  unfold PRWin_ofFlatType_dec, PRWin_ofFlatType. rewrite andb_true_iff. 
  rewrite !list_ofFlatType_dec_correct. easy. 
Qed. 

Definition FlatPR_wf_dec (fpr : FlatPR) := 
  leb 1 (width fpr) 
  && leb 1 (offset fpr)
  && Nat.eqb (Nat.modulo (width fpr) (offset fpr)) 0
  && leb (width fpr) (|init fpr|)
  && forallb (PRWin_of_size_dec (width fpr)) (windows fpr)
  && Nat.eqb (Nat.modulo (|init fpr|) (offset fpr)) 0
  && list_ofFlatType_dec (Sigma fpr) (init fpr)
  && forallb (list_ofFlatType_dec (Sigma fpr)) (final fpr)
  && forallb (PRWin_ofFlatType_dec (Sigma fpr)) (windows fpr). 

Lemma FlatPR_wf_dec_correct (fpr : FlatPR) : FlatPR_wf_dec fpr = true <-> FlatPR_wellformed fpr. 
Proof. 
  unfold FlatPR_wf_dec, FlatPR_wellformed. rewrite !andb_true_iff, !and_assoc.
  rewrite !leb_iff. rewrite <- !(reflect_iff _ _ (Nat.eqb_spec _ _ )).  
  rewrite !forallb_forall. 
  setoid_rewrite PRWin_ofFlatType_dec_correct. 
  setoid_rewrite list_ofFlatType_dec_correct. 
  setoid_rewrite PRWin_of_size_dec_correct. 
  split; intros; repeat match goal with [H : _ /\ _ |- _] => destruct H end; 
  repeat match goal with [ |- _ /\ _ ] => split end; try easy. 
  - apply Nat.mod_divide in H1 as (k & H1); [ | lia]. 
    exists k; split; [ | apply H1 ]. destruct k; cbn in *; lia.
  - apply Nat.mod_divide in H4 as (k & H4); [ | lia].  exists k; apply H4.  
  - apply Nat.mod_divide; [ lia | ]. destruct H1 as (k & _ & H1). exists k; apply H1.
  - apply Nat.mod_divide; [ lia | ]. apply H4. 
Qed. 

Definition trivialNoInstance := Build_BinaryPR 0 0 [] [] [] 0. 
Lemma trivialNoInstance_isNoInstance : not (BinaryPRLang trivialNoInstance). 
Proof. 
  intros (H & _). destruct H as (H & _). cbn in H. lia. 
Qed. 

Definition reduction (fpr : FlatPR) := if FlatPR_wf_dec fpr && leb 1 (Sigma fpr) then hBinaryPR (h fpr) fpr else trivialNoInstance. 

Lemma reduction_correct (fpr : FlatPR) : FlatPRLang fpr <-> BinaryPRLang (reduction fpr).  
Proof. 
  (*split; intros (H & H1). *)
  (*- unfold reduction. rewrite (proj2 (FlatPR_wf_dec_correct _) H). *)
    (*destruct (lt_dec 0 (Sigma fpr)). *)
    (*+ *)
    (*apply reduction_wf. *)
Admitted. 
