From PslBase Require Import Base FinTypes. 
From PslBase Require Import Vectors.Vectors. 
From Undecidability.L.Complexity.Cook Require Import Prelim BinaryPR PR PR_homomorphisms. 
Require Import Lia.

Section fixInstance. 
  Variable (pr : PR). 

  Notation Sigma := (Sigma pr).
  Notation offset := (offset pr).
  Notation width := (width pr).
  Notation init := (init pr).
  Notation windows := (windows pr).
  Notation final := (final pr).
  Notation steps := (steps pr). 

  (*we first do the reduction for wellformed instances, satisfying the syntactic requirements *)
  Context (A : PR_wellformed pr). 
  Context (A1 : |elem Sigma| > 0). (*instances without this property are trivial no instances *)
  
  (*we fix the homomorphism on natural numbers *)
  Definition hNat (Sig : nat) (x : nat) := if leb (S x) Sig then repEl x false ++ [true] ++ repEl (Sig - x -1) false
                                                else repEl Sig false. 

  Lemma hNat_length (Sig x : nat) : |hNat Sig x| = Sig. 
  Proof. 
    unfold hNat. destruct leb eqn:H. 
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

  Lemma h'_inv1 (Sig x n : nat) : hNat Sig x = repEl n false ++ [true] ++ repEl (Sig - n -1) false -> x = n. 
  Proof. 
    intros. unfold hNat in H. 
    destruct leb eqn:H1. 
    - clear H1. revert H.  generalize (Sig - x- 1). generalize (Sig - n -1). 
      revert n. induction x; intros. 
      + destruct n; cbn in H; [reflexivity | congruence]. 
      + destruct n; cbn in H; [ congruence | ]. inv H. now apply IHx in H1.
    - destruct (le_lt_dec n Sig). 
      + assert (|repEl n false| <= |repEl Sig false|) by (now rewrite !repEl_length). 
        apply list_length_split1 in H0 as (s1 & s2 & H0 & _ & H2). rewrite H2 in H. 
        apply app_eq_length in H as (_ & H); [ | apply H0]. 
        apply repEl_app_inv in H2 as (n1 & n2 & -> & -> & H2).   
        destruct n2; cbn in H; congruence. 
      + match type of H with ?a = ?b => assert (|a| = |b|) by congruence end. 
        rewrite !app_length, !repEl_length in H0. cbn in H0. lia. 
  Qed. 

  (*now, the homomorphism for finite types is defined by composing hNat and index *)
  Definition h' (x : Sigma) := hNat (|elem Sigma|) (index x). 

  Lemma h'_ge1 x : |h' x | >= 1. 
  Proof. 
    unfold h'. rewrite hNat_length. lia. 
  Qed. 

  Lemma h'_uniform x y : |h' x| = |h' y|. 
  Proof. 
    unfold h'. rewrite !hNat_length. easy.
  Qed. 

  Lemma h'_injective : injective h'. 
  Proof. 
    intros x y H. unfold h', hNat in H. 
    erewrite (leb_correct (S (index y))) in H. 2: apply index_le.   
    now apply h'_inv1, injective_index in H. 
  Qed. 

  Notation hoffset := (@hoffset (FinType (EqType bool)) pr h' h'_ge1 h'_uniform A1).
  Notation hwidth := (@hwidth (FinType (EqType bool)) pr h' h'_ge1 h'_uniform A1). 
  Notation hinit := (@hinit (FinType (EqType bool)) pr h'). 
  Notation hwindows := (@hwindows (FinType (EqType bool)) pr h'). 
  Notation hfinal := (@hfinal (FinType (EqType bool)) pr h'). 
  Notation hsteps := (@hsteps pr). 

  Definition hBinaryPR := @BinaryPR.Build_BinaryPR hoffset hwidth hinit hwindows hfinal hsteps. 

  Lemma PR_homomorphism_wf : PR_wellformed pr -> BinaryPR.BinaryPR_wellformed hBinaryPR. 
  Proof. 
    intros (H1 & H2 & H3 & H4 & H5 & H6). split; [ | split; [ | split]]; cbn. 
    + unfold hwidth. specialize (@k_ge _ pr h' h'_ge1 h'_uniform A1). 
      destruct A as (A2 & _). intros. remember (k h'_ge1 h'_uniform A1). setoid_rewrite <- Heqn. nia. 
    + unfold hinit, hwidth. rewrite (h_multiplier h'_ge1 h'_uniform A1 init). 
      remember (k h'_ge1 h'_uniform A1). setoid_rewrite <- Heqn. nia. 
    + unfold hwidth. intros [] H. unfold hwindows in H. apply in_map_iff in H as (win' & <- & H). 
      destruct win'. apply H5 in H. destruct H as (H & H0); cbn in *. 
      split; cbn; now setoid_rewrite (h_multiplier h'_ge1 h'_uniform A1). 
    + destruct H6 as (k' & H6). unfold hinit, hoffset. exists k'. 
      rewrite (h_multiplier h'_ge1 h'_uniform A1 init), H6.
      remember (k h'_ge1 h'_uniform A1). setoid_rewrite <- Heqn. nia. 
  Qed. 

  (*we now get the reduction for the case that the instance we reduce from is wellformed *)
  Lemma reduction_wf : PRLang pr <-> BinaryPRLang hBinaryPR. 
  Proof. 
    (*specialize (h_bounded_injective) as F1. *)
    (*specialize (h_uniform_homomorphism) as F2. *)
    split; intros. 
    - destruct H as (_ & sf & H1 & H2).
      split; [ apply PR_homomorphism_wf; auto | ]. 
      apply PR_homomorphism_iff; eauto. 
      apply h'_injective. 
    - destruct H as (_ & H1).
      split; [ apply A | ]. 
      apply PR_homomorphism_iff in H1; eauto. apply h'_injective. 
  Qed. 
End fixInstance. 

Definition PRWin_of_size_dec (X : Type) width (win : PRWin X) := Nat.eqb (|prem win|) width && Nat.eqb (|conc win|) width.

Lemma leb_iff a b : leb a b = true <-> a <= b. 
Proof. 
  split; intros. 
  - now apply leb_complete. 
  - now apply leb_correct. 
Qed.

Lemma PRWin_of_size_dec_correct (X : Type) width (win : PRWin X) : PRWin_of_size_dec width win = true <-> PRWin_of_size win width. 
Proof. 
  unfold PRWin_of_size, PRWin_of_size_dec. rewrite andb_true_iff. rewrite <- !(reflect_iff _ _ (Nat.eqb_spec _ _ )). easy.
Qed. 

Print PR_wellformed. 

Definition PR_wf_dec (pr : PR) := 
  leb 1 (width pr) 
  && leb 1 (offset pr)
  && Nat.eqb (Nat.modulo (width pr) (offset pr)) 0
  && leb (width pr) (|init pr|)
  && forallb (PRWin_of_size_dec (width pr)) (windows pr)
  && Nat.eqb (Nat.modulo (|init pr|) (offset pr)) 0.
 

Lemma PR_wf_dec_correct (pr : PR) : PR_wf_dec pr = true <-> PR_wellformed pr. 
Proof. 
  unfold PR_wf_dec, PR_wellformed. rewrite !andb_true_iff, !and_assoc.
  rewrite !leb_iff. rewrite <- !(reflect_iff _ _ (Nat.eqb_spec _ _ )).  
  rewrite !forallb_forall. 
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

Lemma reduction_correct (pr : PR) : { bpr & PRLang pr <-> BinaryPRLang bpr}.  
Proof. 
  destruct (PR_wf_dec pr) eqn:H1. 
  - apply PR_wf_dec_correct in H1. remember H1 as H0. clear HeqH0. destruct H1 as (H1 & _ & _ & H2 & _). 
    destruct init; cbn in H2; [ exists trivialNoInstance; lia| ]. 
    assert (|elem (Sigma pr)| > 0). 
    { specialize (@elem_spec _ e). destruct elem; cbn; [eauto | lia]. }
    exists (hBinaryPR H). apply reduction_wf, H0.   
  - assert (not (PR_wf_dec pr = true)) as H by eauto. rewrite PR_wf_dec_correct in H. 
    exists trivialNoInstance. split; intros. 
    + destruct H0; tauto. 
    + exfalso; apply trivialNoInstance_isNoInstance, H0. 
Qed. 
