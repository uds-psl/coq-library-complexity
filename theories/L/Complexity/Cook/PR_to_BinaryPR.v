From PslBase Require Import Base FinTypes.
From PslBase Require Import Vectors.Vectors. 
From Undecidability.L.Complexity.Cook Require Import Prelim BinaryPR PR PR_homomorphisms. 
Require Import Lia.

(** *PR to BinaryPR *)
(*We reduce arbitrary PR instances to a binary alphabet by using the results on uniform homomorphisms. *)

Section fixInstance. 
  (*we first do the reduction for wellformed instances, satisfying the syntactic requirements *)
  Variable (pr : PR). 

  Notation Sigma := (Sigma pr).
  Notation offset := (offset pr).
  Notation width := (width pr).
  Notation init := (init pr).
  Notation windows := (windows pr).
  Notation final := (final pr).
  Notation steps := (steps pr). 

  Context (A : PR_wellformed pr). 
  Context (A1 : |elem Sigma| > 0). (*instances without this property are trivial no instances *)
  
  (*we fix the homomorphism on natural numbers *)
  (*it just encodes the alphabet using a unary encoding: there is one indicator bit for each element of the alphabet*)
  Definition hNat (Sig : nat) (x : nat) := if leb (S x) Sig then repEl x false ++ [true] ++ repEl (Sig - x -1) false
                                                else repEl Sig false. 

  Lemma hNat_length (Sig x : nat) : |hNat Sig x| = Sig. 
  Proof. 
    unfold hNat. destruct leb eqn:H. 
    - rewrite !app_length, !repEl_length. apply leb_complete in H. cbn. nia. 
    - now rewrite repEl_length.
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

  Lemma h'_length x : |h' x| = |elem Sigma|. 
  Proof. 
    unfold h'. now rewrite hNat_length.   
  Qed. 

  Definition h := h h'. 

  Notation hoffset := (@hoffset pr (|elem Sigma|)).
  Notation hwidth := (@hwidth pr (|elem Sigma|)). 
  Notation hinit := (@hinit (FinType (EqType bool)) pr h'). 
  Notation hwindows := (@hwindows (FinType (EqType bool)) pr h'). 
  Notation hfinal := (@hfinal (FinType (EqType bool)) pr h'). 
  Notation hsteps := (@hsteps pr). 

  Definition hBinaryPR := @BinaryPR.Build_BinaryPR hoffset hwidth hinit hwindows hfinal hsteps. 

  Lemma h_multiplier_sp x : |h x| = (|elem Sigma|) * |x|. 
  Proof. 
    unfold h. erewrite h_multiplier. 2: apply h'_length. easy.
  Qed. 

  Lemma PR_homomorphism_wf : PR_wellformed pr -> BinaryPR.BinaryPR_wellformed hBinaryPR. 
  Proof. 
    intros (H1 & H2 & H3 & H4 & H5 & H6). 
    unfold BinaryPR_wellformed; repeat match goal with [ |- _ /\ _] => split end; cbn. 
    + unfold hwidth. nia. 
    + unfold hoffset. nia. 
    + unfold hwidth, hoffset. destruct H3 as (k' & H3 & H3'). exists k'. split; nia.  
    + unfold hinit, hwidth. rewrite h_multiplier_sp. nia. 
    + unfold hwidth. intros [] H. unfold hwindows in H. apply in_map_iff in H as (win' & <- & H). 
      destruct win'. apply H5 in H. destruct H as (H & H0); cbn in *. 
      split; cbn; now rewrite h_multiplier_sp. 
    + destruct H6 as (k' & H6). unfold hinit, hoffset. exists k'. 
      rewrite h_multiplier_sp, H6. nia. 
  Qed. 

  (*we now get the reduction for the case that the instance we reduce from is wellformed *)
  Lemma reduction_wf : PRLang pr <-> BinaryPRLang hBinaryPR. 
  Proof. 
    split; intros. 
    - destruct H as (_ & sf & H1 & H2).
      split; [ apply PR_homomorphism_wf; auto | ]. 
      apply PR_homomorphism_iff; eauto; [ apply h'_length | apply h'_injective].
    - destruct H as (_ & H1).
      split; [ apply A | ]. 
      apply (PR_homomorphism_iff h'_length A1 h'_injective A1) in H1; [apply H1 | apply A]. 
  Qed. 
End fixInstance. 

(*for non-wellformed instances, we map to a trivial no-instance *)
Definition trivialNoInstance := Build_BinaryPR 0 0 [] [] [] 0. 
Lemma trivialNoInstance_isNoInstance : not (BinaryPRLang trivialNoInstance). 
Proof. 
  intros (H & _). destruct H as (H & _). cbn in H. lia. 
Qed. 

Definition reduction (pr : PR) := if PR_wf_dec pr then hBinaryPR pr else trivialNoInstance. 

Lemma PR_to_BinaryPR (pr : PR) : PRLang pr <-> BinaryPRLang (reduction pr).  
Proof. 
  unfold reduction. 
  destruct (PR_wf_dec pr) eqn:H1. 
  - apply PR_wf_dec_correct in H1. remember H1 as H0. clear HeqH0. destruct H1 as (H1 & _ & _ & H2 & _). 
    destruct init; cbn in H2; [ lia | ]. 
    assert (|elem (Sigma pr)| > 0). 
    { specialize (@elem_spec _ e). destruct elem; cbn; [eauto | lia]. }
    apply reduction_wf; easy. 
  - assert (not (PR_wf_dec pr = true)) as H by eauto. rewrite PR_wf_dec_correct in H. 
    split; intros. 
    + destruct H0; tauto. 
    + exfalso; apply trivialNoInstance_isNoInstance, H0. 
Qed. 
