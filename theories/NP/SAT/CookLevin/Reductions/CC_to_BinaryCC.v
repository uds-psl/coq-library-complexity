From Undecidability.Shared.Libs.PSL Require Import Base FinTypes.
From Undecidability.Shared.Libs.PSL Require Import Vectors.Vectors. 
From Complexity.Libs.CookPrelim Require Import MorePrelim FlatFinTypes.
From Complexity.NP.SAT.CookLevin Require Import BinaryCC CC CC_homomorphisms. 
Require Import Lia.

(** * CC to BinaryCC *)
(** We reduce arbitrary CC instances to a binary alphabet by using the results on uniform homomorphisms. *)

Section fixInstance. 
  (** we first do the reduction for wellformed instances, satisfying the syntactic requirements *)
  Variable (pr : CC). 

  Notation Sigma := (Sigma pr).
  Notation offset := (offset pr).
  Notation width := (width pr).
  Notation init := (init pr).
  Notation cards := (cards pr).
  Notation final := (final pr).
  Notation steps := (steps pr). 

  Context (A : CC_wellformed pr). 
  Context (A1 : |elem Sigma| > 0). (*instances without this property are trivial no-instances *)
  
  (*we fix the homomorphism on natural numbers *)
  (*it just encodes the alphabet using a unary encoding: there is one indicator bit for each element of the alphabet*)
  Definition hNat (Sig : nat) (x : nat) := if leb (S x) Sig then repeat false x ++ [true] ++ repeat false (Sig - x -1)
                                                else repeat false Sig. 

  Lemma hNat_length (Sig x : nat) : |hNat Sig x| = Sig. 
  Proof using. 
    clear A A1 pr.
    unfold hNat. destruct leb eqn:H. 
    - rewrite !app_length, !repeat_length. apply leb_complete in H. cbn. nia. 
    - apply repeat_length.
  Qed. 

  Lemma hP_inv1 (Sig x n : nat) : hNat Sig x = repeat false n ++ [true] ++ repeat false (Sig - n -1) -> x = n. 
  Proof. 
    intros. unfold hNat in H. 
    destruct leb eqn:H1. 
    - clear H1. revert H.  generalize (Sig - x- 1). generalize (Sig - n -1). 
      revert n. induction x; intros. 
      + destruct n; cbn in H; [reflexivity | congruence]. 
      + destruct n; cbn in H; [ congruence | ]. inv H. now apply IHx in H1.
    - destruct (le_lt_dec n Sig). 
      + assert (|repeat false n| <= |repeat false Sig|) by (now rewrite !repeat_length). 
        apply list_length_split1 in H0 as (s1 & s2 & H0 & _ & H2). rewrite H2 in H. 
        apply app_eq_length in H as (_ & H); [ | apply H0]. 
        apply repEl_app_inv in H2 as (n1 & n2 & -> & -> & H2).   
        destruct n2; cbn in H; congruence. 
      + match type of H with ?a = ?b => assert (|a| = |b|) by congruence end. 
        rewrite !app_length, !repeat_length in H0. lia. 
  Qed. 

  (** now, the homomorphism for finite types is defined by composing hNat and index *)
  Definition h' (x : Sigma) := hNat (|elem Sigma|) (index x). 

  Lemma hP_injective : injective h'. 
  Proof. 
    intros x y H. unfold h', hNat in H. 
    erewrite (leb_correct (S (index y))) in H. 2: apply index_le.   
    now apply hP_inv1, injective_index in H. 
  Qed. 

  Lemma hP_length x : |h' x| = |elem Sigma|. 
  Proof. 
    unfold h'. now rewrite hNat_length.   
  Qed. 

  Definition h := h h'. 

  Notation hoffset := (@hoffset pr (|elem Sigma|)).
  Notation hwidth := (@hwidth pr (|elem Sigma|)). 
  Notation hinit := (@hinit (FinType (EqType bool)) pr h'). 
  Notation hcards := (@hcards (FinType (EqType bool)) pr h'). 
  Notation hfinal := (@hfinal (FinType (EqType bool)) pr h'). 
  Notation hsteps := (@hsteps pr). 

  Definition hBinaryCC := @BinaryCC.Build_BinaryCC hoffset hwidth hinit hcards hfinal hsteps. 

  Lemma h_multiplier_sp x : |h x| = (|elem Sigma|) * |x|. 
  Proof. 
    unfold h. erewrite h_multiplier. 2: apply hP_length. easy.
  Qed. 

  Lemma CC_homomorphism_wf : CC_wellformed pr -> BinaryCC.BinaryCC_wellformed hBinaryCC. 
  Proof. 
    intros (H1 & H2 & H3 & H4 & H5 & H6). 
    unfold BinaryCC_wellformed; repeat match goal with [ |- _ /\ _] => split end; cbn. 
    + unfold hwidth. nia. 
    + unfold hoffset. nia. 
    + unfold hwidth, hoffset. destruct H3 as (k' & H3 & H3'). exists k'. split; nia.  
    + unfold hinit, hwidth. rewrite h_multiplier_sp. nia. 
    + unfold hwidth. intros [] H. unfold hcards in H. apply in_map_iff in H as (card' & <- & H). 
      destruct card'. apply H5 in H. destruct H as (H & H0); cbn in *. 
      split; cbn; now rewrite h_multiplier_sp. 
    + destruct H6 as (k' & H6). unfold hinit, hoffset. exists k'. 
      rewrite h_multiplier_sp, H6. nia. 
  Qed. 

  (** we now get the reduction for the case that the instance we reduce from is wellformed *)
  Lemma reduction_wf : CCLang pr <-> BinaryCCLang hBinaryCC. 
  Proof. 
    split; intros. 
    - destruct H as (_ & sf & H1 & H2).
      split; [ apply CC_homomorphism_wf; auto | ]. 
      apply CC_homomorphism_iff; eauto; [ apply hP_length | apply hP_injective].
    - destruct H as (_ & H1).
      split; [ apply A | ]. 
      apply (CC_homomorphism_iff hP_length A1 hP_injective) in H1; [apply H1 | apply A]. 
  Qed. 
End fixInstance. 

(** for non-wellformed instances, we map to a trivial no-instance *)
Definition trivialNoInstance := Build_BinaryCC 0 0 [] [] [] 0. 
Lemma trivialNoInstance_isNoInstance : not (BinaryCCLang trivialNoInstance). 
Proof. 
  intros (H & _). destruct H as (H & _). cbn in H. lia. 
Qed. 

Definition reduction (pr : CC) := if CC_wf_dec pr then hBinaryCC pr else trivialNoInstance. 

Lemma CC_to_BinaryCC (pr : CC) : CCLang pr <-> BinaryCCLang (reduction pr).  
Proof. 
  unfold reduction. 
  destruct (CC_wf_dec pr) eqn:H1. 
  - apply CC_wf_dec_correct in H1. remember H1 as H0. clear HeqH0. destruct H1 as (H1 & _ & _ & H2 & _). 
    destruct init; cbn in H2; [ lia | ]. 
    assert (|elem (Sigma pr)| > 0). 
    { specialize (@elem_spec _ e). destruct elem; cbn; [eauto | lia]. }
    apply reduction_wf; easy. 
  - assert (not (CC_wf_dec pr = true)) as H by eauto. rewrite CC_wf_dec_correct in H. 
    split; intros. 
    + destruct H0; tauto. 
    + exfalso; apply trivialNoInstance_isNoInstance, H0. 
Qed. 
