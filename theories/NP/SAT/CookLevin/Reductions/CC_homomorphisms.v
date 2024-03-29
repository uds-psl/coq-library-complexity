From Undecidability.Shared.Libs.PSL Require Import Base FiniteTypes. 
From Complexity.Libs Require Import MorePrelim UniformHomomorphisms.
From Complexity.NP.SAT.CookLevin.Subproblems Require CC BinaryCC .
Import CC.
Require Import Lia.

(** * Results on the behaviour of CC under string homomorphisms *)
(** Specifically, we show that we can obtain equivalent CC instances by applying injective uniform homomorphisms. *)

Section fixInstance.  
  Variable (Y : finType). (*target alphabet of the homomorphism *)
  Variable (fpr : CC). 

  Notation Sigma := (Sigma fpr).
  Notation offset := (offset fpr).
  Notation width := (width fpr).
  Notation init := (init fpr).
  Notation cards := (cards fpr).
  Notation final := (final fpr).
  Notation steps := (steps fpr). 

  (** A unique homomorphism is defined by h' *)
  Variable (h' : Sigma -> list Y).
  Definition h := canonicalHom h'. 
  
  (** A0 and A1 model uniformity and ε-freeness *)
  Variable (k : nat). 
  Context (A0 : forall x, |h' x| = k). 
  Context (A1 : k >= 1). 

  (** of course, we need injectivity *)
  Context (A2 : injective h'). 

  Local Set Default Proof Using "Type".

  (** we show basic results about h *)
  Lemma h_unifHom : uniform_homomorphism h. 
  Proof using A0 A1. 
    repeat split. 
    - apply canonicalHom_is_homomorphism. 
    - intros. cbn. rewrite !app_nil_r. now rewrite !A0.
    - intros. cbn. rewrite app_nil_r. now rewrite A0. 
  Qed. 

  Hint Extern 4 (uniform_homomorphism h) => apply h_unifHom : core. 
  Lemma h_injective l1 l2 : h l1 = h l2 -> l1 = l2. 
  Proof using A0 A1 A2. 
    revert l2. induction l1; intros l2 H0. 
    - destruct l2; [cbn in *; reflexivity | ]. 
      cbn in H0. apply (f_equal (@length _)) in H0. rewrite app_length in H0. cbn in H0. 
      specialize (A0 e). lia. 
    - destruct l2; [ apply h_length_inv' in H0; cbn in *; auto; congruence | ]. 
      rewrite homo_cons in H0; [ | apply h_unifHom ]. 
      rewrite homo_cons with (x := e) in H0; [ | apply h_unifHom]. 
      apply app_eq_length in H0 as (H0 & H0'); [ | apply (proj1 (proj2 (h_unifHom)))]. 
      apply IHl1 in H0'. 
      cbn in H0; rewrite !app_nil_r in H0. now apply A2 in H0. 
  Qed. 

  Lemma h_multiplier x : |h x| = k * |x|. 
  Proof using A0 .
  clear A1. induction x. 
    - cbn. lia. 
    - cbn. rewrite app_length. unfold h, canonicalHom in IHx. rewrite IHx. rewrite A0. nia. 
  Qed. 

  Lemma h_app_inv1 a u v : h a = u ++ v -> |u| = k -> exists a1 a2, a = a1::a2 /\ h [a1] = u /\ h a2 = v. 
  Proof using A0 A1.
    intros.  destruct a. 
    - specialize (h_multiplier []) as H1. rewrite H in H1. rewrite app_length in H1. cbn in H1. nia. 
    - rewrite homo_cons in H; [ | apply h_unifHom]. 
      specialize (h_multiplier [e]) as H1. cbn in H1. rewrite Nat.mul_1_r, app_nil_r in H1. 
      apply app_eq_length in H; [ | cbn in *; rewrite app_nil_r; lia]. 
      exists e, a. split;  [easy | tauto ]. 
  Qed. 

  Lemma h_app_inv a c u v : h a = u ++ v -> |u| = c * k -> exists a1 a2, a = a1 ++ a2 /\ h a1 = u /\ h a2 = v. 
  Proof using A1 A0. 
    intros. revert a u H0 H. induction c; intros. 
    - cbn in H0; destruct u; [ | cbn in H0; congruence]. 
      exists [], a. split; [ now cbn | split; [apply homo_nil, h_unifHom | cbn in H; apply H]]. 
    - cbn in H0. assert (k <= |u|) by lia. apply list_length_split1 in H1 as (s1 & s2 & H2 & H3 & ->). 
      rewrite H0 in H3. replace (k + c * k - k) with ( c * k) in H3 by nia. 
      rewrite <- app_assoc in H. apply h_app_inv1  in H as (a1 & a' & -> & H4 & H5); [ | apply H2] . 
      apply IHc in H5 as (a0 & a2 & -> & H5 & H6); [ | apply H3]. 
      exists (a1 :: a0), a2. cbn; split; [easy | split]. 
      + unfold h, canonicalHom in H5. cbn in H4; rewrite app_nil_r in H4. easy. 
      + apply H6. 
  Qed. 

  (** the transformed CC instance *)
  Definition hoffset := k * offset. 
  Definition hwidth := k * width. 
  Definition hinit := h init. 
  Definition hcard card := match card with Build_CCCard prem conc => Build_CCCard (h prem) (h conc) end.
  Definition hcards := map hcard cards. 
  Definition hfinal := map h final. 
  Definition hsteps := steps. 

  Definition hCC := Build_CC hoffset hwidth hinit hcards hfinal hsteps.

  (** from now on, we assume a well-formed instance for the main results *)
  Context (A : CC_wellformed fpr). 

  Lemma hCC_wf : CC_wellformed hCC. 
  Proof using A A0 A1. 
    destruct A as (F1 & F2 & F3 & F4 & F5 & F6). 
    unfold CC_wellformed. cbn. unfold hwidth, hoffset, hinit, hcards, hsteps. repeat match goal with [ |- _ /\ _] => split end; try nia.
    - destruct F3 as (k0 & F3 & F3'). exists k0; split; [easy | nia].
    - rewrite h_multiplier. nia.
    - intros card H. apply in_map_iff in H as (card' & <- & H). apply F5 in H. 
      destruct card'; destruct H as [H1 H2]. cbn in *. split; unfold hcard; cbn; rewrite h_multiplier; nia. 
    - destruct F6 as (k0 & F6). exists k0. rewrite h_multiplier. nia. 
  Qed. 

  (** we show equivalence of the original instance and the transformed instance*)

  (** agreement of coversHead *)
  Lemma coversHead_homomorphism_iff card a b : 
    coversHead card a b <-> coversHead (hcard card) (h a) (h b). 
  Proof using A A0 A1 A2. 
    split.
    - unfold hcard. destruct card. intros ((c1 & H1) & (c2 & H2)). 
      subst. split; cbn -[canonicalHom]; rewrite (proj1 h_unifHom); unfold prefix; eauto.
    - intros. unfold hcard in H. destruct card. destruct H as ((c1 & H1) & (c2 & H2)). 
      cbn in *. destruct A as (_ & _ & _ & _ & A4 & _ ). 
      eapply h_app_inv in H1 as (a1 & a2 & -> & H1 & <-); [ | rewrite Nat.mul_comm; apply h_multiplier].  
      eapply h_app_inv in H2 as (b1 & b2 & -> & H2 & <-); [ | rewrite Nat.mul_comm; apply h_multiplier]. 
      apply h_injective in H1 as <-.
      apply h_injective in H2 as <-.
      split; unfold prefix; eauto.  
  Qed. 

  (** For the direction from homomorphisms to the original instance, we actually need a stronger result telling us that 
    the conclusion is again in the image of the homomorphism
    *)
  Lemma coversHead_homomorphism2 card a1 a2 u v: 
    card el hcards 
    -> |a1| = offset 
    -> |u| = k * offset 
    -> coversHead card (h a1 ++ h a2) (u ++ v) 
    -> exists b1, u = h b1 /\ |b1| = offset 
        /\ coversHead card (h a1 ++ h a2) (h b1 ++ v). 
  Proof using A A0 A1. 
    intros. destruct H2 as ((c1 & H3) & (c2 & H4)). 
    unfold hcards in H; apply in_map_iff in H as (card' & <- & H).  
    destruct card'; cbn in *. 
    destruct A as (_ & _ & (ak & A5 & ->) & _ & A4 & _). 
    apply A4 in H as (H & H'). cbn in *. 
    assert (|u| <= |h conc|) by (rewrite h_multiplier; nia). 
    apply list_length_split1 in H2 as (b1' & b2' & H2 & _ & H2'). 
    eapply h_app_inv in H2' as (b1 & b2 & -> & <- & <-); [ | rewrite H2, H1, Nat.mul_comm; reflexivity ]. 
    rewrite (proj1 h_unifHom), <-app_assoc in H4.
    apply app_eq_length in H4 as (-> & ->); [ | easy]. 
    exists b1. 
    split; [ easy | split]. 
    - rewrite h_multiplier in H1; nia. 
    - split; cbn. 
      + unfold prefix. exists c1. easy. 
      + unfold prefix. exists c2. now rewrite (proj1 h_unifHom), <- app_assoc. 
  Qed. 

  (** agreement for valid*)
  Hint Constructors valid : core.

  Lemma valid_homomorphism1 a b : 
    |a| >= width 
    -> valid offset width cards a b 
    -> valid hoffset hwidth hcards (h a) (h b).
  Proof using Type*. 
    intros H0. unfold hwidth, hoffset.
    induction 1 as [ | ? ? ? ? H IH H1 H2 H3 | ? ? ? ? card H IH H1 H2 H3 H4]. 
    + rewrite homo_nil; [eauto | apply h_unifHom]. 
    + rewrite app_length in H0. nia. 
    + rewrite !(proj1 h_unifHom). destruct card as [prem conc]. 
      econstructor 3. 
      * destruct (le_lt_dec width (|a|)). 
        -- apply IH. nia. 
        --(*we show that for this case, the whole string is covered by the rule *)
          clear IH H2 H3. 
          specialize (valid_multiple_of_offset H) as (m & H').
          eapply valid_vacuous with (m := m). 
          ++ rewrite !h_multiplier. apply valid_length_inv in H. nia. 
          ++ rewrite !h_multiplier. nia. 
          ++ rewrite h_multiplier. nia. 
      * rewrite h_multiplier. nia. 
      * rewrite h_multiplier. nia. 
      * unfold hcards. apply in_map_iff. exists (Build_CCCard prem conc). split; [ | apply H3]. reflexivity. 
      * rewrite <- !(proj1 h_unifHom). apply coversHead_homomorphism_iff; assumption.
  Qed. 

  (** For the other direction, we again prove a stronger result saying that the conclusion is in the image of the homomorphism. 
    The lemma decomposes to two interesting cases: 
    - the case where a single rewrite card covers the whole string
    - the case where a part of the string is already covered by some cards and we add a new card at the front
  *)
  Lemma valid_homomorphism2 a b' : 
    |a| >= width 
    -> valid hoffset hwidth hcards (h a) b' 
    -> exists b, b' = h b /\ valid offset width cards a b.
  Proof using Type*. 
    (*we switch to the validDirect characterisation *)
    intros H H0. assert (valid hoffset hwidth hcards (h a) b' /\ |h a| >= hwidth) as H1%validDirect_valid. 
    { split; [easy | ]. unfold hwidth; rewrite h_multiplier. nia. }
    all: unfold hoffset, hwidth. 
    4: { destruct A as (_ & H5 & _). nia. }
    3: { destruct A as (_ & _ & (k0 & H5 & H6) &_). exists k0. nia. }
    2: { destruct A as (H5 & _). nia. }
    enough (exists b, b' = h b /\ validDirect offset width cards a b).
    { destruct H2 as (b & -> & H2). apply validDirect_valid in H2. 2-4: apply A. easy. }
    clear H0 H. 
    remember (h a). revert a Heql. 
    induction H1 as [? ? card H H0 H1 H2  | ? ? ? ? card H IH H0 H1 H2 H3 ]; intros a0 Heql. 
    - subst. 
      destruct A as (_ & _ & _ & _ & H5 & _). unfold hcards in H1. apply in_map_iff in H1 as (card' & <- & H1).
      specialize (H5 _ H1) as (H1' & H1''). 
      exists (conc card'). remember H2 as H20. clear HeqH20. (*we'll need the hypothesis later *)
      destruct H2 as ((a1 & H2) & (b1 & H3)). (*we show b1 = a1 = []*)
      assert (b1 = []). 
      { 
        rewrite H2, H3, !app_length in H. destruct card'. cbn in *. 
        rewrite !h_multiplier in H. enough (a1 = []) as -> by (destruct b1; [easy | cbn in H; nia]). 
        rewrite H2, app_length, h_multiplier in H0. unfold hwidth in H0. destruct a1; [easy | cbn in H0; nia].
      } 
      rewrite H3, H4, app_nil_r. destruct card'. cbn in *. split; [easy | ]. 
      eapply h_app_inv in H2 as (b1' & b2 & -> & H2 & <-); [ | rewrite h_multiplier, Nat.mul_comm; reflexivity]. 
      apply h_injective in H2 as ->. 
      assert (b2 = []) as ->.
      { rewrite h_multiplier, app_length in H0. unfold hwidth in H0. destruct b2; [easy | cbn in H0; nia]. }
      rewrite app_nil_r. econstructor; [lia | lia | apply H1 | ].
      apply coversHead_homomorphism_iff.
      rewrite H3, H4, !app_nil_r in H20. apply H20.
    - unfold hoffset, hwidth in *. unfold hcards in H2. apply in_map_iff in H2 as (rule' & <- & H10). 
      symmetry in Heql. eapply h_app_inv in Heql as (a1 & a2 & -> & F1 & F2); [ | rewrite Nat.mul_comm; apply H0]. 
      subst. apply coversHead_homomorphism2 in H3 as (b1 & -> & H7 & H3); 
        [ |now apply in_map_iff | rewrite h_multiplier in H0; nia | easy ]. 
       specialize (IH a2 eq_refl) as (b0 & -> & IH). 
        exists (b1 ++ b0). repeat split.
        * now rewrite (proj1 h_unifHom). 
        * econstructor; [ easy | rewrite h_multiplier in H0; nia | easy | apply H10 | ]. 
          rewrite <- !(proj1 h_unifHom) in H3. apply coversHead_homomorphism_iff in H3; eauto.
  Qed. 

  (** we can obtain an equivalence, but its second direction is significantly weaker than the direction which we've just shown *)
  Lemma valid_homomorphism_iff a b : 
    |a| >= width 
    -> valid offset width cards a b <-> valid hoffset hwidth hcards (h a) (h b).
  Proof using Type*. 
    intros H0; split. unfold hwidth, hoffset. 
    - apply valid_homomorphism1; easy.  
    - intros. apply valid_homomorphism2 in H as (b' & Heq & H1 ). 
      + symmetry in Heq. apply h_injective in Heq; easy. 
      + apply H0. 
  Qed. 

  (** this lifts to powers of valid*)
  Lemma valid_relpower_homomorphism1 a b steps : 
    |a| >= width 
    -> relpower (valid offset width cards) steps a b 
    -> relpower (valid (k * offset) (k * width) hcards) steps (h a) (h b).
  Proof using Type*. 
    intros H. induction 1 as [ | ? ? ? ? H0 ? IH]; [ eauto | ]. econstructor. 
    + apply valid_homomorphism_iff; [ apply H | easy ]. 
    + apply IH.  apply valid_length_inv in H0. lia. 
  Qed. 

  Lemma valid_relpower_homomorphism2 a b' steps: 
    |a| >= width 
    -> relpower (valid (k * offset) (k * width) hcards) steps (h a) b' 
    -> exists b, b' = h b /\ relpower (valid offset width cards) steps a b. 
  Proof using Type*. 
    intros H H0. remember (h a). revert a Heql H. induction H0 as [ | ? ? ? ? H0 H1 IH]; intros. 
    - exists a0. split; eauto. 
    - subst. apply valid_homomorphism2 in H0 as (b' & -> & H0); [ | easy ]. 
      edestruct (IH b' eq_refl) as (c' & -> & IH'). 
      + apply valid_length_inv in H0; lia. 
      + exists c'; split; [ easy | ]. econstructor; easy. 
  Qed. 

  (** again a slightly weaker equivalence *)
  Lemma valid_relpower_homomorphism_iff a b steps : 
    |a| >= width 
    -> relpower (valid offset width cards) steps a b <-> relpower (valid (k * offset) (k * width) hcards) steps (h a) (h b).
  Proof using Type*. 
    intros. split. 
    - now apply valid_relpower_homomorphism1.  
    - intros (b' & Heq & H1)%valid_relpower_homomorphism2; [ | easy ]. 
      symmetry in Heq; apply h_injective in Heq. easy. 
  Qed. 

  (** agreement of the final constraints *)
  Lemma final_agree sf : 
    |init| = |sf| 
    -> satFinal offset (length init) final sf <-> satFinal hoffset (length hinit) hfinal (h sf). 
  Proof using Type*. 
    intros G. unfold satFinal, hoffset, hfinal. split; intros (subs & k0 & H1 & H2 & H3). 
    - rewrite G in H2. exists (h subs), (k0). 
      split; [now apply in_map_iff | split; [ unfold hinit; rewrite h_multiplier; nia | ]]. 
      destruct H3 as (b & H3). rewrite <- (firstn_skipn (k0 * offset) sf). 
      rewrite (proj1 h_unifHom). 
      (*we make a case analysis: if subs = [], the claim holds trivially *)
      (*otherwise, we know that sf has a length of at least k0 * offset *)
      destruct subs. 
      + rewrite homo_nil; [ | apply h_unifHom]. unfold prefix; cbn; eauto. 
      + rewrite skipn_app. 
        * rewrite H3. rewrite (proj1 h_unifHom). exists (h b); eauto. 
        * rewrite h_multiplier. rewrite firstn_length. 
          enough (|sf| >= k0 * offset) by nia. 
          specialize (skipn_length (k0 * offset) sf). rewrite H3. cbn. nia. 
    - apply in_map_iff in H1 as (subs' & <- & H1). 
      exists subs', k0; split; [ apply H1 | ]. 
      destruct H3 as (b & H3). unfold prefix. 
      rewrite <- (firstn_skipn (k0 * offset) sf), (proj1 h_unifHom) in H3. 
      unfold hinit in H2; rewrite h_multiplier in H2. split; [ nia | ]. 
      rewrite skipn_app in H3. 
      + eapply h_app_inv in H3 as (a1 & a2 & -> & H4 & H5); [ | rewrite Nat.mul_comm, h_multiplier; easy ].
        exists a2. enough (a1 = subs') by easy. 
        symmetry; apply h_injective. easy.
      + rewrite h_multiplier. rewrite firstn_length. nia. 
  Qed. 
      
  (** the transformed instance is a YES-instance iff the original instance is a YES-instance *)
  Lemma CC_homomorphism_iff : 
    (exists sf, relpower (valid offset width cards) steps init sf /\ satFinal offset (|init|) final sf) 
    <-> (exists sf, relpower (valid hoffset hwidth hcards) hsteps hinit sf /\ satFinal hoffset (|hinit|) hfinal sf). 
  Proof using Type*. 
    unfold hsteps, hinit, hoffset, hwidth. 
    destruct A as (_ & _ & _  & A4 &_). 
    split; intros. 
    - destruct H as (sf & H1 & H2 ). 
      exists (h sf). split. 
      + apply valid_relpower_homomorphism_iff; easy. 
      + clear A4. apply final_agree. 
        * apply relpower_valid_length_inv in H1. lia. 
        * apply H2. 
    - destruct H as (sf & H1 & H2). 
      apply valid_relpower_homomorphism2 in H1 as (sf' & -> & H1).
      + exists sf'. split; [ easy | ].
        clear A4. apply final_agree. 
        * apply relpower_valid_length_inv in H1; easy. 
        * apply H2. 
      + apply A4. 
  Qed. 

  Corollary CC_homomorphism_inst_iff : 
    CCLang fpr <-> CCLang hCC. 
  Proof using Type*. 
    split; intros [H1 H2%CC_homomorphism_iff].
    - split; [apply hCC_wf | apply H2].
    - split; [apply A | apply H2]. 
  Qed. 
End fixInstance. 
