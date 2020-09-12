From PslBase Require Import Base FinTypes. 
From Undecidability.L.Complexity Require Import MorePrelim Problems.Cook.TCC Problems.Cook.CC.
Require Import Lia.

(** * Reduction of 3-CC to CC. *)
(*Apart from syntactical differences, this is just a simple embedding. *)

Section fixInstance. 
  (*We do not directly fix a TCC instance since we do not actually require the alphabet to be finite for the reduction *)
  Variable (FSigma : Type). 
  Variable (Finit : list FSigma). 
  Variable (Fcards : list (TCCCard FSigma)). 
  Variable (Ffinal : list (list FSigma)). 
  Variable (Fsteps : nat). 

  Definition TCCCard_to_CCCard (X : Type) (card : TCCCard X) := 
    Build_CCCard (TCCCardP_to_list (TCC.prem card)) (TCCCardP_to_list (TCC.conc card)).

  Definition CC_cards := map (@TCCCard_to_CCCard FSigma) Fcards. 

  Hint Constructors CC.valid : core.
  Hint Constructors TCC.valid : core. 

  (*We show agreement for valid and satFinal *)
  Lemma valid_agree (s1 s2 : list FSigma) : 
    |s1| >= 3 -> TCC.valid (coversHeadList Fcards) s1 s2 <-> CC.valid 1 3 CC_cards s1 s2. 
  Proof. 
    intros; split. 
    - induction 1 as [ | a b x y H0 IH H1 | a b x y H0 IH H1].
      + eauto. 
      + cbn in H; lia. 
      + replace (x :: a) with ([x] ++ a) by now cbn. replace (y :: b) with ([y] ++ b) by now cbn. 
        destruct H1 as (card & H3 & H4). 
        destruct (le_lt_dec 3 (|a|)) as [H2 | H2]. 
        * econstructor 3; [apply IH; lia | easy | easy | apply in_map_iff | ]. 
          -- exists card. split; [reflexivity | easy]. 
          -- unfold coversHead. cbn. easy. 
        * assert (|a| = 2) as H1 by now cbn in H. clear H2 H IH. 
          apply TCC.valid_length_inv in H0. rewrite H1 in H0. 
          list_length_inv. econstructor 3; [ eapply valid_vacuous with (m := 2); cbn; eauto | easy | easy | | ].  
          -- apply in_map_iff. exists card; split; [ reflexivity | easy]. 
          -- destruct H4. cbn; split; eauto. 
    - induction 1 as [ | a b u v H0 IH H1 H2 H3 | a b u v card H0 IH H1 H2 H3 H4].
      + eauto. 
      + rewrite app_length in H; lia. 
      + list_length_inv. cbn in *. unfold CC_cards in H3. apply in_map_iff in H3 as (card' & <- & H3). 
        destruct (le_lt_dec 3 (|a|)) as [H1 | H1].  
        * econstructor 3; [ apply IH; lia | exists card'; split; [ apply H3 | ]]. 
          destruct H4; split; eauto. 
        * assert (|a| = 2) by lia. clear IH H1 H. apply valid_length_inv in H0. rewrite H2 in H0.
          list_length_inv. constructor 3; [ apply TCC.valid_vacuous; cbn; eauto| ]. 
          exists card'; split; [apply H3 | ]. destruct H4; split; eauto. 
  Qed. 

  Lemma relpower_valid_agree k (s1 s2 : list FSigma) : 
    |s1| >= 3 -> relpower (TCC.valid (coversHeadList Fcards)) k s1 s2 <-> relpower (CC.valid 1 3 CC_cards) k s1 s2. 
  Proof. 
    intros; split; induction 1 as [? | ? ? ? ? H0 H1 IH]; [ eauto | | eauto | ]. 
    - econstructor; [ apply valid_agree; [apply H | apply H0] | apply IH]. 
      apply TCC.valid_length_inv in H0; lia. 
    - econstructor; [ apply valid_agree; [ apply H | apply H0] | apply IH]. 
      apply valid_length_inv in H0; lia. 
  Qed. 

  Lemma final_agree (s : list FSigma) : |s| = |Finit| -> TCC.satFinal Ffinal s <-> CC.satFinal 1 (length Finit) Ffinal s. 
  Proof. 
    unfold TCC.satFinal, satFinal. setoid_rewrite Nat.mul_1_r. split; intros. 
    - destruct H0 as (subs & H1 & H2). exists subs. 
      destruct H2 as (b1 & b2 & ->). 
      exists (|b1|). split; [ apply H1 | ]. 
      rewrite skipn_app; [ | easy]. 
      split; [ rewrite !app_length in H; lia | now exists b2].
    - destruct H0 as (subs & k & H1 & H2 & (b & H3)). exists subs. split; [ apply H1 | ]. 
      unfold substring. 
      setoid_rewrite <- (firstn_skipn k s). setoid_rewrite H3.
      exists (firstn k s), b. easy.
  Qed. 
End fixInstance. 

(*The reduction is now straightforward. *)
Definition CC_instance (tpr : TCC) := Build_CC 1 3 (TCC.init tpr) (CC_cards (TCC.cards tpr)) (TCC.final tpr) (TCC.steps tpr). 

Lemma TCC_to_CC (tpr : TCC) : TCCLang tpr <-> CCLang (CC_instance tpr). 
Proof. 
  split; intros. 
  - destruct H as (H & sf & H1 & H2). split; [ | exists sf; repeat split]. 
    + repeat split; cbn in *; [ lia | lia | exists 3; split; lia | apply H | | | ]. 
      * unfold CC_cards in *. apply in_map_iff in H0 as (card' & <- & H0). cbn. destruct card', prem, conc; now cbn.   
      * unfold CC_cards in *. apply in_map_iff in H0 as (card' & <- & H0). cbn. destruct card', prem, conc; now cbn.
      * setoid_rewrite Nat.mul_1_r. eauto. 
    + apply relpower_valid_agree, H1. apply H. 
    + apply final_agree, H2. apply TCC.relpower_valid_length_inv in H1; cbn. lia. 
  - destruct H as (H1 & sf & H2 & H3). split; [ | exists sf; repeat split]; cbn in *. 
    + destruct H1 as (_ & _ & _ & H1 &_). cbn in H1. apply H1.  
    + apply relpower_valid_agree; [ apply H1 | apply H2]. 
    + eapply final_agree, H3. apply relpower_valid_length_inv in H2. lia. 
Qed. 
