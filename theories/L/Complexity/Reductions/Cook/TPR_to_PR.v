From PslBase Require Import Base FinTypes. 
From Undecidability.L.Complexity Require Import MorePrelim Problems.Cook.TPR Problems.Cook.PR.
Require Import Lia.

(** * Reduction of 3-PR to PR. *)
(*Apart from syntactical differences, this is just a simple embedding. *)

Section fixInstance. 
  (*We do not directly fix a TPR instance since we do not actually require the alphabet to be finite for the reduction *)
  Variable (FSigma : Type). 
  Variable (Finit : list FSigma). 
  Variable (Fwindows : list (TPRWin FSigma)). 
  Variable (Ffinal : list (list FSigma)). 
  Variable (Fsteps : nat). 

  Definition TPRWin_to_PRWin (X : Type) (win : TPRWin X) := Build_PRWin (TPRWinP_to_list (TPR.prem win)) (TPRWinP_to_list (TPR.conc win)).

  Definition PR_windows := map (@TPRWin_to_PRWin FSigma) Fwindows. 

  Hint Constructors PR.valid : core.
  Hint Constructors TPR.valid : core. 

  (*We show agreement for valid and satFinal *)

  Lemma valid_agree (s1 s2 : list FSigma) : 
    |s1| >= 3 -> TPR.valid (rewritesHeadList Fwindows) s1 s2 <-> PR.valid 1 3 PR_windows s1 s2. 
  Proof. 
    intros; split. 
    - induction 1 as [ | a b x y H0 IH H1 | a b x y H0 IH H1].
      + eauto. 
      + cbn in H; lia. 
      + replace (x :: a) with ([x] ++ a) by now cbn. replace (y :: b) with ([y] ++ b) by now cbn. 
        destruct H1 as (win & H3 & H4). 
        destruct (le_lt_dec 3 (|a|)) as [H2 | H2]. 
        * econstructor 3; [apply IH; lia | easy | easy | apply in_map_iff | ]. 
          -- exists win. split; [reflexivity | easy]. 
          -- unfold rewritesHead. cbn. easy. 
        * assert (|a| = 2) as H1 by now cbn in H. clear H2 H IH. 
          apply TPR.valid_length_inv in H0. rewrite H1 in H0. 
          list_length_inv. econstructor 3; [ eapply valid_vacuous with (m := 2); cbn; eauto | easy | easy | | ].  
          -- apply in_map_iff. exists win; split; [ reflexivity | easy]. 
          -- destruct H4. cbn; split; eauto. 
    - induction 1 as [ | a b u v H0 IH H1 H2 H3 | a b u v win H0 IH H1 H2 H3 H4].
      + eauto. 
      + rewrite app_length in H; lia. 
      + list_length_inv. cbn in *. unfold PR_windows in H3. apply in_map_iff in H3 as (win' & <- & H3). 
        destruct (le_lt_dec 3 (|a|)) as [H1 | H1].  
        * econstructor 3; [ apply IH; lia | exists win'; split; [ apply H3 | ]]. 
          destruct H4; split; eauto. 
        * assert (|a| = 2) by lia. clear IH H1 H. apply valid_length_inv in H0. rewrite H2 in H0.
          list_length_inv. constructor 3; [ apply TPR.valid_vacuous; cbn; eauto| ]. 
          exists win'; split; [apply H3 | ]. destruct H4; split; eauto. 
  Qed. 

  Lemma relpower_valid_agree k (s1 s2 : list FSigma) : 
    |s1| >= 3 -> relpower (TPR.valid (rewritesHeadList Fwindows)) k s1 s2 <-> relpower (PR.valid 1 3 PR_windows) k s1 s2. 
  Proof. 
    intros; split; induction 1; [ eauto | | eauto | ]. 
    - econstructor; [ apply valid_agree; [apply H | apply H0] | apply IHrelpower]. 
      apply TPR.valid_length_inv in H0; lia. 
    - econstructor; [ apply valid_agree; [ apply H | apply H0] | apply IHrelpower]. 
      apply valid_length_inv in H0; lia. 
  Qed. 

  Lemma final_agree (s : list FSigma) : |s| = |Finit| -> TPR.satFinal Ffinal s <-> PR.satFinal 1 (length Finit) Ffinal s. 
  Proof. 
    unfold TPR.satFinal, satFinal. setoid_rewrite Nat.mul_1_r. split; intros. 
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
Definition PR_instance (tpr : TPR) := Build_PR 1 3 (TPR.init tpr) (PR_windows (TPR.windows tpr)) (TPR.final tpr) (TPR.steps tpr). 

Lemma TPR_to_PR (tpr : TPR) : TPRLang tpr <-> PRLang (PR_instance tpr). 
Proof. 
  split; intros. 
  - destruct H as (H & sf & H1 & H2). split; [ | exists sf; repeat split]. 
    + repeat split; cbn in *; [ lia | lia | exists 3; split; lia | apply H | | | ]. 
      * unfold PR_windows in *. apply in_map_iff in H0 as (win' & <- & H0). cbn. destruct win', prem, conc; now cbn.   
      * unfold PR_windows in *. apply in_map_iff in H0 as (win' & <- & H0). cbn. destruct win', prem, conc; now cbn.
      * setoid_rewrite Nat.mul_1_r. eauto. 
    + apply relpower_valid_agree, H1. apply H. 
    + apply final_agree, H2. apply TPR.relpower_valid_length_inv in H1; cbn. lia. 
  - destruct H as (H1 & sf & H2 & H3). split; [ | exists sf; repeat split]; cbn in *. 
    + destruct H1 as (_ & _ & _ & H1 &_). cbn in H1. apply H1.  
    + apply relpower_valid_agree; [ apply H1 | apply H2]. 
    + eapply final_agree, H3. apply relpower_valid_length_inv in H2. lia. 
Qed. 
