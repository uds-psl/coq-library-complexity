From PslBase Require Import Base. 
From PslBase Require Import Vectors.Vectors. 
From Undecidability Require Import L.Complexity.Cook.Prelim FlatTPR FlatPR.
Require Import Lia.

From Undecidability.L Require Import Tactics.LTactics.
From Undecidability.L.Complexity Require Import Problems.kSAT PolyBounds Tactics NP. 
From Undecidability.L.Datatypes Require Import LBool LNat Lists LProd. 

Section fixInstance. 
  Variable (ftpr : FlatTPR). 

  Notation FSigma := (FlatTPR.Sigma ftpr).
  Notation Finit := (FlatTPR.init ftpr).
  Notation Fwindows := (FlatTPR.windows ftpr).
  Notation Ffinal := (FlatTPR.final ftpr).
  Notation Fsteps := (FlatTPR.steps ftpr). 

  Definition TPRWin_to_PRWin (win : TPRWin nat) := Build_PRWin (TPRWinP_to_list (TPR.prem win)) (TPRWinP_to_list (TPR.conc win)).

  Definition PR_windows := map TPRWin_to_PRWin Fwindows. 

  Hint Constructors PR.valid. 
  Hint Constructors TPR.valid.
  Lemma valid_agree (s1 s2 : list nat) : TPR.valid (rewritesHeadList Fwindows) s1 s2 <-> PR.valid 1 3 PR_windows s1 s2. 
  Proof. 
    split. 
    - induction 1. 
      + eauto. 
      + replace (x :: a) with ([x] ++ a) by now cbn. replace (y :: b) with ([y] ++ b) by now cbn. eauto.
      + replace (x :: a) with ([x] ++ a) by now cbn. replace (y :: b) with ([y] ++ b) by now cbn. 
        destruct H0 as (rule & H1 & H2). 
        econstructor 3; [apply IHvalid | now cbn | now cbn | | ]. 
        * unfold PR_windows. apply in_map_iff. exists rule. split; eauto.
        * unfold rewritesHead. unfold TPRWin_to_PRWin. cbn. eauto. 
    - induction 1. 
      + eauto. 
      + destruct u as [ | n1 u]; cbn in H1; [ congruence | destruct u; cbn in H1; [ | congruence]]. 
        destruct v as [ | n2 v]; cbn in H2; [ congruence | destruct v; cbn in H2; [ | congruence]].
        cbn; eauto. 
      + destruct u as [ | n1 u]; cbn in H0; [ congruence | destruct u; cbn in H0; [ | congruence]]. 
        destruct v as [ | n2 v]; cbn in H1; [ congruence | destruct v; cbn in H1; [ | congruence]].
        cbn in *. destruct H3 as (H3 & H4). 
        unfold PR_windows in H2. apply in_map_iff in H2 as (rule' & <- & H2). 
        cbn in *. econstructor 3; [ apply IHvalid | ]. 
        exists rule'. split; [ apply H2 | split; eauto ]. 
  Qed. 

  Definition FPR_instance := Build_FlatPR FSigma 1 3 Finit PR_windows Ffinal Fsteps. 
End fixInstance. 

Lemma reduction (ftpr : FlatTPR) : FlatTPRLang ftpr <-> FlatPRLang (FPR_instance ftpr). 
Proof. 
  split; intros. 
  - destruct H as (H & sf & H1 & H2 & H3). split; [ | exists sf; repeat split].  
    + destruct H as (F1 & F2 & F3). unfold FlatPR_wellformed. cbn in *.
      unfold PR_windows. 
      repeat split. 
      * lia. 
      * apply in_map_iff in H as (win' & <- & H). cbn.  destruct win', prem, conc; now cbn.   
      * apply in_map_iff in H as (win' & <- & H). cbn.  destruct win', prem, conc; now cbn. 
      * setoid_rewrite Nat.mul_1_r. eauto. 
      * apply F1. 
      * apply F2. 
      * apply in_map_iff in H as (win' & <- & H). 
        apply F3 in H. destruct win', prem, conc; cbn in *. unfold list_ofFlatType. 
        destruct H as ((G1 & G2 & G3) & _). cbn in *. intros. 
        repeat match goal with 
          |[H : ?a \/ ?b |- _] => destruct H
          | [H : False |- _] => destruct H
        end; subst; eauto.  
      * apply in_map_iff in H as (win' & <- & H). 
        apply F3 in H. destruct win', prem, conc; cbn in *. unfold list_ofFlatType. 
        destruct H as (_ & (G1 & G2 & G3)). cbn in *. intros. 
        repeat match goal with 
          |[H : ?a \/ ?b |- _] => destruct H
          | [H : False |- _] => destruct H
        end; subst; eauto.
    + apply H1. 
    + clear H1 H3. cbn in *. induction H2. 
      * eauto. 
      * econstructor; [ | apply IHrelpower]. apply valid_agree, H0. 
    + unfold TPR.satFinal in H3. destruct H3 as (subs & H3 & H4). 
      exists subs; cbn. tauto.    
  - destruct H as (H & sf & H1 & H2 & H3). split; [ | exists sf; repeat split]. 
    + clear H1 H2 H3. destruct H as (_ & _ & _ & F1 & F2 & F3). 
      split; [ | split]. 
      * cbn in F1; apply F1. 
      * cbn in F2. apply F2. 
      * intros [prem conc]. specialize (F3 (Build_PRWin prem conc)). 
        cbn in F3. intros H1. unfold PR_windows in F3. rewrite in_map_iff in F3. 
        assert (exists x, TPRWin_to_PRWin x = Build_PRWin prem conc /\ x el FlatTPR.windows ftpr) as H2. 
        { exists (prem / conc). cbn. eauto. }
        apply F3 in H2. destruct H2 as (H2 & H3). destruct prem, conc. cbn in *. 
        unfold list_ofFlatType in H2, H3. repeat split; eauto. 
    + apply H1. 
    + clear H1 H3. cbn in H2. induction H2. 
      * eauto. 
      * econstructor; [ | apply IHrelpower]. apply valid_agree, H0. 
    + apply H3. 
Qed. 

(*Section fixType. *)
  (*Variable (X : Type).*)
  (*Context {H : registered X}.*)
  (*Run TemplateProgram (tmGenEncode "TPRWinP_enc" (TPRWinP X)). *)
  (*Run TemplateProgram (tmGenEncode "TPRWin_enc" (TPRWin X)). *)

(*Run TemplateProgram (tmGenEncode "FlatTPR_enc" FlatTPR).*)
(*Hint Resolve TM_enc_correct : Lrewrite.*)


(*Lemma FlatTPR_to_FlatPR : reducesPolyMO FlatTPRLang FlatPRLang. *)

