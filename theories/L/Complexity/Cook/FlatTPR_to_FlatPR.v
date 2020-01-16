From PslBase Require Import Base FinTypes. 
From PslBase Require Import Vectors.Vectors. 
From Undecidability Require Import L.Complexity.Cook.Prelim FlatTPR FlatPR TPR_to_PR.
Require Import Lia.

(*we can completely re-use the construction and correctness results of the TPR-PR reduction *)
(*as the reduction does not depend on the alphabet being finite *)
Definition FPR_instance (ftpr : FlatTPR) := Build_FlatPR (FlatTPR.Sigma ftpr) 1 3 (FlatTPR.init ftpr) (PR_windows (FlatTPR.windows ftpr)) (FlatTPR.final ftpr) (FlatTPR.steps ftpr).

Lemma reduction (ftpr : FlatTPR) : FlatTPRLang ftpr <-> FlatPRLang (FPR_instance ftpr). 
Proof. 
  split; intros. 
  - destruct H as (H & sf & H1 & H2 & H3). split; [ | exists sf; repeat split].  
    + destruct H as (F0 & F1 & F2 & F3). unfold FlatPR_wellformed. cbn in *.
      unfold PR_windows. 
      repeat split. 
      * lia. 
      * lia. 
      * exists 3. split; easy.  
      * apply F0. 
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
    + clear H1 H3. cbn in *. apply relpower_valid_agree, H2. apply H. 
    + apply final_agree, H3. now apply TPR.relpower_valid_length_inv in H2. 
  - destruct H as (H & sf & H1 & H2 & H3). split; [ | exists sf; repeat split]. 
    + clear H1 H2 H3. destruct H as (_ & _ & _ & F0 & _ & _ & F1 & F2 & F3). 
      split; [ | split; [ | split]]. 
      * cbn in F0. apply F0. 
      * cbn in F1; apply F1. 
      * cbn in F2. apply F2. 
      * intros [prem conc]. specialize (F3 (Build_PRWin prem conc)). 
        cbn in F3. intros H1. unfold PR_windows in F3. rewrite in_map_iff in F3. 
        assert (exists x, TPRWin_to_PRWin x = Build_PRWin prem conc /\ x el FlatTPR.windows ftpr) as H2. 
        { exists (prem / conc). cbn. eauto. }
        apply F3 in H2. destruct H2 as (H2 & H3). destruct prem, conc. cbn in *. 
        unfold list_ofFlatType in H2, H3. unfold ofFlatType in *. repeat split; cbn; eauto. 
    + apply H1. 
    + clear H1 H3. cbn in H2. apply relpower_valid_agree, H2. apply H. 
    + eapply final_agree, H3. now apply relpower_valid_length_inv in H2. 
Qed. 

(*Section fixType. *)
  (*Variable (X : Type).*)
  (*Context {H : registered X}.*)
  (*Run TemplateProgram (tmGenEncode "TPRWinP_enc" (TPRWinP X)). *)
  (*Run TemplateProgram (tmGenEncode "TPRWin_enc" (TPRWin X)). *)

(*Run TemplateProgram (tmGenEncode "FlatTPR_enc" FlatTPR).*)
(*Hint Resolve TM_enc_correct : Lrewrite.*)


(*Lemma FlatTPR_to_FlatPR : reducesPolyMO FlatTPRLang FlatPRLang. *)

