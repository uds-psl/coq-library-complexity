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
  - destruct H as (H & H0 & sf & H1 & H2 & H3). split; [ | split; [ | exists sf; repeat split]].
    + unfold FlatTPR_wellformed in H. unfold FlatPR_wellformed. cbn in *. unfold PR_windows.
      repeat split; try lia.   
      * exists 3. split; easy.  
      * apply in_map_iff in H4 as (win' & <- & H4). 
        destruct win', prem, conc; cbn in *. easy.  
      * apply in_map_iff in H4 as (win' & <- & H4). 
        destruct win', prem, conc; cbn in *. easy.  
      * setoid_rewrite Nat.mul_1_r. eauto. 
    + destruct H0 as (F1 & F2 & F3). repeat split. 
      * apply F1. 
      * apply F2. 
      * cbn in H0. unfold PR_windows in H0. 
        apply in_map_iff in H0 as (win' & <- & H0). cbn. destruct win', prem, conc; cbn.
        apply F3 in H0. destruct H0 as ((G1 & G2 & G3) & _). unfold list_ofFlatType; intros. cbn in *.
        repeat match goal with 
          |[H : ?a \/ ?b |- _] => destruct H
          | [H : False |- _] => destruct H
        end; subst; eauto.  
      * cbn in H0. unfold PR_windows in H0. 
        apply in_map_iff in H0 as (win' & <- & H0). cbn. destruct win', prem, conc; cbn.
        apply F3 in H0. destruct H0 as (_ & (G1 & G2 & G3)). unfold list_ofFlatType; intros. cbn in *.
        repeat match goal with 
          |[H : ?a \/ ?b |- _] => destruct H
          | [H : False |- _] => destruct H
        end; subst; eauto.  
    + apply H1. 
    + clear H1 H3. cbn in *. apply relpower_valid_agree, H2. apply H. 
    + apply final_agree, H3. now apply TPR.relpower_valid_length_inv in H2. 
  - destruct H as (H & H0 & sf & H1 & H2 & H3). split; [ | split; [ | exists sf; repeat split]].
    + clear H1 H2 H3. destruct H as (_ & _ & _ & F0 & _ & _).  
      unfold FlatTPR_wellformed. easy.  
    + clear H1 H2 H3. destruct H0 as (F1 & F2 & F3).
      split; [ | split]. 
      * cbn in F1; apply F1. 
      * cbn in F2. unfold FlatTPR.isValidFlatFinal. apply F2. 
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

