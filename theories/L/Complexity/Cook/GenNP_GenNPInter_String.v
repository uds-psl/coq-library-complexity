(* -*- company-coq-local-symbols: (("|_|" .?␣)); -*- *)
From PslBase Require Import FiniteTypes. 
From Undecidability.TM Require Import TM.
Require Import Lia. 
From Undecidability.L.Complexity.Cook Require Import GenNP TCSR Prelim GenNP_GenNPInter_Basics GenNP_GenNPInter_Tape GenNP_GenNPInter_Transition.
Require Import PslBase.FiniteTypes.BasicDefinitions. 

(** *equivalent string/rule based predicates*)
Module stringbased (sig : TMSig).
  Module trans' := transition sig.
  Export trans'.

  Definition FGamma := FinType (EqType (Gamma)). 
  Definition FstateSigma := FinType (EqType (stateSigma)). 
  Definition Fpolarity := FinType (EqType polarity).

  (*the same for rewrite windows *)
  Definition polarityRevTCSRWinP (x : TCSRWinP Gamma) : TCSRWinP Gamma :=
    match x with {σ1, σ2, σ3}=> {polarityFlipGamma σ3, polarityFlipGamma σ2, polarityFlipGamma σ1} end. 
  Definition polarityRevWin (x : TCSRWin Gamma) : TCSRWin Gamma := {| prem := polarityRevTCSRWinP (prem x); conc := polarityRevTCSRWinP (conc x)|}. 

  Lemma polarityRevWin_inv r (σ1 σ2 σ3 σ4 σ5 σ6 : Gamma) : polarityRevWin r = {σ1, σ2, σ3} / {σ4, σ5, σ6} -> r = {~σ3, ~σ2, ~σ1} / {~σ6, ~σ5, ~σ4}. 
  Proof.
    unfold polarityRevWin. destruct r, prem, conc. cbn. intros.
    inv H. now repeat rewrite polarityFlipGamma_involution. 
  Qed. 
    
  (*a rule template which instantiates the symbols with the three possible consistent polarities*)
  Definition makeRulesPol (a b c : stateSigma ) (d e f : Gamma): list (TCSRWin Gamma) :=
    [  {     inr (negative ! a) , inr(negative ! b), inr (negative ! c) }
         / { d,  e, f };
       {     inr (neutral ! a), inr (neutral ! b), inr (neutral ! c) }
         / { d, e, f};
       {     inr (positive ! a), inr (positive ! b), inr (positive ! c) }
         / { d, e, f}
    ].

  Ltac orintro := intros; repeat match goal with [H : ?a \/ ?b |- _ ] => destruct H end. 

  (** *Identity rules*)
  Definition makeIdentityRulesTemplate (x : FstateSigma * FstateSigma * FstateSigma) : list (TCSRWin Gamma) :=
    match x with (a, b, c) => makeRulesPol a b c (inr (neutral ! a)) (inr (neutral ! b)) (inr (neutral ! c)) end. 
  Lemma identityRulesTemplate_iff (σ1 σ2 σ3 :stateSigma) r : r el makeIdentityRulesTemplate (σ1, σ2, σ3) <-> exists p, r = {inr p ! σ1, inr p ! σ2, inr p ! σ3} / {inr neutral ! σ1, inr neutral ! σ2, inr neutral ! σ3}. 
  Proof.
    unfold makeIdentityRulesTemplate, makeRulesPol. split.
    - cbn; orintro; eauto. 
    - intros ([] & ->); eauto. 
  Qed. 


  (*both halves *)

  (*
    |_| |_| |_|
    |_| |_| |_|
   *)
  Definition makeIdentityRulesBlankBlankBlank := makeIdentityRulesTemplate (|_| , |_| , |_| ). 
  Lemma identityRulesBlankBlankBlank_iff r : r el makeIdentityRulesBlankBlankBlank <-> r = { inr (inr |_|) , inr (inr |_|) , inr (inr |_|) } / { inr (inr |_|) , inr (inr |_|) , inr (inr |_|) }. 
  Proof. 
    unfold makeIdentityRulesBlankBlankBlank. rewrite identityRulesTemplate_iff. cbn. split.
    - intros (_ & -> ); reflexivity. 
    - eauto. 
  Qed. 

  (* Lemma agree (γ1 γ2 γ3 γ4 γ5 γ6 : tapeSigma) : { inr γ1 , inr (γ2), inr (γ3) } / {inr (γ4) , inr (γ5) , inr (γ6)} el makeIdentityRulesBlankBlankBlank <-> identityWindow γ1 γ2 γ3 γ4 γ5 γ6. *)
  (* Proof. *)
  (*   rewrite identityRulesBlankBlankBlank_iff.  *)
  (*   split. *)
  (*   - intros. inv H. eauto.  *)
  (*   - intros. inv H. *) 

  (*
    σ1 σ2 σ3
    σ1 σ2 σ3
   *)
  Definition makeIdentityRulesSigSigSig' (x : Sigma * Sigma * Sigma) :=
    match x with (σ1, σ2, σ3) => makeIdentityRulesTemplate (Some σ1, Some σ2, Some σ3) end.
  Definition makeIdentityRulesSigSigSig := makeExhaustive makeIdentityRulesSigSigSig'.
  Lemma identityRulesSigSigSig_iff r : r el makeIdentityRulesSigSigSig <-> exists p σ1 σ2 σ3, r = { inr p !! σ1, inr p !! σ2, inr p !! σ3} / { inr neutral !! σ1, inr neutral !! σ2, inr neutral !! σ3}.
  Proof. 
    unfold makeIdentityRulesSigSigSig. rewrite makeExhaustive_correct. unfold makeIdentityRulesSigSigSig'. split.
    - intros ([[σ1 σ2] σ3] & ([] & ->)%identityRulesTemplate_iff); cbn; eauto. 
    - intros (p & σ1 & σ2 & σ3 & ->). exists (σ1, σ2, σ3). rewrite identityRulesTemplate_iff. exists p. eauto. 
  Qed. 

  (*right half *)

  (*
    σ1 |_| |_|
    σ1 |_| |_|
   *)
  Definition makeIdentityRulesSigBlankBlank' σ := makeIdentityRulesTemplate (Some σ , |_| , |_|). 
  Definition makeIdentityRulesSigBlankBlank := makeExhaustive makeIdentityRulesSigBlankBlank'. 
  Lemma identityRulesSigBlankBlank_iff r : r el makeIdentityRulesSigBlankBlank <-> exists p σ, r = { inr p !! σ, inr (inr |_|) , inr (inr |_|) } / { inr neutral !! σ , inr (inr |_|) , inr (inr |_|) }. 
  Proof. 
    unfold makeIdentityRulesSigBlankBlank. rewrite makeExhaustive_correct. unfold makeIdentityRulesSigBlankBlank'. setoid_rewrite identityRulesTemplate_iff.
    cbn. split; intros [a [b H]]; eauto. 
  Qed. 

  (*
    σ1 σ2 |_|
    σ1 σ2 |_|
   *)
  Definition makeIdentityRulesSigSigBlank' (x : Sigma * Sigma) :=
    match x with (σ1, σ2) => makeIdentityRulesTemplate (Some σ1, Some σ2, |_|) end.
  Definition makeIdentityRulesSigSigBlank := makeExhaustive makeIdentityRulesSigSigBlank'. 
  Lemma identityRulesSigSigBlank_iff r : r el makeIdentityRulesSigSigBlank <-> exists p σ1 σ2, r = { inr p !! σ1, inr p !! σ2 , inr (inr |_|) } / { inr neutral !! σ1, inr neutral !! σ2, inr (inr |_|) }. 
  Proof. 
    unfold makeIdentityRulesSigSigBlank. rewrite makeExhaustive_correct. unfold makeIdentityRulesSigSigBlank'. split.
    - intros [[σ1 σ2] ([] & ->)%identityRulesTemplate_iff]; cbn; eauto.
    - intros (p & σ1 & σ2 &  ->). exists (σ1, σ2). rewrite identityRulesTemplate_iff; exists p; eauto.  
  Qed. 

  Definition makeIdentityBoth := makeIdentityRulesBlankBlankBlank ++ makeIdentityRulesSigSigSig.
  Definition makeIdentityRight := makeIdentityRulesSigBlankBlank++ makeIdentityRulesSigSigBlank. 
  Definition makeIdentityLeft := map polarityRevWin makeIdentityRight.  (*the left rules are symmetric to the right rules *)

  Definition makeIdentity := makeIdentityBoth ++ makeIdentityRight ++ makeIdentityLeft. 


  (** *shift right rules*)
  (*of the form {a, b, c} / {↑ d, ↑ a, ↑ b} *)
  Definition makeShiftRightRulesTemplate (x : stateSigma * stateSigma * stateSigma * stateSigma) :=
    match x with (((a, b), c), d) => makeRulesPol a b c (inr (positive ! d)) (inr (positive ! a)) (inr (positive ! b)) end. 
  Lemma shiftRightRulesTemplate_iff (σ1 σ2 σ3 σ4 : stateSigma) r : r el makeShiftRightRulesTemplate (σ1, σ2, σ3, σ4) <-> exists p, r = { inr p ! σ1 , inr p ! σ2, inr p ! σ3} / { inr positive ! σ4, inr positive ! σ1, inr positive ! σ2}. 
  Proof. 
    unfold makeShiftRightRulesTemplate, makeRulesPol. cbn. split.
    - orintro; eauto. 
    - intros ([] & ->); eauto.
  Qed. 

  (* both halves*)
  (*
      σ1 σ2 σ3
      σ4 σ2 σ2
   *)
  Definition makeShiftRightRulesSigSigSigSig' (x : Sigma * Sigma * Sigma * Sigma) :=
    match x with (σ1, σ2, σ3, σ4) => makeShiftRightRulesTemplate (Some σ1, Some σ2, Some σ3, Some σ4) end. 
  Definition makeShiftRightRulesSigSigSigSig := makeExhaustive makeShiftRightRulesSigSigSigSig'. 
  Lemma shiftRightRulesSigSigSigSig_iff r : r el makeShiftRightRulesSigSigSigSig <-> exists p σ1 σ2 σ3 σ4, r = { inr p !! σ1, inr p !! σ2, inr p !! σ3} / {inr positive !! σ4, inr positive !! σ1, inr positive !! σ2}. 
  Proof. 
    unfold makeShiftRightRulesSigSigSigSig. rewrite makeExhaustive_correct. unfold makeShiftRightRulesSigSigSigSig'. split.
    - intros [[[[σ1 σ2] σ3] σ4] ([] & ->)%shiftRightRulesTemplate_iff]; cbn; eauto 10. 
    - intros (p & σ1 & σ2 & σ3 & σ4 & ->). exists (σ1, σ2, σ3, σ4); rewrite shiftRightRulesTemplate_iff; exists p; eauto. 
  Qed. 

  (* right half*)

  (*
    |_| |_| |_|
    σ1  |_| |_|
   *)
  Definition makeShiftRightRulesBlankBlankBlank' (σ : Sigma) := makeShiftRightRulesTemplate (|_| , |_| , |_| , Some σ).
  Definition makeShiftRightRulesBlankBlankBlank := makeExhaustive makeShiftRightRulesBlankBlankBlank'. 
  Lemma shiftRightRulesBlankBlankBlank_iff r : r el makeShiftRightRulesBlankBlankBlank <-> exists σ, r = { inr (inr |_|) , inr (inr |_|) , inr (inr |_|) } / { inr positive !! σ , inr (inr |_|) , inr (inr |_|)}. 
  Proof. 
    unfold makeShiftRightRulesBlankBlankBlank. rewrite makeExhaustive_correct. unfold makeShiftRightRulesBlankBlankBlank'. split. 
    - intros [σ ([] & ->)%shiftRightRulesTemplate_iff]; cbn; eauto. 
    - intros (σ & ->); exists σ; rewrite shiftRightRulesTemplate_iff; eauto. Unshelve. exact positive. 
  Qed. 

  (*
    σ1 |_| |_|
    σ2  σ1 |_|
   *)
  Definition makeShiftRightRulesSigBlankBlank' (x : Sigma * Sigma) :=
    match x with (σ1, σ2) => makeShiftRightRulesTemplate (Some σ1, |_| , |_| , Some σ2) end.
  Definition makeShiftRightRulesSigBlankBlank := makeExhaustive makeShiftRightRulesSigBlankBlank'. 
  Lemma shiftRightRulesSigBlankBlank_iff r : r el makeShiftRightRulesSigBlankBlank <-> exists p σ1 σ2, r = {inr p !! σ1, inr (inr |_|) , inr (inr |_|) } / { inr positive !! σ2 , inr positive !! σ1, inr (inr |_|) }. 
  Proof.
    unfold makeShiftRightRulesSigBlankBlank. rewrite makeExhaustive_correct. unfold makeShiftRightRulesSigBlankBlank'. split.
    - intros [[σ1 σ2] ([] & ->)%shiftRightRulesTemplate_iff]; cbn; eauto. 
    - intros (p & σ1 & σ2 & ->); exists (σ1, σ2); rewrite shiftRightRulesTemplate_iff. exists p; eauto. 
  Qed. 

  (*
    σ1 σ2 |_|
    σ3 σ1 σ2
  *)
  Definition makeShiftRightRulesSigSigBlank' (x : Sigma * Sigma * Sigma) :=
    match x with (σ1, σ2, σ3) => makeShiftRightRulesTemplate (Some σ1, Some σ2, |_| , Some σ3) end. 
  Definition makeShiftRightRulesSigSigBlank := makeExhaustive makeShiftRightRulesSigSigBlank'. 
  Lemma shiftRightRulesSigSigBlank_iff r : r el makeShiftRightRulesSigSigBlank <-> exists p σ1 σ2 σ3, r = {inr p !! σ1, inr p !! σ2, inr (inr |_|)} / {inr positive !! σ3, inr positive !! σ1, inr positive !! σ2}. 
  Proof. 
    unfold makeShiftRightRulesSigSigBlank. rewrite makeExhaustive_correct. unfold makeShiftRightRulesSigSigBlank'. split.
    - intros [[[σ1 σ2] σ3] ([] & ->)%shiftRightRulesTemplate_iff]; cbn; eauto.
    - intros (p & σ1 & σ2 & σ3 & ->); exists (σ1, σ2, σ3); rewrite shiftRightRulesTemplate_iff. exists p; eauto. 
  Qed. 

  (*left half*)

  (*
    |_| |_| σ1
    |_| |_| |_|
   *)
  Definition makeShiftRightRulesBlankBlankSig' (σ : Sigma) := makeShiftRightRulesTemplate (|_| , |_| , Some σ , |_| ).
  Definition makeShiftRightRulesBlankBlankSig := makeExhaustive makeShiftRightRulesBlankBlankSig'. 
  Lemma shiftRightRulesBlankBlankSig_iff r : r el makeShiftRightRulesBlankBlankSig <-> exists p σ, r = {inr (inr |_|) , inr (inr |_|) , inr p !! σ} / { inr (inr |_|) , inr (inr |_|) , inr (inr |_|)}. 
  Proof. 
    unfold makeShiftRightRulesBlankBlankSig. rewrite makeExhaustive_correct. unfold makeShiftRightRulesBlankBlankSig'. split. 
    - intros [σ ([] & ->)%shiftRightRulesTemplate_iff]; cbn; eauto. 
    - intros (p & σ & ->); exists σ. rewrite shiftRightRulesTemplate_iff; exists p; eauto. 
  Qed. 

  (*
    |_| σ1 σ2
    |_| |_| σ1
   *)
  Definition makeShiftRightRulesBlankSigSig' (x : Sigma * Sigma) :=
    match x with (σ1, σ2) => makeShiftRightRulesTemplate (|_| , Some σ1, Some σ2, |_|) end.
  Definition makeShiftRightRulesBlankSigSig := makeExhaustive makeShiftRightRulesBlankSigSig'. 
  Lemma shiftRightRulesBlankSigSig_iff r : r el makeShiftRightRulesBlankSigSig <-> exists p σ1 σ2, r = {inr (inr |_|), inr p !! σ1, inr p !! σ2} / {inr (inr |_|) , inr (inr |_|), inr positive !! σ1}. 
  Proof.
    unfold makeShiftRightRulesBlankSigSig. rewrite makeExhaustive_correct. unfold makeShiftRightRulesBlankSigSig'. split. 
    - intros [[σ1 σ2] ([] & ->)%shiftRightRulesTemplate_iff]; cbn; eauto. 
    - intros (p & σ1 & σ2 & ->); exists (σ1, σ2). rewrite shiftRightRulesTemplate_iff; exists p; eauto. 
  Qed. 

  (*
    σ1  σ2 σ3
    |_| σ1 σ2
   *)
  Definition makeShiftRightRulesSigSigSigBlank' (x : Sigma * Sigma * Sigma) :=
    match x with (σ1, σ2, σ3) => makeShiftRightRulesTemplate (Some σ1, Some σ2, Some σ3, |_|) end. 
  Definition makeShiftRightRulesSigSigSigBlank := makeExhaustive makeShiftRightRulesSigSigSigBlank'. 

  Lemma shiftRightRulesSigSigSigBlank_iff r : r el makeShiftRightRulesSigSigSigBlank <-> exists p σ1 σ2 σ3, r = {inr p !! σ1, inr p !! σ2, inr p !! σ3} / {inr (inr |_|), inr positive !! σ1, inr positive !! σ2}. 
  Proof. 
    unfold makeShiftRightRulesSigSigSigBlank. rewrite makeExhaustive_correct. unfold makeShiftRightRulesSigSigSigBlank'. split. 
    - intros [[[σ1 σ2] σ3] ([] & ->)%shiftRightRulesTemplate_iff]; cbn; eauto. 
    - intros (p & σ1 & σ2 & σ3 & ->); exists (σ1, σ2, σ3). rewrite shiftRightRulesTemplate_iff; exists p; eauto.
  Qed. 

  Definition makeShiftRightBoth := makeShiftRightRulesSigSigSigSig. 
  Definition makeShiftRightRight := makeShiftRightRulesBlankBlankBlank ++ makeShiftRightRulesSigBlankBlank ++ makeShiftRightRulesSigSigBlank. 
  Definition makeShiftRightLeft := makeShiftRightRulesBlankBlankSig ++ makeShiftRightRulesBlankSigSig ++ makeShiftRightRulesSigSigSigBlank. 
  Definition makeShiftRight := makeShiftRightBoth ++ makeShiftRightRight ++ makeShiftRightLeft. 
                
  (** *shift left rules *) 
  (*these can be derived from the rules for shifting right due to symmetry *)
  Definition makeShiftLeft := map polarityRevWin makeShiftRight. 

  Definition makeTapeRules := makeIdentity ++ makeShiftRight ++ makeShiftLeft. 


  Ltac rewHeadTape_inv2 := repeat match goal with
                                  | [H : rewHeadTape _ _ |- _] => inv H
                                  | [H : shiftRightWindow _ _ _ _ _ _ |- _ ] => inv H
                                  | [H : identityWindow _ _ _ _ _ _ |- _] => inv H
                                  | [H : |_| = # ?σ |- _] => is_var σ; destruct σ; cbn in H; try congruence
                                  | [H : # ?σ = |_| |- _] => is_var σ; destruct σ; cbn in H; try congruence
                                  | [H : Some (_, _) = % ?e |- _] => symmetry in H; apply polarityFlipTapeSigmaInv1 in H; rewrite H in *; clear H
                                  | [H : % ?e = Some (_, _) |- _] => apply polarityFlipTapeSigmaInv1 in H; rewrite H in *; clear H
                                  | [H : Some (_, _) = # ?e |- _] => symmetry in H; apply polarityFlipTapeSigma'Inv1 in H; rewrite H in *; clear H
                                  | [H : # ?e = Some (_, _) |- _] => apply polarityFlipTapeSigma'Inv1 in H; rewrite H in *; clear H
                                  | [H : |_| = |_| |- _] => clear H
                                  | [ |- context [inr (inr (# ?e))]] => rewrite polarityFlip_push_in
                           end. 
 
  Hint Extern 1 => apply in_or_app. 
  Hint Extern 1 => rewrite identityRulesSigSigSig_iff. 

  Lemma shift_right_agree (γ1 γ2 γ3 γ4 γ5 γ6 : Gamma) : shiftRightWindow γ1 γ2 γ3 γ4 γ5 γ6 <-> { γ1, γ2, γ3} / { γ4, γ5, γ6} el makeShiftRight. 
  Proof with apply in_or_app. 
    split. 
    - intros. inv H; unfold makeShiftRight... 
      + left. unfold makeShiftRightBoth. 
        apply shiftRightRulesSigSigSigSig_iff. exists p. exists σ1, σ2, σ3, σ4. eauto. 
      + right... left. unfold makeShiftRightRight... 
        left. apply shiftRightRulesBlankBlankBlank_iff. exists σ1. eauto. 
      + right... left. unfold makeShiftRightRight...
        right... left. apply shiftRightRulesSigBlankBlank_iff. exists p, σ1, σ2. eauto. 
      + right... left. unfold makeShiftRightRight... 
        right... right. apply shiftRightRulesSigSigBlank_iff. exists p, σ1, σ2, σ3. eauto.
      + right... right. unfold makeShiftRightLeft...
        left. apply shiftRightRulesBlankBlankSig_iff. exists p, σ1. eauto. 
      + right... right. unfold makeShiftRightLeft...
        right... left. apply shiftRightRulesBlankSigSig_iff. exists p, σ1, σ2. eauto. 
      + right... right. unfold makeShiftRightLeft...
        right... right. apply shiftRightRulesSigSigSigBlank_iff. exists p, σ1, σ2, σ3. eauto. 
    - intros.
      repeat match goal with
             | [ H : _ el _ |- _] => apply in_app_or in H
             | [H : _ \/ _ |- _] => destruct H as [H | H]
             end. 
      1: unfold makeShiftRightBoth in H; apply shiftRightRulesSigSigSigSig_iff in H. 
      2: apply shiftRightRulesBlankBlankBlank_iff in H. 
      3: apply shiftRightRulesSigBlankBlank_iff in H.
      4: apply shiftRightRulesSigSigBlank_iff in H. 
      5: apply shiftRightRulesBlankBlankSig_iff in H.
      6: apply shiftRightRulesBlankSigSig_iff in H.
      7: apply shiftRightRulesSigSigSigBlank_iff in H. 

      all: repeat match goal with
      | [H: exists _, _ |- _ ] => destruct H as (? & H)
      end; inv H; cbn; unfold withPolaritySigma; eauto. 
  Qed. 

  Lemma identity_agree (σ1 σ2 σ3 σ4 σ5 σ6 : Gamma) : identityWindow σ1 σ2 σ3 σ4 σ5 σ6 <-> { σ1, σ2, σ3} / { σ4, σ5, σ6 } el makeIdentity.
  Proof with apply in_or_app. 
    (* split.  *)
  Admitted.  

  Lemma string_agree a b : rewritesHead_pred makeTapeRules a b <-> rewHeadTape a b.
  Proof. 
    (* split.  *)
    (* - intros. unfold rewritesHead_pred in H. destruct H as (r & H1 & H2). *)
    (*   unfold makeTapeRules in H1. apply in_app_or in H1; destruct H1 as [H1 | H1]; [ | apply in_app_or in H1; destruct H1 as [H1 | H1]].  *)
    (*   + destruct r. destruct prem, conc. *)

    (*     apply identity_agree in H1. *)

    (* 2: { *)
    (*   intros.  *)
    (*   unfold rewritesHead_pred. *)
    (*   rewHeadTape_inv2.  *)
    (*   + evar (γ1 : Gamma). evar (γ2 : Gamma). evar (γ3 : Gamma). evar (γ4 : Gamma). evar (γ5 : Gamma). evar (γ6 : Gamma). *)
    (*     exists ({γ1, γ2, γ3} / {γ4, γ5, γ6}). *)
    (*     split.  *)
    (*     2: { *)
    (*       unfold rewritesHead. split.  *)
    (*       unfold prefix. exists h1. subst γ1 γ2 γ3 γ4 γ5 γ6. cbn. reflexivity.  *)
    (*       subst γ1 γ2 γ3 γ4 γ5 γ6. unfold prefix. exists h2. cbn. reflexivity.  *)
    (*     } *)
    (*     subst γ1 γ2 γ3 γ4 γ5 γ6.   *)
    (*     unfold makeTapeRules.  *)
    (*     apply in_or_app. right. apply in_or_app. right.  *)
    (*     unfold makeShiftLeft.  *)
    (*     unfold makeIdentityBoth. apply in_or_app. right.  *)
    (*     rewrite identityRulesSigSigSig_iff. exists (polarityFlip p). eauto 12.  *)
    (*     Set Debug Eauto.  *)
    (*     eauto 8.  *)

      
    (*   - split.  *)
    (*     +  *)
    (* } *)
    (* - unfold rewritesHead_pred. intros (r & H1 & H2).  *)
    (*   destruct H2 as (H2 & H3).  *)
    (*   unfold makeTapeRules in H1. *)
    (*   apply in_app_or in H1; destruct H1 as [H1 | H1]; [ | apply in_app_or in H1; destruct H1]. *)
    (*   + unfold makeIdentity in H1. *)
    (*     apply in_app_or in H1; destruct H1 as [H1 | H1]; [ | apply in_app_or in H1; destruct H1]. *)
    (*     * unfold makeIdentityBoth in H1.  *)
    (*       apply in_app_or in H1; destruct H1 as [H1 | H1].  *)
    (*       -- apply identityRulesBlankBlankBlank_iff in H1. subst. cbn in *.  *)
    (*          unfold prefix in *. destruct H2 as (b' & ->). destruct H3 as (a' & ->).  *)
    (*          apply rewHeadTape_tail_invariant with (h1' := []) (h2' := []).  *)
    (*          eauto.  *)
    (*      -- apply identityRulesSigSigSig_iff in H1. destruct H1 as (? & ? & ? & ? & H1).  *)
    (*         subst.  *)
    (*         unfold prefix in *. destruct H2 as (b' & ->). destruct H3 as (a' & ->).  *)
    (*          apply rewHeadTape_tail_invariant with (h1' := []) (h2' := []). *)
    (*          unfold withPolaritySigma. eauto.  *)
    (*          eauto.  *)
  Admitted. 


  Section finTypeRepr.
    Definition finRepr (X : finType) (n : nat) := n = length (elem X ). 
    Definition finReprEl (X : finType) (n : nat) k (x : X) := finRepr X n /\ k < n /\ index x = k.  

    Definition flatOption (n : nat) := S n.
    Definition flatProd (a b : nat) := a * b.
    Definition flatSum (a b : nat) := a + b.

    Definition flatNone := 0.
    Definition flatSome k := S k. 
    Definition flatInl (k : nat) := k.
    Definition flatInr (a: nat) k := a + k. 
    Definition flatPair (a b : nat) x y := x * b + y. 

    Lemma finReprOption (X : finType) (n : nat) : finRepr X n -> finRepr (FinType (EqType (option X))) (flatOption n).
    Proof. 
      intros. unfold finRepr in *. unfold flatOption; cbn -[enum]. rewrite H; cbn.
      rewrite map_length. reflexivity. 
    Qed. 


    Lemma finReprElSome (X : finType) n k x : finReprEl n k x -> @finReprEl (FinType (EqType (option X))) (flatOption n) (flatSome k) (Some x). 
    Proof. 
      intros (H1 & H2 & H3). split; [ | split]; cbn in *.
      - now apply finReprOption. 
      - now unfold flatSome, flatOption.
      - rewrite getPosition_map. 2: unfold injective; congruence. now rewrite <- H3. 
    Qed. 

    Lemma finReprElNone (X : finType) n : finRepr X n -> @finReprEl (FinType (EqType (option X))) (flatOption n) flatNone None. 
    Proof. 
      intros. split; [ | split]; cbn. 
      - now apply finReprOption.
      - unfold flatNone, flatOption. lia. 
      - now unfold flatNone. 
    Qed. 

    Lemma finReprSum (A B: finType) (a b : nat) : finRepr A a -> finRepr B b -> finRepr (FinType (EqType (sum A B))) (flatSum a b). 
    Proof. 
      intros. unfold finRepr in *. unfold flatSum; cbn in *.
      rewrite app_length. rewrite H, H0.
      unfold toSumList1, toSumList2. now rewrite !map_length.
    Qed. 

    Lemma finReprElInl (A B : finType) (a b : nat) k x : finRepr B b -> finReprEl a k x -> @finReprEl (FinType (EqType (sum A B))) (flatSum a b) (flatInl k) (inl x). 
    Proof. 
      intros H0 (H1 & H2 & H3). split; [ | split]. 
      - now apply finReprSum. 
      - now unfold flatInl, flatSum. 
      - unfold finRepr in H1. rewrite H1 in *. 
        clear H0 H1. cbn. unfold toSumList1, toSumList2, flatInl. 
        rewrite getPosition_app1 with (k := k).
        + reflexivity. 
        + now rewrite map_length. 
        + unfold index in H3. rewrite <- getPosition_map with (f := (@inl A B)) in H3. 2: now unfold injective.
          easy. 
    Qed. 

    Lemma finReprElInr (A B : finType) (a b : nat) k x : finRepr A a -> finReprEl b k x -> @finReprEl (FinType (EqType (sum A B))) (flatSum a b) (flatInr a k) (inr x). 
    Proof. 
      intros H0 (H1 & H2 & H3). split; [ | split ]. 
      - now apply finReprSum. 
      - now unfold flatInr, flatSum. 
      - unfold finRepr in H1; rewrite H1 in *. clear H1. 
        cbn. unfold toSumList1, toSumList2, flatInr. 
        rewrite getPosition_app2 with (k := k). 
        + rewrite map_length. unfold finRepr in H0. now cbn. 
        + now rewrite map_length.
        + intros H1. apply in_map_iff in H1. destruct H1 as (? & ? &?); congruence. 
        + unfold index in H3. rewrite <- getPosition_map with (f := (@inr A B)) in H3. 2: now unfold injective. 
          easy. 
    Qed. 

    Lemma finReprProd (A B : finType) (a b : nat) : finRepr A a -> finRepr B b -> finRepr (FinType (EqType (prod A B))) (flatProd a b).  
    Proof. 
      intros. unfold finRepr in *. unfold flatProd.
      cbn. now rewrite prodLists_length. 
    Qed. 

    Lemma finReprElPair (A B : finType) (a b : nat) k1 k2 x1 x2 : finReprEl a k1 x1 -> finReprEl b k2 x2 -> @finReprEl (FinType (EqType (prod A B))) (flatProd a b) (flatPair a b k1 k2) (pair x1 x2).
    Proof. 
      intros (H1 & H2 & H3) (F1 & F2 & F3). split; [ | split]. 
      - now apply finReprProd. 
      - unfold flatPair, flatProd. nia. 
      - cbn. unfold flatPair. unfold finRepr in *. rewrite H1, F1 in *.
        rewrite getPosition_prodLists with (k1 := k1) (k2 := k2); eauto. 
    Qed. 

  End finTypeRepr.

  Section finTypeExpressions. 

    (*this basically mirrors the structure of the alphabet, but using abstract constructors that can be replaced with either the usual Coq constructors or flat constructors for L *)
    Inductive sigVar := Sig1 | Sig2 | Sig3 | Sig4.

    Inductive fpolSigma := psConsC : polarity -> sigVar -> fpolSigma | psConsV : sigVar -> fpolSigma. 
    Definition fstateSigma := option sigVar.
    Definition ftapeSigma' := option fpolSigma.
    Definition ftapeSigma := sum delim ftapeSigma'. 
    Definition fStates := fstateSigma.
    Definition fGamma := sum fStates ftapeSigma. 


    Record evalEnv X Y Z := {
                          pV : X;
                          stateV : Y;
                          sV1 : Z;
                          sV2 : Z;
                          sV3 : Z;
                          sV4 : Z
                        }.

    Definition reifySigVar {X Y Z : Type} (env : evalEnv X Y Z) v := match v with
                                                | Sig1 => sV1 env
                                                | Sig2 => sV2 env
                                                | Sig3 => sV3 env 
                                                | Sig4 => sV4 env
                                                end. 

    Definition reifyPolSigmaFin (env : evalEnv polarity states Sigma) (c : fpolSigma) :=
      match c with
        | psConsC p sv => (p, reifySigVar env sv)
        | psConsV sv => (pV env, reifySigVar env sv)
      end. 
    Definition reifyStateSigmaFin (env : evalEnv polarity states Sigma) (c : fstateSigma) :=
      match c with
      | None => None
      | Some sv => Some (reifySigVar env sv)
      end. 
    Definition reifyTapeSigma'Fin (env : evalEnv polarity states Sigma) (c : ftapeSigma') : tapeSigma' :=
      match c with
      | None => None
      | Some c => Some (reifyPolSigmaFin env c)
      end. 
    Definition reifyTapeSigmaFin (env : evalEnv polarity states Sigma) (c : ftapeSigma) : tapeSigma :=
      match c with
      | inl delimC => inl delimC
      | inr c => inr (reifyTapeSigma'Fin env c)
      end. 
    Definition reifyStatesFin (env : evalEnv polarity states Sigma) (c : fStates) : States := (stateV env, reifyStateSigmaFin env c).
    Definition reifyGammaFin (env : evalEnv polarity states Sigma) (c : fGamma) : Gamma :=
      match c with
      | inl c => inl (reifyStatesFin env c)
      | inr c => inr (reifyTapeSigmaFin env c)
      end. 


    Definition flatPolarity := 3.
    Definition flatDelim := 1. 
    Definition flatDelimC := 0.
    Definition flatSigma := length (elem Sigma). 
    Definition flatstates := length (elem states). 

    Definition flattenPolarity (p : polarity) := index p. 

    Notation flatPolSigma := (flatProd flatPolarity flatSigma).
    Notation flatTapeSigma' := (flatOption flatPolSigma).
    Notation flatTapeSigma := (flatSum flatDelim flatTapeSigma').
    Notation flatStateSigma := (flatOption flatSigma).
    Notation flatStates := (flatProd flatstates flatStateSigma).
    Notation flatGamma := (flatSum flatStates flatTapeSigma). 
                            

    Definition reifyPolSigmaFlat (env : evalEnv nat nat nat) c :=
      match c with
      | psConsC p sv => flatPair flatPolarity flatSigma (flattenPolarity p) (reifySigVar env sv)
      | psConsV sv => flatPair flatPolarity flatSigma (pV env) (reifySigVar env sv)
    end. 
    Definition reifyStateSigmaFlat (env : evalEnv nat nat nat) c :=
      match c with
      | None => flatNone
      | Some sv => flatSome (reifySigVar env sv)
      end. 
    Definition reifyTapeSigma'Flat (env : evalEnv nat nat nat) c :=
      match c with
      | None => flatNone
      | Some c => flatSome (reifyPolSigmaFlat env c)
      end. 
    Definition reifyTapeSigmaFlat (env : evalEnv nat nat nat) c :=
      match c with
      | inl delimC => flatInl flatDelimC
      | inr c => flatInr flatDelim (reifyTapeSigma'Flat env c)
    end. 
    Definition reifyStatesFlat (env : evalEnv nat nat nat) c := flatPair flatstates flatStateSigma (stateV env) (reifyStateSigmaFlat env c).
    Definition reifyGammaFlat (env : evalEnv nat nat nat) c :=
      match c with
      | inl c => flatInl (reifyStatesFlat env c)
      | inr c => flatInr flatStates (reifyTapeSigmaFlat env c)
      end. 

    Lemma flattenPolarity_reprEl p : finReprEl flatPolarity (flattenPolarity p) p. 
    Proof. 
      unfold finReprEl. 
      split; [ | split]. 
      - unfold finRepr. unfold flatPolarity. unfold elem. now cbn.
      - destruct p; unfold flatPolarity; cbn; lia. 
      - destruct p; cbn; lia.
    Qed. 

    Definition isFlatEnvOf (a : evalEnv nat nat nat) (b : evalEnv polarity states Sigma) :=
      finReprEl flatPolarity (pV a) (pV b)
      /\ finReprEl flatstates (stateV a) (stateV b)
      /\ finReprEl flatSigma (sV1 a) (sV1 b)
      /\ finReprEl flatSigma (sV2 a) (sV2 b)
      /\ finReprEl flatSigma (sV3 a) (sV3 b)
      /\ finReprEl flatSigma (sV4 a) (sV4 b). 

    Lemma reifySigVar_reprEl a b c : isFlatEnvOf a b -> finReprEl flatSigma (reifySigVar a c) (reifySigVar b c). 
    Proof. 
      intros (_ & _ & H1 & H2 & H3 & H4). destruct c; cbn; assumption. 
    Qed.

    Lemma isFlatEnv_polarity a b : isFlatEnvOf a b -> finReprEl flatPolarity (pV a) (pV b). 
    Proof. intros. apply H. Qed. 

    Lemma isFlatEnv_states a b : isFlatEnvOf a b -> finReprEl flatstates (stateV a) (stateV b). 
    Proof. intros. apply H. Qed. 

    Smpl Create finRepr. 
    Smpl Add (apply finReprElPair) : finRepr.
    Smpl Add (apply finReprElNone) : finRepr. 
    Smpl Add (apply finReprElSome) : finRepr.
    Smpl Add (apply finReprElInl) : finRepr.
    Smpl Add (apply finReprElInr) : finRepr. 

    Smpl Add (apply finReprProd) : finRepr.
    Smpl Add (apply finReprOption) : finRepr.
    Smpl Add (apply finReprSum) : finRepr. 

    Smpl Add (apply reifySigVar_reprEl) : finRepr.
    Smpl Add (apply flattenPolarity_reprEl) : finRepr. 
    Smpl Add (apply isFlatEnv_polarity) : finRepr.
    Smpl Add (apply isFlatEnv_states) : finRepr. 

    Ltac finRepr_simpl := smpl finRepr; repeat smpl finRepr. 

    Lemma delimC_reprEl : finReprEl flatDelim flatDelimC delimC.  
    Proof. 
      split; [ | split]. 
      - unfold finRepr. auto. 
      - auto. 
      - auto. 
    Qed. 

    Smpl Add (apply delimC_reprEl) : finRepr. 

    Lemma reifyPolSigma_reprEl a b c: isFlatEnvOf a b -> finReprEl flatPolSigma (reifyPolSigmaFlat a c) (reifyPolSigmaFin b c). 
    Proof.
      intros. destruct c; cbn [reifyPolSigmaFlat reifyPolSigmaFin]; unfold flatPolSigma; now finRepr_simpl.
    Qed. 

    Smpl Add (apply reifyPolSigma_reprEl) : finRepr.

    Lemma reifyStateSigma_reprEl a b c : isFlatEnvOf a b -> finReprEl flatStateSigma (reifyStateSigmaFlat a c) (reifyStateSigmaFin b c). 
    Proof.
      intros. destruct c; cbn [reifyStateSigmaFin reifyStateSigmaFlat]; now finRepr_simpl.
    Qed. 

    Smpl Add (apply reifyStateSigma_reprEl) : finRepr. 

    Lemma reifyTapeSigma'_reprEl a b c : isFlatEnvOf a b -> finReprEl flatTapeSigma' (reifyTapeSigma'Flat a c) (reifyTapeSigma'Fin b c). 
    Proof.
      intros. destruct c; cbn [reifyTapeSigma'Flat reifyTapeSigma'Fin]; now finRepr_simpl.
    Qed.

    Smpl Add (apply reifyTapeSigma'_reprEl) : finRepr. 

    Lemma reifyTapeSigma_reprEl a b c : isFlatEnvOf a b -> finReprEl flatTapeSigma (reifyTapeSigmaFlat a c) (reifyTapeSigmaFin b c). 
    Proof. 
      intros. destruct c; cbn [reifyTapeSigmaFlat reifyTapeSigmaFin]; try destruct d; now finRepr_simpl.
    Qed. 

    Smpl Add (apply reifyTapeSigma_reprEl) : finRepr.

    Lemma reifyStates_reprEl a b c : isFlatEnvOf a b -> finReprEl flatStates (reifyStatesFlat a c) (reifyStatesFin b c). 
    Proof.
      intros. now finRepr_simpl. 
    Qed.

    Smpl Add (apply reifyStates_reprEl) : finRepr.

    Lemma reifyGamma_reprEl a b c : isFlatEnvOf a b -> finReprEl flatGamma (reifyGammaFlat a c) (reifyGammaFin b c). 
    Proof.
      intros. destruct c; cbn [reifyGammaFlat reifyGammaFin]; now finRepr_simpl. 
    Qed. 

    Smpl Add (apply reifyGamma_reprEl) : finRepr.

    Definition reifyWindow (Y : Type) (r : fGamma -> Y) rule := match rule with {a, b, c} / {d, e, f} => {r a, r b, r c} / {r d, r e, r f} end. 


    Definition isFlatWinPOf (X : finType) (x : nat)(b : TCSRWinP nat) (a : TCSRWinP X) :=
      finReprEl x (winEl1 b) (winEl1 a) /\ finReprEl x (winEl2 b) (winEl2 a) /\ finReprEl x (winEl3 b) (winEl3 a).  

    Definition isFlatWindowOf (X : finType) (x : nat) (b : window nat) (a : window X):=
      isFlatWinPOf x (prem b) (prem a) /\ isFlatWinPOf x (conc b) (conc a) . 

    Lemma reifyWindow_reprEl (X : finType) x reifyFlat reifyFin w : (forall c, finReprEl x (reifyFlat c) (reifyFin c)) -> @isFlatWindowOf X x (reifyWindow reifyFlat w) (reifyWindow reifyFin w). 
    Proof. 
      intros. 
      destruct w. cbn. destruct prem, conc. split; cbn. 
      + split; [ | split]; cbn; auto.
      + split; [ | split]; cbn; auto.
    Qed. 

    Lemma reifyWindow_Gamma_isFlatWindowOf evalFlat evalFin w: isFlatEnvOf evalFlat evalFin -> isFlatWindowOf flatGamma (reifyWindow (reifyGammaFlat evalFlat) w) (reifyWindow (reifyGammaFin evalFin) w).
    Proof. 
      intros. apply reifyWindow_reprEl. intros. now apply reifyGamma_reprEl. 
    Qed. 


    (*create all evaluation environments for listable types *)
    Definition tupToEvalEnv (X Y Z : Type) tup := match tup with (a, b, c, d, e, f) => @Build_evalEnv X Y Z a b c d e f end. 
    Definition makeAllEnv (X Y Z : Type) (allX : list X) (allY : list Y) (allZ : list Z) :=
      map (@tupToEvalEnv X Y Z) (prodLists (prodLists (prodLists (prodLists (prodLists allX allY) allZ) allZ) allZ) allZ). 

    Lemma prodLists_correct (X Y : Type) (A : list X) (B : list Y) a b : (a, b) el prodLists A B <-> a el A /\ b el B. 
    Proof. 
      induction A; cbn.
      - tauto.
      - split; intros.
        + apply in_app_iff in H. destruct H as [H | H].
          * apply in_map_iff in H; destruct H as (? & H1 & H2). inv H1. auto. 
          * apply IHA in H. tauto. 
        + destruct H as [[H1 | H1] H2].
          * apply in_app_iff. left. apply in_map_iff. exists b. firstorder. 
          * apply in_app_iff. right. now apply IHA. 
    Qed. 

    Lemma makeAllEnv_correct (X Y Z : Type) (listX : list X) (listY : list Y) (listZ : list Z) a b c d e f: (Build_evalEnv a b c d e f) el makeAllEnv listX listY listZ <-> a el listX /\ b el listY /\ c el listZ /\ d el listZ /\ e el listZ /\ f el listZ. 
    Proof. 
      unfold makeAllEnv. rewrite in_map_iff. split.
      + intros ([[[[[]]]]] & H1 & H2). inv H1. repeat apply prodLists_correct in H2 as [H2  ?]. tauto.
      + intros (? & ? & ? & ? & ? & ?). exists (a, b, c, d, e, f). split.
        * now cbn. 
        * repeat (apply prodLists_correct; split); auto.
    Qed. 
    
    (*instantiate all rules - the resulting list is ordered by rules *)

    Definition makeRules' (X Y Z W : Type) (reify : evalEnv X Y Z -> fGamma -> W)  (l : list (evalEnv X Y Z)) rule:= map (fun env => reifyWindow (reify env) rule) l. 
    Definition makeRules (X Y Z W : Type) (reify : evalEnv X Y Z -> fGamma -> W) (allX : list X) (allY : list Y) (allZ : list Z) (rules : list (window fGamma)) :=
      let listEnv := makeAllEnv allX allY allZ in concat (map (makeRules' reify listEnv) rules). 

    Definition makeRulesFin := makeRules reifyGammaFin. 
    Definition makeRulesFlat := makeRules reifyGammaFlat. 

    (*we now prove our main result: if we plug lists whose elements are related by finReprEl into makeRulesFlat and makeRulesFin, both procedures do produce exactly the same rules up to finReprEl *)

    Definition list_finReprEl (X : finType) (x : nat) (A : list X) (B : list nat) :=
      (forall n, n el B -> exists a, finReprEl x n a /\ a el A) /\ (forall a, a el A -> exists n, finReprEl x n a /\ n el B). 

    Definition list_isFlatEnvOf (envFinList : list (evalEnv polarity states Sigma)) (envFlatList : list (evalEnv nat nat nat)) :=
      (forall envFlat, envFlat el envFlatList -> exists envFin, isFlatEnvOf envFlat envFin /\ envFin el envFinList)
      /\ (forall envFin, envFin el envFinList -> exists envFlat, isFlatEnvOf envFlat envFin /\ envFlat el envFlatList).
                                                    
    Lemma makeEnv_isFlatEnvOf (Afin : list polarity) (Bfin : list states) (Cfin : list Sigma) (Aflat Bflat Cflat : list nat):
      list_finReprEl flatPolarity Afin Aflat -> list_finReprEl flatstates Bfin Bflat -> list_finReprEl flatSigma Cfin Cflat ->
      list_isFlatEnvOf (makeAllEnv Afin Bfin Cfin) (makeAllEnv Aflat Bflat Cflat).
    Proof. 
      intros.  split.
      all: intros [] (F1 & F2 & F3 & F4 & F5 & F6)%makeAllEnv_correct. 
      all:  apply H in F1 as (a & F1 & F1').
      all:  apply H0 in F2 as (b & F2 & F2').
      all:  apply H1 in F3 as (c & F3 & F3').
      all:  apply H1 in F4 as (d & F4 & F4').
      all:  apply H1 in F5 as (e & F5 & F5').
      all:  apply H1 in F6 as (f & F6 & F6'). 
      all: exists (Build_evalEnv a b c d e f); split; 
        [unfold isFlatEnvOf; split; [ | split; [ | split; [ | split; [ | split]]]]; cbn; auto
         | apply makeAllEnv_correct; tauto ].
    Qed.  
 
    Definition list_isFlatWindowOf (windowFinList : list (window Gamma)) (windowFlatList : list (window nat)) :=
      (forall w, w el windowFlatList -> exists w', isFlatWindowOf flatGamma w w' /\ w' el windowFinList) /\ (forall w', w' el windowFinList -> exists w, isFlatWindowOf flatGamma w w' /\ w el windowFlatList). 

    Lemma makeRules'_isFlatWindowOf (envFinList : list (evalEnv polarity states Sigma)) (envFlatList : list (evalEnv nat nat nat)) rule :
      list_isFlatEnvOf envFinList envFlatList ->
      list_isFlatWindowOf (makeRules' reifyGammaFin envFinList rule) (makeRules' reifyGammaFlat envFlatList rule).
    Proof. 
      intros. split. 
      + intros. unfold makeRules' in *. apply in_map_iff in H0 as (env & <- & H0). 
        apply H in H0 as (env' & H1 & H2). exists (reifyWindow (reifyGammaFin env') rule). 
        split. 
        - now apply reifyWindow_Gamma_isFlatWindowOf. 
        - apply in_map_iff. exists env'. split; auto. 
     + intros. unfold makeRules' in *. apply in_map_iff in H0 as (env & <- & H0). 
        apply H in H0 as (env' & H1 & H2). exists (reifyWindow (reifyGammaFlat env') rule). 
        split. 
        - now apply reifyWindow_Gamma_isFlatWindowOf. 
        - apply in_map_iff. exists env'. split; auto.
     Qed. 

    Lemma makeRules_isFlatWindowOf (Afin : list polarity) (Bfin : list states) (Cfin : list Sigma) (Aflat Bflat Cflat : list nat) rules :
      list_finReprEl flatPolarity Afin Aflat -> list_finReprEl flatstates Bfin Bflat -> list_finReprEl flatSigma Cfin Cflat ->
      list_isFlatWindowOf (makeRulesFin Afin Bfin Cfin rules) (makeRulesFlat Aflat Bflat Cflat rules).
    Proof. 
      intros. split. 
      all: repeat setoid_rewrite in_concat_iff; repeat setoid_rewrite in_map_iff.
      all: intros w (lrules & H2 & (rule & <- & H4)). 
      all: eapply makeRules'_isFlatWindowOf in H2; [ | eapply makeEnv_isFlatEnvOf; eauto ].
      all: destruct H2 as (w' & H2 & H3); eauto 10. 
    Qed. 

    Lemma nth_error_nth (X : Type) x (l : list X) n : nth_error l n = Some x -> nth n l x = x.  
    Proof. 
      revert n; induction l; intros; cbn. 
      - now destruct n. 
      - destruct n; cbn in H.
        * congruence. 
        * now apply IHl. 
    Qed. 

    Lemma finType_elem_dupfree (t : finType) : Dupfree.dupfree (elem t). 
    Proof. 
      apply dupfree_countOne. destruct t. destruct class. cbn. intros x; specialize (enum_ok x) as H2. lia.
    Qed. 

    Lemma finType_enum_list_finReprEl (t : finType) : list_finReprEl (length (elem t)) (elem t) (seq 0 (length (elem t))). 
    Proof. 
      unfold list_finReprEl. split.
      - intros. apply in_seq in H. destruct (nth_error (elem t) n ) eqn:H1.  
        + exists e. split; [ | now apply nth_error_In in H1 ].
          split; [ | split].
          * easy. 
          * easy. 
          * apply nth_error_nth in H1. rewrite <- H1. apply getPosition_nth. 2: easy.
            apply finType_elem_dupfree.   
       + destruct H. cbn in H0. apply nth_error_Some in H0. congruence. 
      - intros. exists (getPosition (elem t) a). apply In_nth with (d := a) in H as (n & H1 & <-). split.
        + split; [ | split]. 
          * easy. 
          * rewrite getPosition_nth; auto. apply finType_elem_dupfree. 
          * reflexivity.
        + rewrite getPosition_nth; [ | | assumption].
          * apply in_seq.  lia. 
          * apply finType_elem_dupfree. 
    Qed. 

    (*next steps: validity of rewrites transfers *)
    (*for that: use list_finReprEl to define relation between configuration strings  *)
    (*show that on related strings, the rewrites predicate rewritesHead_pred agrees *)
    Definition reprStringFin (X : finType) (x : nat) (s : list X) (s' : list nat) := s' = map index s. 

    Lemma isFlatWindowOf_map_index (X : finType) (x : nat) (win : window X) (win' : window nat) :
      isFlatWindowOf x win' win -> (prem win' : list nat) = map index (prem win) /\ (conc win' : list nat) = map index (conc win). 
    Proof. 
      intros ((H1 & H2 & H3) & (F1 & F2 & F3)). 
      destruct win. destruct prem, conc. cbn in *. 
      cbn [TCSR.winEl1 TCSR.winEl2 TCSR.winEl3] in *.
      repeat match goal with
             | [H : finReprEl _ _ _ |- _] => rewrite (proj2 (proj2 H)); clear H
      end. 
      destruct win', prem, conc. now cbn. 
    Qed. 


    Lemma index_injective (X : finType) : injective (@index X). 
    Proof. 
      unfold injective. intros a b H. unfold index in H.
      specialize (getPosition_correct a (elem X)) as H1.  
      specialize (getPosition_correct b (elem X)) as H2. 
      destruct Dec. 2: { now specialize (elem_spec a) as H3. }
      destruct Dec. 2: { now specialize (elem_spec b) as H3. }
      rewrite H in H1. rewrite <- (H1 b). 
      eapply H2. 
    Qed. 

    
    Lemma rewritesHead_pred_flat_agree rulesFin rulesFlat finStr finStr' flatStr flatStr' :
      reprStringFin flatGamma finStr flatStr
      -> reprStringFin flatGamma finStr' flatStr'
      -> list_isFlatWindowOf rulesFin rulesFlat 
      -> (rewritesHead_pred rulesFin finStr finStr' <-> rewritesHead_pred rulesFlat flatStr flatStr'). 
    Proof. 
      intros. unfold rewritesHead_pred. split; intros (rule & H2 & H3).
      - apply H1 in H2 as (rule' & F1 & F2). exists rule'. split; [apply F2 | ]. 
        unfold rewritesHead, prefix in *. destruct H3 as ((b1 & ->) & (b2 & ->)). 
        unfold reprStringFin in H, H0.
        rewrite map_app in H, H0. split.
        + exists (map index b1). rewrite H. enough (map index (prem rule) = prem rule') as H2.
          { now setoid_rewrite H2. }
          destruct rule; cbn. destruct prem. 
          apply isFlatWindowOf_map_index in F1. 
          rewrite (proj1 F1). now cbn. 
        + exists (map index b2). rewrite H0. enough (map index (conc rule) = conc rule') as H2. 
          { now setoid_rewrite H2. }
          destruct rule; cbn. destruct conc.
          apply isFlatWindowOf_map_index in F1.
          rewrite (proj2 F1). now cbn. 
     - apply H1 in H2 as (rule' & F1 & F2). exists rule'. split; [ apply F2 | ].
       unfold rewritesHead, prefix in *. destruct H3 as ((b1 & ->) & (b2 & ->)).
       unfold reprStringFin in H, H0. split.
       + symmetry in H. apply map_eq_app in H as (finStr1  & finStr2 & -> & ? & ?). 
         exists finStr2.
         enough (finStr1 = prem rule') as H3 by (now setoid_rewrite H3).
         apply isFlatWindowOf_map_index in F1. destruct F1 as (F1 & _).  rewrite F1 in H. 
         apply Prelim.map_inj in H; [easy | apply index_injective]. 
       + symmetry in H0. apply map_eq_app in H0 as (finStr1  & finStr2 & -> & ? & ?). 
         exists finStr2.
         enough (finStr1 = conc rule') as H3 by (now setoid_rewrite H3).
         apply isFlatWindowOf_map_index in F1. destruct F1 as (_ & F1). rewrite F1 in H0. 
         apply Prelim.map_inj in H0; [easy | apply index_injective].
    Qed. 

    Lemma valid_flat_agree rulesFin rulesFlat finStr finStr' flatStr flatStr' :
      reprStringFin flatGamma finStr flatStr
      -> reprStringFin flatGamma finStr' flatStr'
      -> list_isFlatWindowOf rulesFin rulesFlat 
      -> valid (rewritesHead_pred rulesFin) finStr finStr' <-> valid (rewritesHead_pred rulesFlat) flatStr flatStr'. 
    Proof.
      intros. 
      split.
      - intros H2. revert flatStr flatStr' H0 H. induction H2; intros.
        + rewrite H, H0; cbn; constructor 1.  
        + rewrite H3, H0. cbn [map]. constructor.
          * now eapply IHvalid.
          * rewrite map_length. auto.
        + rewrite H3, H0. cbn [map]. constructor 3. 
          * now eapply IHvalid.
          * eapply rewritesHead_pred_flat_agree.
            -- rewrite <- H3. apply H3. 
            -- rewrite <- H0. apply H0. 
            -- apply H1. 
            -- apply H. 
      - intros H2. revert finStr finStr' H0 H. induction H2; intros. 
        + destruct finStr; [ | now unfold reprStringFin in H].
          destruct finStr'; [ | now unfold reprStringFin in H0].
          constructor. 
        + unfold reprStringFin in H0, H3. 
          destruct finStr; cbn [map] in H3; [ congruence | ].
          destruct finStr'; cbn [map] in H0; [congruence | ]. 
          inv H0; inv H3. constructor 2. 
          2: now rewrite map_length in H. 
          apply IHvalid; easy. 
        + unfold reprStringFin in H0, H3.
          destruct finStr; cbn [map] in H3; [ congruence | ].
          destruct finStr'; cbn [map] in H0; [congruence | ]. 
          inv H0; inv H3. constructor 3. 
          * eapply IHvalid; easy.
          * eapply rewritesHead_pred_flat_agree. 
            4: apply H.
            -- easy.
            -- easy. 
            -- apply H1. 
    Qed. 


    Require Import PslBase.FiniteTypes.FinTypes.
    Definition mtrRules : list (window fGamma):=
      [ {inr (inr (Some (psConsV Sig1))), inr (inr (Some (psConsV Sig2))), inr (inr (Some (psConsV Sig3)))}/ {inr (inr (Some (psConsC positive Sig4))), inr (inr (Some (psConsC positive Sig1))), inr (inr (Some (psConsC positive Sig2)))};
          {inr (inr |_|), inr (inr |_|), inr (inr |_|)}/{inr (inr (Some (psConsC positive Sig1))), inr (inr |_|), inr (inr |_|)};
          {inr (inr (Some (psConsV Sig1))), inr (inr |_|), inr (inr |_|)}/{inr (inr (Some (psConsC positive Sig2))), inr (inr (Some (psConsC positive Sig1))), inr (inr |_|)};
          {inr (inr (Some (psConsV Sig1))), inr (inr (Some (psConsV Sig2))), inr (inr |_|)}/{inr (inr (Some (psConsC positive Sig3))), inr (inr (Some (psConsC positive Sig1))), inr (inr (Some (psConsC positive Sig2)))}
      ].

    Definition finMTRRules := makeRulesFin (elem Fpolarity) (elem states) (elem Sigma) mtrRules. 

    Ltac destruct_or H := match type of H with
                          | ?a \/ ?b => destruct H as [H | H]; try destruct_or H
                            end. 

    Lemma makeAllEnv_finType (A B C : finType) env : env el makeAllEnv (elem A) (elem B) (elem C). 
    Proof. 
      destruct env. apply makeAllEnv_correct. repeat split. 
      all: apply elem_spec. 
    Qed. 

  Ltac rewHeadTape_inv2 := repeat match goal with
                                  | [H : rewHeadTape _ _ |- _] => inv H
                                  | [H : shiftRightWindow _ _ _ _ _ _ |- _ ] => inv H
                                  | [H : identityWindow _ _ _ _ _ _ |- _] => inv H
                                  | [d : delim |- _] => destruct d
                                  | [H : |_| = # ?σ |- _] => is_var σ; destruct σ; cbn in H; try congruence
                                  | [H : # ?σ = |_| |- _] => is_var σ; destruct σ; cbn in H; try congruence
                                  | [H : Some (_, _) = % ?e |- _] => symmetry in H; apply polarityFlipTapeSigmaInv1 in H; rewrite H in *; clear H
                                  | [H : % ?e = Some (_, _) |- _] => apply polarityFlipTapeSigmaInv1 in H; rewrite H in *; clear H
                                  | [H : Some (_, _) = # ?e |- _] => symmetry in H; apply polarityFlipTapeSigma'Inv1 in H; rewrite H in *; clear H
                                  | [H : # ?e = Some (_, _) |- _] => apply polarityFlipTapeSigma'Inv1 in H; rewrite H in *; clear H
                                  | [H : inr _ = (~ _) |- _] => symmetry in H
                                  | [H : (~ ?a) = inr (inr |_|) |- _] => is_var a; destruct a; cbn in H; [ congruence | ]
                                  | [H : (~?e) = inr (inr (Some (_, _))) |- _] => apply polarityFlipGammaInv1 in H; try rewrite H in *; clear H
                                  | [H : inr (inr (Some (_, _))) = (~?e) |- _] => symmetry in H; apply polarityFlipGammaInv1 in H; try rewrite H in *; clear H
                                  | [H : % ?a = inr |_| |- _] => is_var a; destruct a; cbn in H; try congruence 
                                  | [H : $ = $ |- _] => clear H
                                  | [H : inr _ = inr _ |- _] => inv H
                                  | [H : inl _ = inl _ |- _] => inv H
                                  | [H : |_| = |_| |- _] => clear H
                                  | [ |- context [inr (inr (# ?e))]] => rewrite polarityFlip_push_in
                           end; try congruence. 
 

    Lemma agreement a b : rewHeadTape a b <-> rewritesHead_pred finMTRRules a b.  
    Proof. 
      split. 
      - intros.
        rewHeadTape_inv2;match goal with
            [ |- rewritesHead_pred _ (?a :: ?b :: ?c :: _) (?d :: ?e :: ?f :: _)] => exists ({a, b, c} /{d, e, f})
          end.
        + split. 
          2: split; unfold prefix; cbn; eauto. 

          unfold finMTRRules. unfold makeRulesFin. unfold makeRules, mtrRules. cbn [map concat]. 
            rewrite !in_app_iff.
            unfold makeRules'. rewrite !in_map_iff.
            left. exists (Build_evalEnv (polarityFlip p) (defstate) )
            evar (env : evalEnv polarity states Sigma). exists env. split; [ | apply makeAllEnv_finType]. cbn. subst env. reflexivity.
            subst rule. reflexivity. 
          * 
            

        rewHeadTape_inv2.
      - intros. unfold rewritesHead_pred in H. destruct H as (rule & H1 & H2). 
        unfold finMTRRules in H1. unfold makeRulesFin in H1. unfold makeRules in H1. unfold mtrRules in H1.  cbn [map concat] in H1. 
        repeat rewrite in_app_iff in H1. unfold makeRules' in H1. rename H1 into H. destruct_or H. 5: destruct H. 
        all : apply in_map_iff in H as (env & <- & _); cbn in H2; destruct H2 as (H1 & H2); cbn in *; destruct H1 as (? & ->); destruct H2 as (? & ->); cbn; eauto. 



End stringbased.
