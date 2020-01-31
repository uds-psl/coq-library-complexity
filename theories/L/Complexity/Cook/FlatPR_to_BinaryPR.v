From PslBase Require Import Base. 
From PslBase Require Import Vectors.Vectors. 
From Undecidability.L.Complexity.Cook Require Import Prelim UniformHomomorphisms BinaryPR FlatPR PR_to_BinaryPR. 
Require Import Lia.

(** Reduction of FlatPR to BinaryPR *)
(*logically, we reduce FlatPR to PR and use the reduction of PR to BinaryPR *)
(*but in order to make the reduction extractable, we give a shortcut reduction which produces instances which are the same up to syntax (like reordering)*)

Section fixInstanceA. 
  (*we first do the reduction for well-formed instances satisfying the syntactic requirements *)

  Variable (fpr : FlatPR). 

  Notation Sigma := (Sigma fpr).
  Notation offset := (offset fpr).
  Notation width := (width fpr).
  Notation init := (init fpr).
  Notation windows := (windows fpr).
  Notation final := (final fpr).
  Notation steps := (steps fpr). 

  Context (A : FlatPR_wellformed fpr). 
  Context (B : isValidFlattening fpr). 
  Context (A1 : Sigma > 0). (*instances without this property are trivial no instances *)

  (*we use the hNat base homomorphism from the PR reduction *)
  Definition hflat := canonicalHom (hNat Sigma).

  Definition hoffset := Sigma * offset. 
  Definition hwidth := Sigma * width. 
  Definition hinit := hflat init.
  Definition hwindow win := match win with Build_PRWin prem conc => Build_PRWin (hflat prem) (hflat conc) end.
  Definition hwindows := map hwindow windows. 
  Definition hfinal := map hflat final. 
  Definition hsteps := steps. 

  Definition hBinaryPR := @BinaryPR.Build_BinaryPR hoffset hwidth hinit hwindows hfinal hsteps. 

  (*We show that if fpr is the flattening of a PR instance pr, then the produced BinaryPR instances are equivalent up to reordering of windows and final strings *)

  Variable (pr : PR). 
  Variable (isFlattening : isFlatPROf fpr pr). 

  Definition finhBinaryPR := PR_to_BinaryPR.hBinaryPR pr.

  (*agreement of produced lists, windows, ... *)
  Lemma isFlatListOf_hom_agree l L : isFlatListOf l L -> hflat l = @h pr L.  
  Proof. 
    destruct isFlattening. 
    intros. rewrite H. unfold h, PR_homomorphisms.h. 
    unfold h', hflat. rewrite <- HSigma. 
    unfold canonicalHom. now rewrite map_map. 
  Qed. 

  Lemma isFlatPRWinOf_hom_agree w W : isFlatPRWinOf w W -> hwindow w = PR_homomorphisms.hwindow (@h' pr) W.
  Proof. 
    intros. destruct w, W. cbn. 
    erewrite isFlatListOf_hom_agree; [ | apply H]. 
    erewrite isFlatListOf_hom_agree; [ | apply H]. 
    easy.
  Qed. 

  Lemma isFlatWindowsOf_hom_agree: hwindows === PR_homomorphisms.hwindows (@h' pr).  
  Proof. 
    split; intros a H;
    [unfold hwindows in H | unfold PR_homomorphisms.hwindows in H]; apply in_map_iff in H as (win & <- & H); apply isFlattening in H as (win' & H & H1); 
      apply isFlatPRWinOf_hom_agree in H1; apply in_map_iff; eauto.  
  Qed. 

  Lemma isFlatFinalOf_hom_agree: hfinal === PR_homomorphisms.hfinal (@h' pr).
  Proof. 
    split; intros a H; [unfold hfinal in H | unfold PR_homomorphisms.hfinal in H]; 
    apply in_map_iff in H as (subs & <- & H); apply isFlattening in H as (subs' & H & H1);
      apply isFlatListOf_hom_agree in H1; apply in_map_iff; eauto. 
  Qed. 

  (*equivalence of well-formedness *)
  Lemma BinaryPR_instances_wf_equivalent : BinaryPR_wellformed finhBinaryPR <-> BinaryPR_wellformed hBinaryPR. 
  Proof. 
    destruct isFlattening. 
    unfold BinaryPR_wellformed. cbn. unfold PR_homomorphisms.hwidth, PR_homomorphisms.hoffset, hwidth, hoffset.  
    rewrite <- !HSigma, <- !HWidth, <- !HOffset. 
    split; intros (H1 & H2 & H3 & H4 &H5 & H6); repeat match goal with [ |- _ /\ _] => split end; try easy.
    - unfold hinit. erewrite isFlatListOf_hom_agree; [ | easy]. apply H4. 
    - intros. rewrite (isFlatWindowsOf_hom_agree) in H. easy.
    - unfold hinit. erewrite isFlatListOf_hom_agree; [ | easy]. apply H6. 
    - unfold hinit in H4. erewrite isFlatListOf_hom_agree in H4; [ | easy]. apply H4. 
    - intros. rewrite <- (isFlatWindowsOf_hom_agree) in H. easy.
    - unfold hinit in H6. erewrite isFlatListOf_hom_agree in H6; [ | easy]. apply H6. 
  Qed. 

  (*now the instances are in fact equivalent *)
  Lemma BinaryPR_instances_equivalent : BinaryPRLang finhBinaryPR <-> BinaryPRLang hBinaryPR. 
  Proof. 
    unfold BinaryPRLang. destruct isFlattening. 
    cbn. unfold PR_homomorphisms.hwidth, PR_homomorphisms.hoffset, hwidth, hoffset, PR_homomorphisms.hsteps, hsteps.  
    rewrite <- !HSigma, <- !HWidth, <- !HOffset, <- !HSteps. 
    unfold hinit, PR_homomorphisms.hinit. setoid_rewrite isFlatListOf_hom_agree; [ | easy | easy].

    split; intros (Hwf & sf & H1 & H2 );
    (split; [ apply BinaryPR_instances_wf_equivalent, Hwf| exists sf; split ]).
    - eapply relpower_congruent. 2: apply H1. intros. eapply valid_windows_equivalent. 
      apply isFlatWindowsOf_hom_agree.
    - eapply satFinal_final_equivalent. 2: apply H2. apply isFlatFinalOf_hom_agree. 
    - eapply relpower_congruent. 2: apply H1. intros. eapply valid_windows_equivalent. 
      symmetry. apply isFlatWindowsOf_hom_agree.
    - eapply satFinal_final_equivalent. 2: apply H2. symmetry. apply isFlatFinalOf_hom_agree. 
  Qed. 
End fixInstanceA.

(*as usual, instances not satisfying the syntactic requirements are just mapped to a trivial no instance *)
Definition trivialNoInstance := Build_BinaryPR 0 0 [] [] [] 0. 
Lemma trivialNoInstance_isNoInstance : not (BinaryPRLang trivialNoInstance). 
Proof. 
  intros (H & _). destruct H as (H & _). cbn in H. lia. 
Qed. 

Definition reduction (fpr : FlatPR) :=
  if FlatPR_wf_dec fpr && isValidFlattening_dec fpr then hBinaryPR fpr else trivialNoInstance.

Lemma FlatPR_to_BinaryPR (fpr : FlatPR) : FlatPRLang fpr <-> BinaryPRLang (reduction fpr).  
Proof. 
  split; intros. 
  - destruct H as (H1 & Hwf & H2). 
    unfold reduction. 
    rewrite (proj2 (FlatPR_wf_dec_correct _) H1). 
    rewrite (proj2 (isValidFlattening_dec_correct _) Hwf). 
    specialize (unflattenPR Hwf) as (pr & H3).
    eapply BinaryPR_instances_equivalent; [ apply H3 | ]. 
    apply isFlatPROf_equivalence in H3. 
    enough (PRLang pr). 
    { specialize (PR_to_BinaryPR pr) as H4. unfold PR_to_BinaryPR.reduction in H4. 
      enough (PR_wf_dec pr = true) as H5 by (rewrite H5 in H4; apply H4, H). 
      destruct H as (H & _ & _). apply PR_wf_dec_correct, H.  
    } 
    apply H3; easy.
  - unfold reduction in H. destruct (FlatPR_wf_dec) eqn:H1, (isValidFlattening_dec) eqn:H2. 
    2-4: cbn in H; now apply trivialNoInstance_isNoInstance in H.
    cbn in H. apply isValidFlattening_dec_correct in H2. apply FlatPR_wf_dec_correct in H1. 
    (*we restore an unflattened instance *)
    specialize (unflattenPR H2) as (pr & H3). eapply isFlatPROf_equivalence; [ apply H3 | ]. 
    apply PR_to_BinaryPR. unfold PR_to_BinaryPR.reduction. 
    enough (PR_wf_dec pr = true) as -> by now eapply BinaryPR_instances_equivalent. 
    eapply PR_wf_dec_correct, isFlatPROf_wf_equivalent; easy.
Qed.

