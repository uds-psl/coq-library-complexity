From PslBase Require Import Base. 
From PslBase Require Import Vectors.Vectors. 
From Undecidability.L.Complexity.Cook Require Import Prelim UniformHomomorphisms BinaryPR FlatPR PR_to_BinaryPR. 
Require Import Lia.

(*we basically reduce to PR and use the established reduction PR -> BinaryPR *)
Section fixInstanceA. 
  Variable (fpr : FlatPR). 

  Notation Sigma := (Sigma fpr).
  Notation offset := (offset fpr).
  Notation width := (width fpr).
  Notation init := (init fpr).
  Notation windows := (windows fpr).
  Notation final := (final fpr).
  Notation steps := (steps fpr). 

  (*we first do the reduction for wellformed instances, satisfying the syntactic requirements *)
  Context (A : FlatPR_wellformed fpr). 
  Context (B : isValidFlattening fpr). 
  Context (A1 : Sigma > 0). (*instances without this property are trivial no instances *)

  (*we use the hNat homomorphism from the PR reduction *)
  Definition hflat := canonicalHom (hNat Sigma).

  Definition hoffset := Sigma * offset. 
  Definition hwidth := Sigma * width. 
  Definition hinit := hflat init.
  Definition hwindow win := match win with Build_PRWin prem conc => Build_PRWin (hflat prem) (hflat conc) end.
  Definition hwindows := map hwindow windows. 
  Definition hfinal := map hflat final. 
  Definition hsteps := steps. 

  Definition hBinaryPR := @BinaryPR.Build_BinaryPR hoffset hwidth hinit hwindows hfinal hsteps. 

  (*We show that if fpr is the flattening of a PR instance pr, then the produced BinaryPR instances are equivalent *)
  (*up to reordering of windows and final strings *)

  Variable (pr : PR). 
  Variable (isFlattening : isFlatPROf fpr pr). 

  Definition finhBinaryPR := PR_to_BinaryPR.hBinaryPR pr.

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


Definition trivialNoInstance := Build_BinaryPR 0 0 [] [] [] 0. 
Lemma trivialNoInstance_isNoInstance : not (BinaryPRLang trivialNoInstance). 
Proof. 
  intros (H & _). destruct H as (H & _). cbn in H. lia. 
Qed. 

Definition reduction (fpr : FlatPR) := if FlatPR_wf_dec fpr && isValidFlattening_dec fpr then hBinaryPR fpr else trivialNoInstance. 

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

(*Section fixInstance. *)
  (*Variable (fpr : FlatPR). *)

  (*Notation Sigma := (Sigma fpr).*)
  (*Notation offset := (offset fpr).*)
  (*Notation width := (width fpr).*)
  (*Notation init := (init fpr).*)
  (*Notation windows := (windows fpr).*)
  (*Notation final := (final fpr).*)
  (*Notation steps := (steps fpr). *)

  (*[>we first do the reduction for wellformed instances, satisfying the syntactic requirements <]*)
  (*Context (A : FlatPR_wellformed fpr). *)
  (*Context (B : isValidFlattening fpr). *)
  (*Context (A1 : Sigma > 0). [>instances without this property are trivial no instances <]*)
  
  (*Definition h' (x : nat) := if leb (S x) Sigma then repEl x false ++ [true] ++ repEl (Sigma - x -1) false*)
                                                (*else repEl Sigma false. *)

  (*Lemma h'_length (x : nat) : |h' x| = Sigma. *)
  (*Proof. *)
    (*unfold h'. destruct leb eqn:H. *)
    (*- rewrite !app_length, !repEl_length. apply leb_complete in H. cbn. nia. *)
    (*- now rewrite repEl_length.*)
  (*Qed. *)

  (*Lemma repEl_app_inv (X : Type) (a : X) s1 s2 n : repEl n a = s1 ++ s2 -> exists n1 n2, s1 = repEl n1 a /\ s2 = repEl n2 a /\ n1 + n2 = n. *)
  (*Proof. *)
    (*revert s1 s2.  induction n. *)
    (*- cbn. destruct s1, s2; cbn; try congruence. intros _. exists 0, 0; now cbn.  *)
    (*- cbn. destruct s1. *)
      (*+ cbn. destruct s2; cbn; [ congruence | ]. *)
        (*intros H. inv H. exists 0, (S n); now cbn. *)
      (*+ intros. cbn in H. inv H. apply IHn in H2 as (n1 & n2 & -> & -> & <-). *)
        (*exists (S n1), n2; now cbn. *)
  (*Qed. *)

  (*Lemma h'_inv1 (x n : nat) : h' x = repEl n false ++ [true] ++ repEl (Sigma - n -1) false -> x = n. *)
  (*Proof. *)
    (*intros. unfold h' in H. *)
    (*destruct leb eqn:H1. *)
    (*- clear H1. revert H.  generalize (Sigma - x- 1). generalize (Sigma - n -1). *)
      (*revert n. induction x; intros. *)
      (*+ destruct n; cbn in H; [reflexivity | congruence]. *)
      (*+ destruct n; cbn in H; [ congruence | ]. inv H. now apply IHx in H1.*)
    (*- destruct (le_lt_dec n Sigma). *)
      (*+ assert (|repEl n false| <= |repEl Sigma false|) by (now rewrite !repEl_length). *)
        (*apply list_length_split1 in H0 as (s1 & s2 & H0 & _ & H2). rewrite H2 in H. *)
        (*apply app_eq_length in H as (_ & H); [ | apply H0]. *)
        (*apply repEl_app_inv in H2 as (n1 & n2 & -> & -> & H2).   *)
        (*destruct n2; cbn in H; congruence. *)
      (*+ match type of H with ?a = ?b => assert (|a| = |b|) by congruence end. *)
        (*rewrite !app_length, !repEl_length in H0. cbn in H0. lia. *)
  (*Qed. *)

  (*Definition h (x : list nat) := concat (map h' x). *)

  (*Lemma h_uniform_homomorphism : uniform_homomorphism h. *)
  (*Proof. *)
    (*split; [ | split].*)
    (*+ unfold homomorphism. intros. unfold h. now rewrite map_app, concat_app. *)
    (*+ intros. unfold h. cbn. rewrite !app_nil_r. now rewrite !h'_length. *)
    (*+ intros. cbn. rewrite app_length, h'_length. cbn. lia. *)
  (*Qed. *)

  (*Lemma h_bounded_injective : bounded_injectivity Sigma (hsingle h). *)
  (*Proof. *)
    (*unfold bounded_injectivity. intros. *)
    (*unfold hsingle in H0. cbn in H0. rewrite !app_nil_r in H0. *)
    (*symmetry in H0. unfold h' in H0. erewrite (leb_correct (S n1)) in H0.  *)
    (*- now apply h'_inv1 in H0. *)
    (*- lia. *)
  (*Qed. *)

  (*[>we now get the reduction for the case that the instance we reduce from is wellformed <]*)
  (*Lemma reduction_wf : FlatPRLang fpr <-> BinaryPRLang (hBinaryPR h fpr). *)
  (*Proof. *)
    (*specialize (h_bounded_injective) as F1. *)
    (*specialize (h_uniform_homomorphism) as F2. *)
    (*split; intros. *)
    (*- destruct H as (_ & sf & H1 & H2 & H3).*)
      (*split; [ apply FlatPR_homomorphism_wf; auto | ]. *)
      (*apply FlatPR_homomorphism_iff; eauto. *)
    (*- destruct H as (H0 & H1).*)
      (*split; [ apply A | split; [apply B | ]]. *)
      (*apply FlatPR_homomorphism_iff in H1; eauto. *)
  (*Qed. *)
(*End fixInstance. *)


(*Definition trivialNoInstance := Build_BinaryPR 0 0 [] [] [] 0. *)
(*Lemma trivialNoInstance_isNoInstance : not (BinaryPRLang trivialNoInstance). *)
(*Proof. *)
  (*intros (H & _). destruct H as (H & _). cbn in H. lia. *)
(*Qed. *)

(*Definition reduction (fpr : FlatPR) := if FlatPR_wf_dec fpr && isValidFlattening_dec fpr && leb 1 (Sigma fpr) then hBinaryPR (h fpr) fpr else trivialNoInstance. *)

(*Lemma reduction_correct (fpr : FlatPR) : FlatPRLang fpr <-> BinaryPRLang (reduction fpr).  *)
(*Proof. *)
  (*[>split; intros (H & H1). <]*)
  (*[>- unfold reduction. rewrite (proj2 (FlatPR_wf_dec_correct _) H). <]*)
    (*[>destruct (lt_dec 0 (Sigma fpr)). <]*)
    (*[>+ <]*)
    (*[>apply reduction_wf. <]*)
(*Admitted. *)
