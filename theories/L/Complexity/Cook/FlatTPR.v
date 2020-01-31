From Undecidability.L.Complexity.Cook Require Import Prelim FlatPR FlatFinTypes. 
From Undecidability.L.Complexity.Cook Require Export TPR.
From PslBase Require Import Base FinTypes. 
Require Import Lia.

(**Flat 3-Parallel Rewriting *)

Record FlatTPR := {
  Sigma : nat;
  init : list nat;
  windows : list (TPRWin nat);
  final : list (list nat);
  steps : nat
  }.

Definition TPRWinP_ofFlatType (winp : TPRWinP nat) (k : nat) := winEl1 winp < k /\ winEl2 winp < k /\ winEl3 winp < k.
Definition TPRWin_ofFlatType (win : TPRWin nat) (k : nat) := TPRWinP_ofFlatType (prem win) k /\ TPRWinP_ofFlatType (conc win) k. 

Definition isValidFlatWindows (l : list (TPRWin nat)) k := (forall win, win el l -> TPRWin_ofFlatType win k).
Definition isValidFlatFinal (l : list (list nat)) k := (forall s, s el l -> list_ofFlatType k s).
Definition isValidFlatInitial (l : list nat) k := list_ofFlatType k l.

(*well-formedness is defined similarly to TPR *)
Definition FlatTPR_wellformed ftpr := length (init ftpr) >= 3.

Definition isValidFlattening ftpr :=
  isValidFlatInitial (init ftpr) (Sigma ftpr)
  /\ isValidFlatFinal (final ftpr) (Sigma ftpr)
  /\ isValidFlatWindows (windows ftpr) (Sigma ftpr). 

Definition FlatTPRLang (C : FlatTPR) :=
  FlatTPR_wellformed C /\ isValidFlattening C
  /\ exists (sf : list nat), list_ofFlatType  (Sigma C) sf
                     /\ relpower (valid (rewritesHeadList (windows C))) (steps C) (init C) sf
                     /\ satFinal (final C) sf.

(** We can define a relation to TPR instances such that TPR instances and FlatTPR instances are equivalent *)
Inductive isFlatTPRWinPOf (X : finType) (flatwinp : TPRWinP nat) (winp : TPRWinP X) := 
  mkIsFlatTPRWinPOf (Helem1 : finReprEl' (winEl1 flatwinp) (winEl1 winp))
    (Helem2 : finReprEl' (winEl2 flatwinp) (winEl2 winp))
    (Helem3 : finReprEl' (winEl3 flatwinp) (winEl3 winp))
  : isFlatTPRWinPOf flatwinp winp. 

Inductive isFlatTPRWinOf (X : finType) (flatwin : TPRWin nat) (win : TPRWin X) := 
  mkIsFlatTPRWinOf (Hprem : isFlatTPRWinPOf (prem flatwin) (prem win)) 
    (Hconc : isFlatTPRWinPOf (conc flatwin) (conc win))
  : isFlatTPRWinOf flatwin win. 

Inductive isFlatTWindowsOf (X : finType) (flatwindows : list (TPRWin nat)) (windows : list (TPRWin X)) := 
  mkIsFlatWindowsOf (Hsound : forall flatwin, flatwin el flatwindows -> exists win, win el windows /\ isFlatTPRWinOf flatwin win)
    (Hcomplete : forall win, win el windows -> exists flatwin, flatwin el flatwindows /\ isFlatTPRWinOf flatwin win)
  : isFlatTWindowsOf flatwindows windows. 

Inductive isFlatTPROf (fpr : FlatTPR) (pr : TPR) := 
  mkIsFlatTPROf (HSigma : finRepr (TPR.Sigma pr) (Sigma fpr))
    (HInit : isFlatListOf (init fpr) (TPR.init pr))
    (HWindows : isFlatTWindowsOf (windows fpr) (TPR.windows pr))
    (HFinal : isFlatFinalOf (final fpr) (TPR.final pr))
    (Hsteps : steps fpr = TPR.steps pr)
  : isFlatTPROf fpr pr.

(*proof of agreement *)
Lemma isFlatTPRWinOf_map_index (X : finType) (win : TPRWin X) win' :
  isFlatTPRWinOf win' win -> (prem win' : list nat) = map index (prem win) /\ (conc win' : list nat) = map index (conc win). 
Proof. 
  intros ([H1 H2 H3] & [F1 F2 F3]). 
  destruct win. destruct prem, conc. cbn in *. 
  repeat match goal with
          | [H : finReprEl' _ _ |- _] => unfold finReprEl' in H; rewrite H; clear H
  end. 
  destruct win', prem, conc. now cbn. 
Qed. 

Lemma rewritesHeadList_flat_agree (X : finType) (windowsFin : list (TPRWin X)) windowsFlat finStr finStr' flatStr flatStr' :
  isFlatListOf flatStr finStr
  -> isFlatListOf flatStr' finStr'
  -> isFlatTWindowsOf windowsFlat windowsFin 
  -> (rewritesHeadList windowsFin finStr finStr' <-> rewritesHeadList windowsFlat flatStr flatStr'). 
Proof. 
  intros. unfold rewritesHeadList. split; intros (win & H2 & H3).
  - apply H1 in H2 as (win' & F1 & F2). exists win'. split; [apply F1 | ]. 
    unfold rewritesHead, prefix in *. destruct H3 as ((b1 & ->) & (b2 & ->)). 
    unfold isFlatListOf in H, H0.
    rewrite map_app in H, H0. split.
    + exists (map index b1). rewrite H. enough (map index (prem win) = prem win') as H2.
      { now setoid_rewrite H2. }
      destruct win; cbn. destruct prem. 
      apply isFlatTPRWinOf_map_index in F2. 
      rewrite (proj1 F2). now cbn. 
    + exists (map index b2). rewrite H0. enough (map index (conc win) = conc win') as H2. 
      { now setoid_rewrite H2. }
      destruct win; cbn. destruct conc.
      apply isFlatTPRWinOf_map_index in F2.
      rewrite (proj2 F2). now cbn. 
  - apply H1 in H2 as (win' & F1 & F2). exists win'. split; [ apply F1 | ].
    unfold rewritesHead, prefix in *. destruct H3 as ((b1 & ->) & (b2 & ->)).
    unfold isFlatListOf in H, H0. split.
    + symmetry in H. apply map_eq_app in H as (finStr1  & finStr2 & -> & ? & ?). 
      exists finStr2.
      enough (finStr1 = prem win') as H3 by (now setoid_rewrite H3).
      apply isFlatTPRWinOf_map_index in F2. destruct F2 as (F2 & _). rewrite F2 in H. 
      apply map_injective in H; [easy | unfold injective; apply injective_index]. 
    + symmetry in H0. apply map_eq_app in H0 as (finStr1  & finStr2 & -> & ? & ?). 
      exists finStr2.
      enough (finStr1 = conc win') as H3 by (now setoid_rewrite H3).
      apply isFlatTPRWinOf_map_index in F2. destruct F2 as (_ & F2). rewrite F2 in H0. 
      apply Prelim.map_inj in H0; [easy | unfold injective; apply injective_index].
Qed.

Lemma valid_flat_agree (X : finType) (windows : list (TPRWin X)) fwindows s1 s2 fs1 fs2: 
  isFlatListOf fs1 s1 
  -> isFlatListOf fs2 s2
  -> isFlatTWindowsOf fwindows windows 
  -> valid (rewritesHeadList fwindows) fs1 fs2 <-> valid (rewritesHeadList windows) s1 s2. 
Proof. 
  intros H H1 H2. 
  split.
  - intros H3. revert s1 s2 H H1. induction H3; intros. 
    + destruct s1; [ | now unfold isFlatListOf in H]. 
      destruct s2; [ | now unfold isFlatListOf in H1].
      constructor. 
    + unfold isFlatListOf in H0, H1. 
      destruct s1; cbn [map] in H0; [ congruence | ].
      destruct s2; cbn [map] in H1; [congruence | ]. 
      inv H0; inv H1. constructor 2. 
      2: now rewrite map_length in H. 
      apply IHvalid; easy. 
    + unfold isFlatListOf in H0, H1.
      destruct s1; cbn [map] in H0; [ congruence | ].
      destruct s2; cbn [map] in H1; [congruence | ]. 
      inv H0; inv H1. constructor 3. 
      * eapply IHvalid; easy.
      * eapply rewritesHeadList_flat_agree. 
        4: apply H.
        -- easy.
        -- easy. 
        -- apply H2. 
  - intros H3. revert fs1 fs2 H H1 H2. induction H3; intros.
    + rewrite H, H1; cbn; constructor 1.  
    + rewrite H1, H0. cbn [map]. constructor.
      * now eapply IHvalid.
      * rewrite map_length. auto.
    + rewrite H1, H0. cbn [map]. constructor 3. 
      * now eapply IHvalid.
      * eapply rewritesHeadList_flat_agree in H.
        -- apply H. 
        -- rewrite <- H0. apply H0. 
        -- rewrite <- H1. apply H1. 
        -- apply H2. 
Qed. 

Lemma valid_flat_isFlatListOf_invariant (X : finType) (windows : list (TPRWin X)) fwindows (s1 : list X) fs1 fs2: 
  isFlatTWindowsOf fwindows windows 
  -> isFlatListOf fs1 s1
  -> |fs1| >= 3
  -> valid (rewritesHeadList fwindows) fs1 fs2
  -> exists (s2 : list X), isFlatListOf fs2 s2. 
Proof. 
  intros. revert s1 H0. induction H2; intros.
  - cbn in H1; lia.
  - cbn in H1; lia. 
  - cbn in H1. destruct s1; [unfold isFlatListOf in H3; cbn in H3; congruence | ].  
    apply isFlatListOf_cons in H3 as (H3' & H3). 
    destruct H0 as (win & (H0 & (_ & (c & H4)))). 
    destruct (le_lt_dec 3 (|a|)). 
    + eapply IHvalid in l as (s2 & H5); [ | apply H3]. clear IHvalid. 
      apply H in H0 as (win' & _ & (_ & [F1 F2 F3])). destruct (conc win). cbn in *.
      inv H4. exists (TPR.winEl1 (conc win') :: s2). 
      apply isFlatListOf_cons. easy.
    + clear IHvalid. apply valid_length_inv in H2. 
      apply H in H0 as (win' & _ & (_ & [F1 F2 F3])).
      destruct conc. 
      assert (c = []) as ->. { destruct c; [ easy | ]. cbn in H4. inv H4. cbn in H2. lia. }
      cbn in H4. inv H4. 
      destruct conc; cbn in *. 
      exists [winEl0; winEl4; winEl5]. unfold isFlatListOf; cbn. 
      rewrite <- F1, <- F2, <- F3. easy.
Qed. 

Lemma relpower_valid_flat_agree (X : finType) (windows : list (TPRWin X)) fwindows s1 s2 fs1 fs2 n:
  |fs1| >= 3
  -> isFlatListOf fs1 s1
  -> isFlatListOf fs2 s2
  -> isFlatTWindowsOf fwindows windows
  -> relpower (valid (rewritesHeadList fwindows)) n fs1 fs2 <-> relpower (valid (rewritesHeadList windows)) n s1 s2.
Proof. 
  intros H0 H1 H2 H3. split.
  - intros H4. revert s1 s2 H1 H2. induction H4; intros. 
    + specialize (isFlatListOf_functional H1 H2) as ->. eauto.
    + specialize (valid_flat_isFlatListOf_invariant H3 H1 H0 H) as (s3 & H5).  
      specialize (valid_length_inv H) as H6. rewrite H6 in H0. 
      specialize (IHrelpower H0  _ _ H5 H2). 
      econstructor. 
      * apply (valid_flat_agree H1 H5 H3) in H. apply H. 
      * apply IHrelpower. 
  - intros H4. clear H0. 
    revert fs1 fs2 H1 H2. induction H4; intros. 
    + specialize (isFlatListOf_injective H1 H2) as ->. constructor. 
    + assert (isFlatListOf (map index b) b) as H0 by (unfold isFlatListOf; easy).
      specialize (IHrelpower _ _ H0 H2). 
      apply (valid_flat_agree H1 H0 H3) in H. eauto. 
Qed. 

Lemma final_flat_agree (X : finType) (F : list (list X)) (f : list (list nat)) : 
  isFlatFinalOf f F -> forall s fs, isFlatListOf fs s -> satFinal f fs <-> satFinal F s. 
Proof. 
  intros. split. 
  - intros (subs & H1 & H2). apply H in H1 as (subs' & H1 & H3). 
    exists subs'. split; [ apply H1 | ]. 
    unfold substring in *. destruct H2 as (b1 & b2 & ->). 
    unfold isFlatListOf in H0. 
    symmetry in H0. apply map_eq_app in H0 as (ls1 & ls2 & -> & -> & H0). 
    symmetry in H0. apply map_eq_app in H0 as (ls3 & ls4 &-> & ? & ->). 
    rewrite H3 in H0. apply map_injective in H0; [ | apply injective_index]. 
    rewrite H0. eauto.
  - intros (subs & H1 & H2). apply H in H1 as (subs' & H1 &H3). 
    exists subs'. split; [ apply H1 | ]. 
    unfold substring in *. destruct H2 as (b1 & b2 & ->). 
    unfold isFlatListOf in H0. 
    rewrite !map_app in H0. rewrite H0, H3. eauto.
Qed. 

Lemma isFlatTPROf_isValidFlattening (tpr : TPR) (ftpr : FlatTPR) : isFlatTPROf ftpr tpr -> isValidFlattening ftpr. 
Proof. 
  intros [H1 H2 H3 H4].
  split; [ | split]. 
  + unfold isValidFlatInitial, list_ofFlatType. rewrite H2. 
    intros a. rewrite in_map_iff. intros (a' & <- & F1).
    unfold ofFlatType. rewrite H1. apply index_le. 
  + intros s H0%H4. destruct H0 as (s' & F1 & ->).
    intros a. rewrite in_map_iff. intros (a' & <- & F3). 
    rewrite H1. apply index_le. 
  + intros win H0%H3. destruct H0 as (win' & F1 & F2). 
    destruct F2 as ([F2 F3 F4] & [F5 F6 F7]).
    repeat split; rewrite H1; unfold finReprEl' in *;
    repeat match goal with [H : index _ = _ |- _] => try rewrite <- H; clear H end;
    apply index_le.  
Qed.

Lemma isFlatTPROf_wf_equivalent (tpr : TPR) (ftpr : FlatTPR) : 
  isFlatTPROf ftpr tpr -> (FlatTPR_wellformed ftpr <-> TPR_wellformed tpr). 
Proof. 
  intros [H1 H2 H3 H4]. split; intros; unfold FlatTPR_wellformed, TPR_wellformed in *.
  - rewrite H2 in H. now rewrite map_length in H.  
  - rewrite H2. rewrite map_length; apply H. 
Qed. 

Lemma isFlatTPROf_equivalence (tpr : TPR) (ftpr : FlatTPR) : 
  isFlatTPROf ftpr tpr -> (FlatTPRLang ftpr <-> TPRLang tpr). 
Proof. 
  intros. split. 
  - intros (H1 & H2 & H3). split; [ now eapply isFlatTPROf_wf_equivalent | ]. 
    destruct H as [F1 F2 F3 F4 F5].
    destruct H3 as (sf & H3 & H4 & H5).
    apply (finRepr_exists_list F1) in H3 as (SF & H3).
    exists SF. split. 
    + eapply relpower_valid_flat_agree; eauto. rewrite <- F5. apply H4.    
    + eapply final_flat_agree; eauto.
  - intros (H1 & H2). split; [ now eapply isFlatTPROf_wf_equivalent | ]. 
    split; [now eapply isFlatTPROf_isValidFlattening | ].
    destruct H as [F1 F2 F3 F4 F5]. 
    destruct H2 as (sf & H3 & H4). 
    exists (map index sf). repeat split. 
    + unfold list_ofFlatType, ofFlatType. 
      setoid_rewrite in_map_iff. intros a (x & <- & H). rewrite F1. apply index_le. 
    + eapply relpower_valid_flat_agree; eauto.
      * rewrite F2, map_length. apply H1. 
      * unfold isFlatListOf. reflexivity. 
      * rewrite F5. apply H3. 
    + eapply final_flat_agree; eauto. unfold isFlatListOf; reflexivity. 
Qed. 

(**from a flat instance, we can restore a canonical non-flat instance *)

Require Import PslBase.FiniteTypes.VectorFin PslBase.FiniteTypes.Cardinality. 
Lemma unflattenTPRWinP (w : TPRWinP nat) k : TPRWinP_ofFlatType w k -> sigT (fun (w' : TPRWinP (finType_CS (Fin.t k))) => isFlatTPRWinPOf w w'). 
Proof. 
  intros. destruct w. destruct H as (H1 & H2 & H3). cbn in *.
  assert (finRepr (finType_CS (Fin.t k)) k). 
  { unfold finRepr. specialize (Card_Fint k) as H4. unfold Cardinality in H4. easy. }
  eapply (finRepr_exists H) in H1 as (a1 & H1).  
  eapply (finRepr_exists H) in H2 as (a2 & H2). 
  eapply (finRepr_exists H) in H3 as (a3 & H3). 
  exists (Build_TPRWinP a1 a2 a3). repeat split; eapply finReprEl_finReprEl'; easy.
Qed. 

Lemma unflattenWindow (w : TPRWin nat) k : TPRWin_ofFlatType w k -> sigT (fun (w' : TPRWin (finType_CS (Fin.t k))) => isFlatTPRWinOf w w'). 
Proof. 
  intros. destruct w. destruct H as (H1 & H2). cbn in *.
  apply unflattenTPRWinP in H1 as (prem' & H1). 
  apply unflattenTPRWinP in H2 as (conc' & H2).
  exists (Build_TPRWin prem' conc'). split; easy.
Qed. 

Lemma unflattenWindows (l : list (TPRWin nat)) k : isValidFlatWindows l k -> sigT (fun (l' : list (TPRWin (finType_CS (Fin.t k)))) => isFlatTWindowsOf l l').  
Proof. 
  intros. unfold isValidFlatWindows in H. induction l. 
  - exists []. easy.
  - edestruct IHl as (l' & IH);[ easy | ]. specialize (H a (or_introl eq_refl)). 
    apply unflattenWindow in H as (a' & H). exists (a' :: l'). split; intros.
    + destruct H0 as [-> | H0]; [easy | ]. apply IH in H0 as (win & ? & ?); eauto.
    + destruct H0 as [-> | H0]; [ easy | ]. apply IH in H0 as (win' & ? & ?); eauto.
Qed. 

Lemma unflattenString (f : list nat) k : list_ofFlatType k f -> sigT (fun (f' : list (finType_CS (Fin.t k))) => isFlatListOf f f'). 
Proof. 
  intros H. 
  eapply finRepr_exists_list with (X := finType_CS (Fin.t k)) in H as (a' & H). 
  2: { unfold finRepr. specialize (Card_Fint k). easy. }
  eauto.
Qed. 

Lemma unflattenFinal (f : list (list nat)) k : isValidFlatFinal f k -> sigT (fun (f' : list (list (finType_CS (Fin.t k)))) => isFlatFinalOf f f'). 
Proof. 
  intros. unfold isValidFlatFinal in H. induction f; intros.
  - exists []; easy.
  - edestruct IHf as (f' & IH); [easy | ]. specialize (H a (or_introl eq_refl)). 
    apply unflattenString in H as (a' &H).
    exists (a'::f'). split; intros. 
    + destruct H0 as [-> | H0]; [easy | ]. apply IH in H0 as (? & ? & ?); eauto.
    + destruct H0 as [-> | H0]; [easy | ]. apply IH in H0 as (? & ? & ?); eauto.
Qed. 

Lemma unflattenTPR (f : FlatTPR) : isValidFlattening f -> sigT (fun (f' : TPR) => isFlatTPROf f f'). 
Proof. 
  intros (H1 & H2 & H3).
  apply unflattenWindows in H3 as (w' & H3). 
  apply unflattenFinal in H2 as (f' & H2). 
  apply unflattenString in H1 as (i' & H1). 
  exists (Build_TPR i' w' f' (steps f)). 
  constructor; eauto.
  cbn. unfold finRepr. specialize (Card_Fint (Sigma f)). easy.
Qed.
