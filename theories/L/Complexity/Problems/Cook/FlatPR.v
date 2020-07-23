From PslBase Require Import Base FinTypes. 
From Undecidability Require Import L.Functions.EqBool.
From Undecidability.L.Complexity Require Export Problems.Cook.PR FlatFinTypes MorePrelim.
Require Import Lia.

(** * Flat Parallel Rewriting *)
(*A flattened version of parallel rewriting using natural numbers to represent finite types *)

Inductive FlatPR := {
  Sigma : nat;
  offset : nat;
  width : nat;
  init : list nat;
  windows : list (PRWin nat);
  final : list (list nat);
  steps : nat
  }.

(*validity of windows and final constraints relative to an alphabet *)
(*we have to enforce this as we always consider only a finite subset of N *)
Definition PRWin_ofFlatType (win : PRWin nat) k:= list_ofFlatType k (prem win) /\ list_ofFlatType k (conc win). 
Definition isValidFlatWindows (l : list (PRWin nat)) k := (forall win, win el l -> PRWin_ofFlatType win k).
Definition isValidFlatFinal (l : list (list nat)) k := (forall s, s el l -> list_ofFlatType k s).
Definition isValidFlatInitial (l : list nat) k := list_ofFlatType k l.

(*the well-formedness constraints are the same as for PR *)
Definition FlatPR_wellformed fpr := 
  width fpr > 0 
  /\ offset fpr > 0 
  /\ (exists k, k > 0 /\ width fpr = k * offset fpr)
  /\ length (init fpr) >= width fpr
  /\ (forall win, win el windows fpr -> PRWin_of_size win (width fpr)) 
  /\ (exists k, length (init fpr) = k * offset fpr). 

(*additionally, we require that instances only use the given finite subset of N *)
Definition isValidFlattening fpr := 
 list_ofFlatType (Sigma fpr) (init fpr) 
  /\ (forall s, s el final fpr -> list_ofFlatType (Sigma fpr) s)
  /\ (forall win, win el windows fpr -> PRWin_ofFlatType win (Sigma fpr)). 

(*the definitions of validity and satisfaction of final constraints can be re-used *)

(*we can now define the language of valid FlatPR instances *)
Definition FlatPRLang (C : FlatPR) := FlatPR_wellformed C /\ isValidFlattening C
  /\ exists (sf : list nat), list_ofFlatType (Sigma C) sf 
      /\ relpower (valid (offset C) (width C) (windows C)) (steps C) (init C) sf 
      /\ satFinal (offset C) (length (init C)) (final C) sf.

Section fixInstance.
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

  (*we want to prove that for syntactically well-formed instances, we can only rewrite to strings that are again strings over the finite alphabet *)
  (*we first prove a more general statement over abstract homomorph properties*)
  Lemma p_invariant (p : list nat -> Prop) (a b : list nat) : 
    p a 
    -> (forall x y, p (x ++ y) <-> p x /\ p y) 
    -> |a| >= width 
    -> (forall x y u v win, rewritesHead win (u ++ x) (v ++ y) -> win el windows -> |u| = offset -> |v| = offset -> p v)
    -> (forall win, win el windows -> p (conc win))
    -> valid offset width windows a b 
    -> p b. 
  Proof. 
    intros H H0 H1 G1 G2 H2. 
    (*we switch to the direct characterisation *)
    assert (valid offset width windows a b /\ |a| >= width) as H3%validDirect_valid by tauto. 2-4: apply A.
    clear H2 H1. induction H3. 
    - clear G1. 
      destruct A as (_ & _ & (k & _ & A2) & _ & A6 & _).  
      destruct B as ( _ & _ & A5).
      specialize (A5 _ H3) as (A5 & A7). 
      specialize H4 as ((rest' & H6') & (rest & H6)).  (*show rest = [] *)
      specialize (A6 _ H3) as (A6 & A6').
      subst. rewrite app_length in H2. 
      (*we need some structural assumptions *)
      assert (rest = []) as ->. 
      { 
        destruct rest'; cbn in H2; [ | lia]. rewrite !app_length in H1. 
        destruct rest; [ easy | cbn in H1; lia].
      }       
      rewrite app_nil_r. now apply G2.     
    - rewrite H0. apply H0 in H. split; [ | apply IHvalidDirect; easy]. now eapply G1. 
  Qed. 

  (*the statement is now a straightforward corollary *)
  Corollary valid_list_ofFlatType_invariant a b : 
    list_ofFlatType Sigma a -> |a| >= width -> valid offset width windows a b -> list_ofFlatType Sigma b. 
  Proof.
    intros H H0 H1. eapply (@p_invariant (list_ofFlatType Sigma)).
    - apply H. 
    - intros. apply list_ofFlatType_app. 
    - apply H0. 
    - intros. destruct H2 as (_ & (c & H2)). 
        destruct A as (_ & _ & A3 & _ & A1 & _ ). destruct B as ( _ & _ & A2).
        specialize (A1 _ H3) as (_ & A1). specialize (A2 _ H3) as (_ & A2). 
        apply app_length_split in H2 as (u' & H2). 
        * rewrite H2 in A2. now apply list_ofFlatType_app in A2. 
        * destruct A3 as (ak & A3 & A4). nia.  
    - intros. destruct B as (_ & _ & A1). 
      apply A1 in H2 as (_ & H2). apply H2. 
    - apply H1. 
  Qed. 

  (*of course, this transfers to an arbitrary number of rewrite steps *)
  Lemma relpower_valid_list_ofFlatType_invariant steps a b: 
    list_ofFlatType Sigma a -> |a| >= width -> relpower (valid offset width windows) steps a b -> list_ofFlatType Sigma b. 
  Proof. 
    intros. induction H1; [easy | ]. 
    apply IHrelpower. eapply valid_list_ofFlatType_invariant, H1; [ apply H | ]. 
    - apply H0.  
    - apply valid_length_inv in H1. lia. 
  Qed. 

End fixInstance.

(*deciders for isValidFlattening and well-formedness *)
Definition PRWin_ofFlatType_dec (Sigma : nat) (win : PRWin nat) := list_ofFlatType_dec Sigma (prem win) && list_ofFlatType_dec Sigma (conc win). 
Lemma PRWin_ofFlatType_dec_correct win Sigma : PRWin_ofFlatType_dec Sigma win = true <-> PRWin_ofFlatType win Sigma. 
Proof. 
  unfold PRWin_ofFlatType_dec, PRWin_ofFlatType. rewrite andb_true_iff. 
  rewrite !list_ofFlatType_dec_correct. easy. 
Qed. 

Definition FlatPR_wf_dec (fpr : FlatPR) := 
  leb 1 (width fpr) 
  && leb 1 (offset fpr)
  && Nat.eqb (Nat.modulo (width fpr) (offset fpr)) 0
  && leb (width fpr) (|init fpr|)
  && forallb (PRWin_of_size_dec (width fpr)) (windows fpr)
  && Nat.eqb (Nat.modulo (|init fpr|) (offset fpr)) 0. 
Definition isValidFlattening_dec (fpr : FlatPR) := 
  list_ofFlatType_dec (Sigma fpr) (init fpr)
  && forallb (list_ofFlatType_dec (Sigma fpr)) (final fpr)
  && forallb (PRWin_ofFlatType_dec (Sigma fpr)) (windows fpr). 

Lemma FlatPR_wf_dec_correct (fpr : FlatPR) : FlatPR_wf_dec fpr = true <-> FlatPR_wellformed fpr. 
Proof. 
  unfold FlatPR_wf_dec, FlatPR_wellformed. rewrite !andb_true_iff, !and_assoc.
  rewrite !leb_iff. rewrite <- !(reflect_iff _ _ (Nat.eqb_spec _ _ )).  
  rewrite !forallb_forall. 
  setoid_rewrite PRWin_of_size_dec_correct. 
  split; intros; repeat match goal with [H : _ /\ _ |- _] => destruct H end; 
  repeat match goal with [ |- _ /\ _ ] => split end; try easy. 
  - apply Nat.mod_divide in H1 as (k & H1); [ | lia]. 
    exists k; split; [ | apply H1 ]. destruct k; cbn in *; lia.
  - apply Nat.mod_divide in H4 as (k & H4); [ | lia].  exists k; apply H4.  
  - apply Nat.mod_divide; [ lia | ]. destruct H1 as (k & _ & H1). exists k; apply H1.
  - apply Nat.mod_divide; [ lia | ]. apply H4. 
Qed. 

Lemma isValidFlattening_dec_correct (fpr : FlatPR) : isValidFlattening_dec fpr = true <-> isValidFlattening fpr. 
Proof. 
  unfold isValidFlattening_dec, isValidFlattening.
  rewrite !andb_true_iff, !and_assoc.
  rewrite !forallb_forall. 
  setoid_rewrite PRWin_ofFlatType_dec_correct. 
  setoid_rewrite list_ofFlatType_dec_correct. 
  split; intros; repeat match goal with [H : _ /\ _ |- _] => destruct H end; 
  repeat match goal with [ |- _ /\ _ ] => split end; try easy. 
Qed. 

(*relation to PR instances *)
Inductive isFlatPRWinOf (X : finType) (flatwin : PRWin nat) (win : PRWin X) := 
  mkIsFlatPRWinO (Hprem : isFlatListOf (prem flatwin) (prem win)) 
    (Hconc : isFlatListOf (conc flatwin) (conc win))
  : isFlatPRWinOf flatwin win. 

Inductive isFlatWindowsOf (X : finType) (flatwindows : list (PRWin nat)) (windows : list (PRWin X)) := 
  mkIsFlatWindowsOf (Hsound : forall flatwin, flatwin el flatwindows -> exists win, win el windows /\ isFlatPRWinOf flatwin win)
    (Hcomplete : forall win, win el windows -> exists flatwin, flatwin el flatwindows /\ isFlatPRWinOf flatwin win)
  : isFlatWindowsOf flatwindows windows. 

Inductive isFlatFinalOf (X : finType) (flatfinal : list (list nat)) (final : list (list X)) := 
  mkIsFlatFinalOf (Hsound : forall fin, fin el flatfinal -> exists fin', fin' el final /\ isFlatListOf fin fin')
    (Hcomplete : forall fin, fin el final -> exists fin', fin' el flatfinal /\ isFlatListOf fin' fin)
  : isFlatFinalOf flatfinal final. 

Inductive isFlatPROf (fpr : FlatPR) (pr : PR) := 
  mkIsFlatPROf (HSigma : finRepr (PR.Sigma pr) (Sigma fpr))
    (HOffset : offset fpr = PR.offset pr)
    (HWidth : width fpr = PR.width pr)
    (HInit : isFlatListOf (init fpr) (PR.init pr))
    (HWindows : isFlatWindowsOf (windows fpr) (PR.windows pr))
    (HFinal : isFlatFinalOf (final fpr) (PR.final pr))
    (HSteps : steps fpr = PR.steps pr)
  : isFlatPROf fpr pr.

Lemma isFlatPROf_isValidFlattening (fpr : FlatPR) (pr : PR) : isFlatPROf fpr pr -> isValidFlattening fpr. 
Proof. 
  intros. destruct H.
  repeat split.
  - rewrite HSigma. now eapply isFlatListOf_list_ofFlatType. 
  - intros s H0%HFinal. rewrite HSigma. destruct H0 as (s' & F1 & ->). 
    eapply isFlatListOf_list_ofFlatType. unfold isFlatListOf. reflexivity. 
  - apply HWindows in H. destruct H as (win' & F1 & F2). 
    destruct F2 as (F2 & F3). rewrite HSigma. 
    eapply isFlatListOf_list_ofFlatType, F2. 
  - apply HWindows in H. destruct H as (win' & F1 & F2). 
    destruct F2 as (F2 & F3). rewrite HSigma. 
    eapply isFlatListOf_list_ofFlatType, F3. 
Qed. 

(** we show that FlatPR instances "behave in the same way" as PR instances  *)

Lemma rewritesHead_flat_agree (X : finType) (windowsFin : list (PRWin X)) windowsFlat finStr finStr' flatStr flatStr' :
  isFlatListOf flatStr finStr
  -> isFlatListOf flatStr' finStr'
  -> isFlatWindowsOf windowsFlat windowsFin 
  -> (exists win, win el windowsFin /\ rewritesHead win finStr finStr') <-> (exists win, win el windowsFlat /\ rewritesHead win flatStr flatStr'). 
Proof. 
  intros. split; intros (win & H2 & H3).
  - apply H1 in H2 as (win' & F1 & F2). exists win'. split; [apply F1 | ]. 
    unfold rewritesHead, prefix in *. destruct H3 as ((b1 & ->) & (b2 & ->)). 
    unfold isFlatListOf in H, H0.
    rewrite map_app in H, H0. split.
    + exists (map index b1). rewrite H. enough (map index (prem win) = prem win') as H2.
      { now setoid_rewrite H2. }
      destruct win; cbn.
      destruct F2. cbn in *. now rewrite Hprem.  
    + exists (map index b2). rewrite H0. enough (map index (conc win) = conc win') as H2. 
      { now setoid_rewrite H2. }
      destruct win; cbn. 
      destruct F2. cbn in *. now rewrite Hconc. 
  - apply H1 in H2 as (win' & F1 & F2). exists win'. split; [ apply F1 | ].
    unfold rewritesHead, prefix in *. destruct H3 as ((b1 & ->) & (b2 & ->)).
    unfold isFlatListOf in H, H0. split.
    + symmetry in H. apply map_eq_app in H as (finStr1  & finStr2 & -> & ? & ?). 
      exists finStr2.
      enough (finStr1 = prem win') as H3 by (now setoid_rewrite H3).
      destruct F2. rewrite Hprem in H. 
      apply map_injective in H; [easy | unfold injective; apply injective_index]. 
    + symmetry in H0. apply map_eq_app in H0 as (finStr1  & finStr2 & -> & ? & ?). 
      exists finStr2.
      enough (finStr1 = conc win') as H3 by (now setoid_rewrite H3).
      destruct F2. rewrite Hconc in H0. 
      apply Prelim.map_inj in H0; [easy | unfold injective; apply injective_index].
Qed.

Section fixFPRInstance. 
  (*for the proof, we fix an instance *)
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


  Lemma valid_flat_agree (X : finType) (fwindows : list (PRWin X)) s1 s2 fs1 fs2: 
    isFlatListOf fs1 s1 
    -> isFlatListOf fs2 s2
    -> isFlatWindowsOf windows fwindows 
    -> valid offset width windows fs1 fs2 <-> valid offset width fwindows s1 s2. 
  Proof. 
    intros H H1 H2. 
    split.
    - intros H3. revert s1 s2 H H1. induction H3; intros. 
      + destruct s1; [ | now unfold isFlatListOf in H]. 
        destruct s2; [ | now unfold isFlatListOf in H1].
        constructor. 
      + unfold isFlatListOf in H4, H5. 
        symmetry in H4. apply map_eq_app in H4 as (ls1 & ls2 & -> & -> & ->). 
        symmetry in H5. apply map_eq_app in H5 as (rs1 & rs2 & -> & -> & ->).
        constructor 2. 
        2-4: now rewrite map_length in *. 
        apply IHvalid; easy. 
      + unfold isFlatListOf in H5, H6.
        symmetry in H5. apply map_eq_app in H5 as (ls1 & ls2 & -> & -> & ->). 
        symmetry in H6. apply map_eq_app in H6 as (rs1 & rs2 & -> & -> & ->).
        assert (exists w, w el windows /\ rewritesHead w (map index ls1 ++ map index ls2) (map index rs1 ++ map index rs2)) as H5 by eauto.
        eapply rewritesHead_flat_agree in H5 as (finwin & H5 & H6). 
        * econstructor 3. 2-3: now rewrite map_length in *. 
          -- eapply IHvalid; easy.
          -- apply H5. 
          -- apply H6. 
        * clear H5 H6. apply isFlatListOf_app; easy.
        * clear H5 H6. apply isFlatListOf_app; easy.
        * clear H5 H6. apply H2. 
    - intros H3. revert fs1 fs2 H H1 H2. induction H3; intros.
      + rewrite H, H1; cbn; constructor 1.  
      + rewrite H2, H4. rewrite !map_app. constructor. 2-4: rewrite map_length; auto.
        now eapply IHvalid.
      + rewrite H4, H5. rewrite !map_app. 
        assert (exists w, w el fwindows /\ rewritesHead w (u ++ a) (v++b)) as H7 by eauto.
        eapply rewritesHead_flat_agree in H7 as (finwin & H7 & H8). 2-4: eauto.
        econstructor 3. 2-3: rewrite map_length; auto.
        * now eapply IHvalid.
        * apply H7. 
        * rewrite H4, H5 in H8. now rewrite !map_app in H8. 
  Qed. 

  (*we re-use the lemma proven above which asserts that list_ofFlatType is invariant *)
  (*for that, we need more assumptions than are required in principle, but this is okay *)
  Lemma valid_flat_isFlatListOf_invariant (X : finType) (s1 : list X) fs1 fs2: 
    finRepr X Sigma
    -> isFlatListOf fs1 s1
    -> |fs1| >= width 
    -> valid offset width windows fs1 fs2
    -> exists (s2 : list X), isFlatListOf fs2 s2. 
  Proof. 
    intros. 
    apply isFlatListOf_list_ofFlatType in H0. rewrite <- H in H0. 
    specialize (@valid_list_ofFlatType_invariant fpr A B fs1 fs2 H0 H1 H2) as H4. 
    apply (finRepr_exists_list H) in H4. destruct H4 as (s2 & H4); easy.
  Qed. 

  Lemma relpower_valid_flat_agree (X : finType) (finwindows : list (PRWin X)) s1 s2 fs1 fs2 n:
    finRepr X Sigma
    -> |fs1| >= width 
    -> isFlatListOf fs1 s1
    -> isFlatListOf fs2 s2
    -> isFlatWindowsOf windows finwindows
    -> relpower (valid offset width windows) n fs1 fs2 <-> relpower (valid offset width finwindows) n s1 s2.
  Proof. 
    intros H0 H1 H2 H3 H4. split.
    - intros H5. revert s1 s2 H2 H3. induction H5; intros. 
      + specialize (isFlatListOf_functional H2 H3) as ->. eauto.
      + specialize (valid_flat_isFlatListOf_invariant H0 H2 H1 H) as (s3 & H6).  
        specialize (valid_length_inv H) as H7. rewrite H7 in H1. 
        specialize (IHrelpower H1  _ _ H6 H3). 
        econstructor. 
        * apply (valid_flat_agree H2 H6 H4) in H. apply H. 
        * apply IHrelpower. 
    - intros H5. clear H1. 
      revert fs1 fs2 H2 H3. induction H5; intros. 
      + specialize (isFlatListOf_injective H2 H3) as ->. constructor. 
      + assert (isFlatListOf (map index b) b) as H1 by (unfold isFlatListOf; easy).
        specialize (IHrelpower _ _ H1 H3). 
        apply (valid_flat_agree H2 H1 H4) in H. eauto. 
  Qed. 

  Lemma final_flat_agree (X : finType) (F : list (list X)) (f : list (list nat)) l: 
    isFlatFinalOf f F -> forall s fs, isFlatListOf fs s -> satFinal offset l f fs <-> satFinal offset l F s. 
  Proof. 
    intros. split. 
    - intros (subs & k & H1 & H2 & H3). apply H in H1 as (subs' & H4 & H5). 
      exists subs', k. split; [ apply H4 | split; [ apply H2 | ]]. 
      unfold isFlatListOf in H0. rewrite H0 in H3. rewrite H5 in H3.  
      destruct H3 as (b & H3). rewrite <- map_skipn in H3. 
      apply map_eq_app in H3 as (ls1 & ls2 & H3 & H6 & H7). 
      rewrite H3. 
      apply map_injective in H6; [ | apply injective_index]. 
      rewrite H6. now exists ls2.
    - intros (subs & k & H1 & H2 & H3). apply H in H1 as (subs' & H4 &H5). 
      exists subs', k. split; [ apply H4 | split; [ apply H2 | ]]. 
      rewrite H5, H0. destruct H3 as (b & H3). 
      exists (map index b). rewrite <- map_skipn. rewrite H3. 
      now rewrite !map_app.
  Qed. 
End fixFPRInstance. 

(*well-formedness is equivalent, of course *)
Lemma isFlatPROf_wf_equivalent (pr : PR) (fpr : FlatPR) : 
  isFlatPROf fpr pr -> (FlatPR_wellformed fpr <-> PR_wellformed pr). 
Proof. 
  intros [H1 H2 H3 H4]. split; intros; unfold FlatPR_wellformed, PR_wellformed in *.
  - destruct H as (F1 & F2 & F3 & F4 & F5 & F6). repeat split.  
    + easy.
    + easy.
    + destruct F3 as (k & F3 & F3'). exists k. nia.
    + rewrite -> H4 in F4. rewrite map_length in F4. lia. 
    + apply HWindows in H as (flatwin & H & H5). apply F5 in H. 
      destruct H5. destruct H as (H & _). rewrite Hprem in H. rewrite map_length in H. lia.  
    + apply HWindows in H as (flatwin & H & H5). apply F5 in H. 
      destruct H5. destruct H as (_ & H). rewrite Hconc in H. rewrite map_length in H. lia.  
    + destruct F6 as (k & F6). rewrite H4 in F6. rewrite map_length in F6. exists k; nia.
  - destruct H as (F1 & F2 & F3 & F4 & F5 & F6). repeat split. 
    + easy. 
    + easy. 
    + destruct F3 as (k & F3 & F3'). exists k. nia. 
    + rewrite H4, map_length. lia.  
    + apply HWindows in H as (finwin & H & H5). apply F5 in H. 
      destruct H5. destruct H as (H & _). rewrite Hprem, map_length. lia.  
    + apply HWindows in H as (finwin & H & H5). apply F5 in H. 
      destruct H5. destruct H as (_ & H). rewrite Hconc, map_length. lia. 
    + destruct F6 as (k & F6). rewrite H4, map_length. exists k. nia. 
Qed. 

(*now we can derive equivalence of instances related via isFlatPROf *)
Lemma isFlatPROf_equivalence (pr : PR) (fpr : FlatPR) : 
  isFlatPROf fpr pr -> (FlatPRLang fpr <-> PRLang pr). 
Proof. 
  intros. split. 
  - intros (H1 & H2 & H3). split; [ now eapply isFlatPROf_wf_equivalent | ]. 
    destruct H as [F1 F2 F3 F4 F5].
    destruct H3 as (sf & H3 & H4 & H5).
    apply (finRepr_exists_list F1) in H3 as (SF & H3).
    exists SF. split. 
    + rewrite <- F2, <- F3, <- HSteps. eapply relpower_valid_flat_agree; eauto. apply H1.    
    + rewrite <- F2. rewrite F4, map_length in H5. eapply final_flat_agree; eauto.
  - intros (H1 & H2). split; [ now eapply isFlatPROf_wf_equivalent | ]. 
    split; [now eapply isFlatPROf_isValidFlattening | ].
    destruct H as [F1 F2 F3 F4 F5]. 
    destruct H2 as (sf & H3 & H4). 
    exists (map index sf). repeat split. 
    + unfold list_ofFlatType, ofFlatType. 
      setoid_rewrite in_map_iff. intros a (x & <- & H). rewrite F1. apply index_le. 
    + eapply relpower_valid_flat_agree; eauto.
      * now rewrite isFlatPROf_wf_equivalent. 
      * now eapply isFlatPROf_isValidFlattening with (pr := pr). 
      * rewrite F4, map_length, F3. apply H1. 
      * unfold isFlatListOf. reflexivity. 
      * rewrite  F2,  F3, HSteps. apply H3. 
    + eapply final_flat_agree; eauto. 
      * unfold isFlatListOf; reflexivity. 
      * rewrite F2, F4, map_length. apply H4. 
Qed. 

(*given a well-formed flat instance, we can derive a "canonical" (up to bijections of the finite type) PR instance *)
(*we use Fin.t as the canonical finite type *)

(*unflattening *)
Require Import PslBase.FiniteTypes.VectorFin PslBase.FiniteTypes.Cardinality. 
Import Coq.Init.Specif.
Lemma unflattenString (f : list nat) k : list_ofFlatType k f -> {f' : list (finType_CS (Fin.t k)) & isFlatListOf f f'}.
Proof. 
  intros H. 
  eapply finRepr_exists_list with (X := finType_CS (Fin.t k)) in H as (a' & H). 
  2: { unfold finRepr. specialize (Fin_cardinality k). unfold Cardinality. easy. }
  eauto.
Qed. 

Lemma unflattenWindow (w : PRWin nat) k : PRWin_ofFlatType w k -> {w' : PRWin (finType_CS (Fin.t k)) & isFlatPRWinOf w w'}. 
Proof. 
  intros. destruct w. destruct H as (H1 & H2). cbn in *.
  apply unflattenString in H1 as (prem' & H1). 
  apply unflattenString in H2 as (conc' & H2).
  exists (Build_PRWin prem' conc'). split; easy.
Qed. 

Lemma unflattenWindows (l : list (PRWin nat)) k : isValidFlatWindows l k -> {l' : list (PRWin (finType_CS (Fin.t k))) & isFlatWindowsOf l l'}.
Proof. 
  intros. unfold isValidFlatWindows in H. induction l. 
  - exists []. easy.
  - edestruct IHl as (l' & IH);[ easy | ]. specialize (H a (or_introl eq_refl)). 
    apply unflattenWindow in H as (a' & H). exists (a' :: l'). split; intros.
    + destruct H0 as [-> | H0]; [easy | ]. apply IH in H0 as (win & ? & ?); eauto.
    + destruct H0 as [-> | H0]; [ easy | ]. apply IH in H0 as (win' & ? & ?); eauto.
Qed. 

Lemma unflattenFinal (f : list (list nat)) k : isValidFlatFinal f k -> {f' : list (list (finType_CS (Fin.t k))) & isFlatFinalOf f f'}.
Proof. 
  intros. unfold isValidFlatFinal in H. induction f; intros.
  - exists []; easy.
  - edestruct IHf as (f' & IH); [easy | ]. specialize (H a (or_introl eq_refl)). 
    apply unflattenString in H as (a' &H).
    exists (a'::f'). split; intros. 
    + destruct H0 as [-> | H0]; [easy | ]. apply IH in H0 as (? & ? & ?); eauto.
    + destruct H0 as [-> | H0]; [easy | ]. apply IH in H0 as (? & ? & ?); eauto.
Qed. 

Lemma unflattenPR (f : FlatPR) : isValidFlattening f -> {f' : PR & isFlatPROf f f'}.
Proof. 
  intros (H1 & H2 & H3).
  apply unflattenWindows in H3 as (w' & H3). 
  apply unflattenFinal in H2 as (f' & H2). 
  apply unflattenString in H1 as (i' & H1). 
  exists (Build_PR (offset f) (width f) i' w' f' (steps f)). 
  constructor; eauto.
  cbn. unfold finRepr. specialize (Fin_cardinality (Sigma f)). easy.  
Qed.

(** ** extraction *)

From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Import  LProd LOptions LLNat LLists.

Section fix_X.
  Variable (X:Type).
  Context `{X_registered : registered X}.

  MetaCoq Run (tmGenEncode "PRWin_enc" (PRWin X)).
  Hint Resolve PRWin_enc_correct : Lrewrite.

  Global Instance term_Build_PRWin : computableTime' (@Build_PRWin X) (fun _ _ => (1, fun _ _ => (1, tt))).
  Proof.
    extract constructor. solverec. 
  Defined. 

  Definition cnst_prem := 5. 
  Global Instance term_prem : computableTime' (@prem X) (fun _ _ => (cnst_prem, tt)).
  Proof.
    extract. unfold cnst_prem. solverec.
  Defined. 

  Definition cnst_conc := 5.
  Global Instance term_conc : computableTime' (@conc X) (fun _ _ => (cnst_conc, tt)). 
  Proof.
    extract. unfold cnst_conc. solverec. 
  Defined.

  Definition c__sizePRWin := 4.
  Lemma PRWin_enc_size (win : PRWin X) : size (enc win) = size (enc (prem win)) + size (enc (conc win)) + c__sizePRWin.
  Proof. 
    destruct win. cbn. unfold enc, c__sizePRWin. cbn. nia.
  Qed. 
End fix_X. 

Hint Resolve PRWin_enc_correct : Lrewrite.

MetaCoq Run (tmGenEncode "FlatPR_enc" (FlatPR)).
Hint Resolve FlatPR_enc_correct : Lrewrite. 

From Undecidability.L.Complexity Require Import PolyBounds. 

Instance term_Build_FlatPR : computableTime' Build_FlatPR (fun _ _ => (1, fun _ _ => (1, fun _ _ => (1, fun _ _ => (1, fun _ _ => (1, fun _ _ => (1, fun _ _ => (1, tt)))))))).
Proof.
  extract constructor. solverec. 
Defined. 

Definition c__Sigma := 10.
Instance term_FlatPR_Sigma : computableTime' Sigma (fun _ _ => (c__Sigma, tt)). 
Proof.
  extract. unfold c__Sigma. solverec. 
Defined. 

Definition c__offset := 10.
Instance term_FlatPR_offset : computableTime' offset (fun _ _ => (c__offset, tt)). 
Proof. 
  extract. unfold c__offset. solverec. 
Defined. 

Definition c__width := 10.
Instance term_FlatPR_width : computableTime' width (fun _ _ => (c__width, tt)). 
Proof. 
  extract. unfold c__width. solverec. 
Defined. 

Definition c__init := 10.
Instance term_FlatPR_init : computableTime' init (fun _ _ => (c__init, tt)). 
Proof. 
  extract. unfold c__init. solverec. 
Defined. 

Definition c__windows := 10.
Instance term_FlatPR_windows : computableTime' windows (fun _ _ => (c__windows, tt)). 
Proof. 
  extract. unfold c__windows. solverec. 
Defined. 

Definition c__final := 10.
Instance term_FlatPR_final : computableTime' final (fun _ _ => (c__final, tt)). 
Proof. 
  extract. unfold c__final. solverec. 
Defined. 

Definition c__steps := 10.
Instance term_FlatPR_steps : computableTime' steps (fun _ _ => (c__steps, tt)). 
Proof. 
  extract. unfold c__steps. solverec. 
Defined. 

Lemma FlatPR_enc_size (fpr : FlatPR) : size (enc fpr) = size (enc (Sigma fpr)) + size(enc (offset fpr)) + size (enc (width fpr)) + size (enc (init fpr)) + size (enc (windows fpr)) + size (enc (final fpr)) + size (enc (steps fpr)) + 9. 
Proof. 
  destruct fpr. cbn. unfold enc. cbn. nia.
Qed. 

(*extraction of PRWin_of_size_dec *)
Section PRWin_of_size. 
  Variable ( X : Type). 
  Context `{X_registered : registered X}.

  Definition c__prwinOfSizeDec := 2 * (cnst_prem + 2 * 5 + cnst_conc + 6 + c__length).
  Definition PRWin_of_size_dec_time (width : nat) (win : PRWin X) := c__prwinOfSizeDec * (1 + |prem win| + |conc win|) + eqbTime (X := nat) (size (enc (|prem win|))) (size (enc width)) + eqbTime (X := nat) (size (enc (|conc win|))) (size (enc width)).
  Global Instance term_PRWin_of_size_dec : computableTime' (@PRWin_of_size_dec X) (fun width _ => (1, fun win _ => (PRWin_of_size_dec_time width win, tt))). 
  Proof. 
    extract. solverec. unfold PRWin_of_size_dec_time, c__prwinOfSizeDec. nia.  
  Defined. 

  Definition c__prwinOfSizeDecBound := c__prwinOfSizeDec + c__eqbComp nat. 
  Lemma PRWin_of_size_dec_time_bound width (win : PRWin X) : PRWin_of_size_dec_time width win <= (size(enc win) + 1) * c__prwinOfSizeDecBound. 
  Proof. 
    unfold PRWin_of_size_dec_time. rewrite !eqbTime_le_l. rewrite !list_size_enc_length, !list_size_length. 
    rewrite PRWin_enc_size. unfold c__prwinOfSizeDecBound, c__sizePRWin. nia.
  Qed. 
End PRWin_of_size. 

(*extraction of FlatPR_wf_dec *)
Definition c__FlatPRWfDec := 3 * c__leb2 + 4 * c__width + 3 * c__offset + 2 * 5 + 2 * c__init + 2 * c__length + c__windows + 32 + 4 * c__leb + 2 * c__eqbComp nat * size (enc 0).
Definition FlatPR_wf_dec_time x := 2 * c__length * (|init x|) + leb_time (width x) (|init x|) + forallb_time (@PRWin_of_size_dec_time nat (width x)) (windows x) + modulo_time (|init x|) (offset x) + modulo_time (width x) (offset x) + c__FlatPRWfDec.  


Instance term_FlatPR_wf_dec : computableTime' FlatPR_wf_dec (fun fpr _ => (FlatPR_wf_dec_time fpr, tt)).
Proof. 
  extract. solverec. unfold FlatPR_wf_dec_time, c__FlatPRWfDec, leb_time. rewrite !eqbTime_le_r. 
  (*ring_simplify.*)
  rewrite Nat.le_min_l. rewrite Nat.le_min_l. 
  simp_comp_arith. 
  (*nia. *)
  leq_crossout.
Defined.
(*nia. *)
(*zify. clear. nia.*)


Definition c__FlatPRWfDecBound := 2*(2 * c__length + c__leb + c__prwinOfSizeDecBound + c__forallb + 2 * c__moduloBound + c__FlatPRWfDec).
Definition poly__FlatPRWfDec n := (n*n + 2* n + 1) * c__FlatPRWfDecBound.

Lemma FlatPR_wf_dec_time_bound fpr : 
  FlatPR_wf_dec_time fpr <= poly__FlatPRWfDec (size (enc fpr)). 
Proof. 
  unfold FlatPR_wf_dec_time. rewrite leb_time_bound_l. 
  rewrite !modulo_time_bound. rewrite list_size_enc_length.
  rewrite list_size_length.
  erewrite forallb_time_bound_env.
  2: {
    split; [intros | ].
    - specialize (PRWin_of_size_dec_time_bound (X := nat) y a) as H1.
      instantiate (2:= fun n => (n + 1) * c__prwinOfSizeDecBound). simp_comp_arith. nia. 
    - smpl_inO. 
  }
  rewrite list_size_length. 
  replace_le (size(enc (windows fpr))) with (size (enc fpr)) by (rewrite FlatPR_enc_size; lia). 
  replace_le (size(enc (init fpr))) with (size (enc fpr)) by (rewrite FlatPR_enc_size; lia). 
  replace_le (size(enc (width fpr))) with (size (enc fpr)) by (rewrite FlatPR_enc_size; lia). 
  replace_le (size(enc(offset fpr))) with (size (enc fpr)) by (rewrite FlatPR_enc_size; lia). 
  unfold poly__FlatPRWfDec, c__FlatPRWfDecBound. nia.
Qed. 
Lemma FlatPR_wf_dec_poly : monotonic poly__FlatPRWfDec /\ inOPoly poly__FlatPRWfDec.
Proof. 
  unfold poly__FlatPRWfDec; split; smpl_inO. 
Qed. 

(*extraction of isValidFlattening_dec *)

(*PRWin_ofFlatType_dec *)
Definition c__PRWinOfFlatTypeDec := cnst_prem + cnst_conc +8.
Definition PRWin_ofFlatType_dec_time (sig : nat) (w : PRWin nat):= list_ofFlatType_dec_time sig (prem w) + list_ofFlatType_dec_time sig (conc w) + c__PRWinOfFlatTypeDec. 
Instance term_PRWin_ofFlatType_dec : computableTime' PRWin_ofFlatType_dec (fun sig _ => (1, fun w _ => (PRWin_ofFlatType_dec_time sig w, tt))). 
Proof.
  extract. solverec. unfold PRWin_ofFlatType_dec_time, c__PRWinOfFlatTypeDec. nia.
Defined. 

Definition c__PRWinOfFlatTypeDecBound := 2 * (c__PRWinOfFlatTypeDec + 1).
Definition poly__PRWinOfFlatTypeDec n := (poly__listOfFlatTypeDec n + 1) * c__PRWinOfFlatTypeDecBound.
Lemma PRWin_ofFlatType_dec_time_bound sig w : PRWin_ofFlatType_dec_time sig w <= poly__PRWinOfFlatTypeDec (size (enc sig) + size (enc w)).
Proof. 
  unfold PRWin_ofFlatType_dec_time. rewrite !list_ofFlatType_dec_time_bound. 
  unfold poly__PRWinOfFlatTypeDec.
  poly_mono list_ofFlatType_dec_poly at 2.
  2: (replace_le (size (enc (conc w))) with (size (enc w)) by (rewrite PRWin_enc_size; lia)); reflexivity.
  poly_mono list_ofFlatType_dec_poly at 1.
  2: (replace_le (size (enc (prem w))) with (size (enc w)) by (rewrite PRWin_enc_size; lia)); reflexivity.
  unfold c__PRWinOfFlatTypeDecBound. nia. 
Qed. 
Lemma PRWin_ofFlatType_dec_poly : monotonic poly__PRWinOfFlatTypeDec /\ inOPoly poly__PRWinOfFlatTypeDec. 
Proof. 
  split; unfold poly__PRWinOfFlatTypeDec; smpl_inO; apply list_ofFlatType_dec_poly.  
Qed. 

(*isValidFlattening_dec *)
Definition c__isValidFlatteningDec := 3 * c__Sigma + c__init + c__final + c__windows + 16.
Definition isValidFlattening_dec_time x := list_ofFlatType_dec_time (Sigma x) (init x) + forallb_time (list_ofFlatType_dec_time (Sigma x)) (final x)+ forallb_time (PRWin_ofFlatType_dec_time (Sigma x)) (windows x) + c__isValidFlatteningDec.
Instance term_isValidFlattening_dec : computableTime' isValidFlattening_dec (fun fpr _ => (isValidFlattening_dec_time fpr, tt)).
Proof.
  extract. solverec. unfold isValidFlattening_dec_time, c__isValidFlatteningDec.
  repeat change (fun x => ?h x) with h. solverec. 
Defined. 

Definition c__isValidFlatteningDecBound := 2 * c__forallb + c__isValidFlatteningDec. 
Definition poly__isValidFlatteningDec n :=(n + 2) * poly__listOfFlatTypeDec n + (n + 1) * poly__PRWinOfFlatTypeDec n + (n + 1) * c__isValidFlatteningDecBound. 
Lemma isValidFlattening_dec_time_bound fpr : isValidFlattening_dec_time fpr <= poly__isValidFlatteningDec (size (enc fpr)). 
Proof. 
  unfold isValidFlattening_dec_time. 
  rewrite list_ofFlatType_dec_time_bound. 
  erewrite forallb_time_bound_env. 
  2: {
    split; [intros | ].
    - rewrite list_ofFlatType_dec_time_bound, Nat.add_comm; reflexivity. 
    - apply list_ofFlatType_dec_poly. 
  }
  erewrite forallb_time_bound_env. 
  2 : {
    split; [intros | ].
    - rewrite PRWin_ofFlatType_dec_time_bound, Nat.add_comm; reflexivity. 
    - apply PRWin_ofFlatType_dec_poly. 
  }

  rewrite !list_size_length. 
  poly_mono list_ofFlatType_dec_poly at 1. 
  2: (replace_le (size (enc (Sigma fpr)) + size (enc (init fpr))) with (size (enc fpr)) by (rewrite FlatPR_enc_size; lia)); reflexivity. 
  poly_mono list_ofFlatType_dec_poly at 2. 
  2: (replace_le (size (enc (final fpr)) + size (enc (Sigma fpr))) with (size (enc fpr)) by (rewrite FlatPR_enc_size; lia)); reflexivity. 
  replace_le (size (enc (final fpr))) with (size (enc fpr)) by (rewrite FlatPR_enc_size; lia) at 1. 
  replace_le (size (enc (windows fpr))) with (size (enc fpr)) by (rewrite FlatPR_enc_size; lia) at 1. 
  poly_mono PRWin_ofFlatType_dec_poly at 1. 
  2: (replace_le (size (enc (windows fpr)) + size (enc (Sigma fpr))) with (size (enc fpr)) by (rewrite FlatPR_enc_size; lia)); reflexivity. 
  unfold poly__isValidFlatteningDec, c__isValidFlatteningDecBound. nia.
Qed. 
Lemma isValidFlatteningDec_poly : monotonic poly__isValidFlatteningDec /\ inOPoly poly__isValidFlatteningDec. 
Proof. 
  split; (unfold poly__isValidFlatteningDec; smpl_inO; [apply list_ofFlatType_dec_poly |apply PRWin_ofFlatType_dec_poly ]). 
Qed. 
