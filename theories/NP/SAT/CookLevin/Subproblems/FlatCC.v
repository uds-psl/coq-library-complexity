From Undecidability.Shared.Libs.PSL Require Import Base FinTypes. 
From Undecidability Require Import L.Functions.EqBool.
From Complexity.NP.SAT.CookLevin Require Export CC.
From Complexity.Libs.CookPrelim Require Import MorePrelim FlatFinTypes.
Require Import Lia.

(** * Flat Covering Cards *)
(*A flattened version of Covering Cards using natural numbers to represent finite types *)

(** ** Definition *)
Inductive FlatCC := {
  Sigma : nat;
  offset : nat;
  width : nat;
  init : list nat;
  cards : list (CCCard nat);
  final : list (list nat);
  steps : nat
  }.

(**validity of cards and final constraints relative to an alphabet *)
(**we have to enforce this as we always consider only a finite subset of N *)
Definition CCCard_ofFlatType (card : CCCard nat) k:= list_ofFlatType k (prem card) /\ list_ofFlatType k (conc card). 
Definition isValidFlatCards (l : list (CCCard nat)) k := (forall card, card el l -> CCCard_ofFlatType card k).
Definition isValidFlatFinal (l : list (list nat)) k := (forall s, s el l -> list_ofFlatType k s).
Definition isValidFlatInitial (l : list nat) k := list_ofFlatType k l.

(**the well-formedness constraints are the same as for CC *)
Definition FlatCC_wellformed fpr := 
  width fpr > 0 
  /\ offset fpr > 0 
  /\ (exists k, k > 0 /\ width fpr = k * offset fpr)
  /\ length (init fpr) >= width fpr
  /\ (forall card, card el cards fpr -> CCCard_of_size card (width fpr)) 
  /\ (exists k, length (init fpr) = k * offset fpr). 

(**additionally, we require that instances only use the given finite subset of N *)
Definition isValidFlattening fpr := 
 list_ofFlatType (Sigma fpr) (init fpr) 
  /\ (forall s, s el final fpr -> list_ofFlatType (Sigma fpr) s)
  /\ (forall card, card el cards fpr -> CCCard_ofFlatType card (Sigma fpr)). 

(**the definitions of validity and satisfaction of final constraints can be re-used *)

(**we can now define the language of valid FlatCC instances *)
Definition FlatCCLang (C : FlatCC) := FlatCC_wellformed C /\ isValidFlattening C
  /\ exists (sf : list nat), list_ofFlatType (Sigma C) sf 
      /\ relpower (valid (offset C) (width C) (cards C)) (steps C) (init C) sf 
      /\ satFinal (offset C) (length (init C)) (final C) sf.

Section fixInstance.
  Variable (fpr : FlatCC). 
  Notation Sigma := (Sigma fpr).
  Notation offset := (offset fpr).
  Notation width := (width fpr).
  Notation init := (init fpr).
  Notation cards := (cards fpr).
  Notation final := (final fpr).
  Notation steps := (steps fpr). 

  Notation "a ⇝ b" := (valid offset width cards a b) (at level 40). 

  Context (A : FlatCC_wellformed fpr). 
  Context (B : isValidFlattening fpr). 

  (**we want to prove that for syntactically well-formed instances, we can only make a step to strings that are again strings over the finite alphabet *)
  (**we first prove a more general statement over abstract homomorph properties*)
  Lemma p_invariant (p : list nat -> Prop) (a b : list nat) : 
    p a 
    -> (forall x y, p (x ++ y) <-> p x /\ p y) 
    -> |a| >= width 
    -> (forall x y u v card, coversHead card (u ++ x) (v ++ y) -> card el cards -> |u| = offset -> |v| = offset -> p v)
    -> (forall card, card el cards -> p (conc card))
    -> a ⇝ b 
    -> p b. 
  Proof. 
    intros H H0 H1 G1 G2 H2. 
    (*we switch to the direct characterisation *)
    assert (a ⇝ b /\ |a| >= width) as H3%validDirect_valid by tauto. 2-4: apply A.
    clear H2 H1. induction H3 as [a b card H1 H2 H4 H5 | a b u v card H1 IH H2 H4 H5 H6]. 
    - clear G1. 
      destruct A as (_ & _ & (k & _ & A2) & _ & A6 & _).  
      destruct B as ( _ & _ & A5).
      specialize (A5 _ H4) as (A5 & A7). 
      specialize H5 as ((rest' & H6') & (rest & H6)).  (*show rest = [] *)
      specialize (A6 _ H4) as (A6 & A6').
      subst. rewrite app_length in H2. 
      (*we need some structural assumptions *)
      assert (rest = []) as ->. 
      { 
        destruct rest'; cbn in H2; [ | lia]. rewrite !app_length in H1. 
        destruct rest; [ easy | cbn in H1; lia].
      }       
      rewrite app_nil_r. now apply G2.     
    - rewrite H0. apply H0 in H. split; [ | apply IH; easy]. now eapply G1. 
  Qed. 

  (**the statement is now a straightforward corollary *)
  Corollary valid_list_ofFlatType_invariant a b : 
    list_ofFlatType Sigma a -> |a| >= width -> a ⇝ b -> list_ofFlatType Sigma b. 
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

  (**of course, this transfers to an arbitrary number of rewrite steps *)
  Lemma relpower_valid_list_ofFlatType_invariant steps a b: 
    list_ofFlatType Sigma a 
    -> |a| >= width 
    -> relpower (valid offset width cards) steps a b 
    -> list_ofFlatType Sigma b. 
  Proof. 
    intros. induction H1 as [ a | ? ? ? ? H1 H2 IH]; [easy | ]. 
    apply IH. eapply valid_list_ofFlatType_invariant, H1; [ apply H | ]. 
    - apply H0.  
    - apply valid_length_inv in H1. nia.  
  Qed. 

End fixInstance.

(**deciders for isValidFlattening and well-formedness *)
Definition CCCard_ofFlatType_dec (Sigma : nat) (card : CCCard nat) := 
  list_ofFlatType_dec Sigma (prem card) && list_ofFlatType_dec Sigma (conc card). 
Lemma CCCard_ofFlatType_dec_correct card Sigma : 
  CCCard_ofFlatType_dec Sigma card = true <-> CCCard_ofFlatType card Sigma. 
Proof. 
  unfold CCCard_ofFlatType_dec, CCCard_ofFlatType. rewrite andb_true_iff. 
  rewrite !list_ofFlatType_dec_correct. easy. 
Qed. 

Definition FlatCC_wf_dec (fpr : FlatCC) := 
  leb 1 (width fpr) 
  && leb 1 (offset fpr)
  && Nat.eqb (Nat.modulo (width fpr) (offset fpr)) 0
  && leb (width fpr) (|init fpr|)
  && forallb (CCCard_of_size_dec (width fpr)) (cards fpr)
  && Nat.eqb (Nat.modulo (|init fpr|) (offset fpr)) 0. 
Definition isValidFlattening_dec (fpr : FlatCC) := 
  list_ofFlatType_dec (Sigma fpr) (init fpr)
  && forallb (list_ofFlatType_dec (Sigma fpr)) (final fpr)
  && forallb (CCCard_ofFlatType_dec (Sigma fpr)) (cards fpr). 

Lemma FlatCC_wf_dec_correct (fpr : FlatCC) : FlatCC_wf_dec fpr = true <-> FlatCC_wellformed fpr. 
Proof. 
  unfold FlatCC_wf_dec, FlatCC_wellformed. rewrite !andb_true_iff, !and_assoc.
  rewrite !leb_iff. rewrite <- !(reflect_iff _ _ (Nat.eqb_spec _ _ )).  
  rewrite !forallb_forall. 
  setoid_rewrite CCCard_of_size_dec_correct. 
  split; intros; repeat match goal with [H : _ /\ _ |- _] => destruct H end; 
  repeat match goal with [ |- _ /\ _ ] => split end; try easy. 
  - apply Nat.mod_divide in H1 as (k & H1); [ | lia]. 
    exists k; split; [ | apply H1 ]. destruct k; cbn in *; lia.
  - apply Nat.mod_divide in H4 as (k & H4); [ | lia].  exists k; apply H4.  
  - apply Nat.mod_divide; [ lia | ]. destruct H1 as (k & _ & H1). exists k; apply H1.
  - apply Nat.mod_divide; [ lia | ]. apply H4. 
Qed. 

Lemma isValidFlattening_dec_correct (fpr : FlatCC) : isValidFlattening_dec fpr = true <-> isValidFlattening fpr. 
Proof. 
  unfold isValidFlattening_dec, isValidFlattening.
  rewrite !andb_true_iff, !and_assoc.
  rewrite !forallb_forall. 
  setoid_rewrite CCCard_ofFlatType_dec_correct. 
  setoid_rewrite list_ofFlatType_dec_correct. 
  split; intros; repeat match goal with [H : _ /\ _ |- _] => destruct H end; 
  repeat match goal with [ |- _ /\ _ ] => split end; try easy. 
Qed. 

(** ** relation to CC instances *)
Inductive isFlatCCCardOf (X : finType) (flatcard : CCCard nat) (card : CCCard X) := 
  mkIsFlatCCCardO (Hprem : isFlatListOf (prem flatcard) (prem card)) 
    (Hconc : isFlatListOf (conc flatcard) (conc card))
  : isFlatCCCardOf flatcard card. 

Inductive isFlatCardsOf (X : finType) (flatcards : list (CCCard nat)) (cards : list (CCCard X)) := 
  mkIsFlatCardsOf (Hsound : forall flatcard, flatcard el flatcards -> exists card, card el cards /\ isFlatCCCardOf flatcard card)
    (Hcomplete : forall card, card el cards -> exists flatcard, flatcard el flatcards /\ isFlatCCCardOf flatcard card)
  : isFlatCardsOf flatcards cards. 

Inductive isFlatFinalOf (X : finType) (flatfinal : list (list nat)) (final : list (list X)) := 
  mkIsFlatFinalOf (Hsound : forall fin, fin el flatfinal -> exists fin', fin' el final /\ isFlatListOf fin fin')
    (Hcomplete : forall fin, fin el final -> exists fin', fin' el flatfinal /\ isFlatListOf fin' fin)
  : isFlatFinalOf flatfinal final. 

Inductive isFlatCCOf (fpr : FlatCC) (pr : CC) := 
  mkIsFlatCCOf (HSigma : finRepr (CC.Sigma pr) (Sigma fpr))
    (HOffset : offset fpr = CC.offset pr)
    (HWidth : width fpr = CC.width pr)
    (HInit : isFlatListOf (init fpr) (CC.init pr))
    (HCards : isFlatCardsOf (cards fpr) (CC.cards pr))
    (HFinal : isFlatFinalOf (final fpr) (CC.final pr))
    (HSteps : steps fpr = CC.steps pr)
  : isFlatCCOf fpr pr.

Lemma isFlatCCOf_isValidFlattening (fpr : FlatCC) (pr : CC) : isFlatCCOf fpr pr -> isValidFlattening fpr. 
Proof. 
  intros. destruct H.
  repeat split.
  - rewrite HSigma. now eapply isFlatListOf_list_ofFlatType. 
  - intros s H0%HFinal. rewrite HSigma. destruct H0 as (s' & F1 & ->). 
    eapply isFlatListOf_list_ofFlatType. unfold isFlatListOf. reflexivity. 
  - apply HCards in H. destruct H as (card' & F1 & F2). 
    destruct F2 as (F2 & F3). rewrite HSigma. 
    eapply isFlatListOf_list_ofFlatType, F2. 
  - apply HCards in H. destruct H as (card' & F1 & F2). 
    destruct F2 as (F2 & F3). rewrite HSigma. 
    eapply isFlatListOf_list_ofFlatType, F3. 
Qed. 

(** we show that FlatCC instances "behave in the same way" as CC instances  *)

Lemma coversHead_flat_agree (X : finType) (cardsFin : list (CCCard X)) cardsFlat finStr finStr' flatStr flatStr' :
  isFlatListOf flatStr finStr
  -> isFlatListOf flatStr' finStr'
  -> isFlatCardsOf cardsFlat cardsFin 
  -> (exists card, card el cardsFin /\ coversHead card finStr finStr') <-> (exists card, card el cardsFlat /\ coversHead card flatStr flatStr'). 
Proof. 
  intros. split; intros (card & H2 & H3).
  - apply H1 in H2 as (card' & F1 & F2). exists card'. split; [apply F1 | ]. 
    unfold coversHead, prefix in *. destruct H3 as ((b1 & ->) & (b2 & ->)). 
    unfold isFlatListOf in H, H0.
    rewrite map_app in H, H0. split.
    + exists (map index b1). rewrite H. enough (map index (prem card) = prem card') as H2.
      { now setoid_rewrite H2. }
      destruct card; cbn.
      destruct F2. cbn in *. now rewrite Hprem.  
    + exists (map index b2). rewrite H0. enough (map index (conc card) = conc card') as H2. 
      { now setoid_rewrite H2. }
      destruct card; cbn. 
      destruct F2. cbn in *. now rewrite Hconc. 
  - apply H1 in H2 as (card' & F1 & F2). exists card'. split; [ apply F1 | ].
    unfold coversHead, prefix in *. destruct H3 as ((b1 & ->) & (b2 & ->)).
    unfold isFlatListOf in H, H0. split.
    + symmetry in H. apply map_eq_app in H as (finStr1  & finStr2 & -> & ? & ?). 
      exists finStr2.
      enough (finStr1 = prem card') as H3 by (now setoid_rewrite H3).
      destruct F2. rewrite Hprem in H. 
      apply map_injective in H; [easy | unfold injective; apply injective_index]. 
    + symmetry in H0. apply map_eq_app in H0 as (finStr1  & finStr2 & -> & ? & ?). 
      exists finStr2.
      enough (finStr1 = conc card') as H3 by (now setoid_rewrite H3).
      destruct F2. rewrite Hconc in H0. 
      apply map_injective in H0; [easy | unfold injective; apply injective_index].
Qed.

Section fixFCCInstance. 
  (*for the proof, we fix an instance *)
  Variable (fpr : FlatCC). 
  Notation Sigma := (Sigma fpr).
  Notation offset := (offset fpr).
  Notation width := (width fpr).
  Notation init := (init fpr).
  Notation cards := (cards fpr).
  Notation final := (final fpr).
  Notation steps := (steps fpr). 

  Context (A : FlatCC_wellformed fpr). 
  Context (B : isValidFlattening fpr). 


  Lemma valid_flat_agree (X : finType) (fcards : list (CCCard X)) s1 s2 fs1 fs2: 
    isFlatListOf fs1 s1 
    -> isFlatListOf fs2 s2
    -> isFlatCardsOf cards fcards 
    -> valid offset width cards fs1 fs2 <-> valid offset width fcards s1 s2. 
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
        assert (exists w, w el cards /\ coversHead w (map index ls1 ++ map index ls2) (map index rs1 ++ map index rs2)) as H5 by eauto.
        eapply coversHead_flat_agree in H5 as (fincard & H5 & H6). 
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
        assert (exists w, w el fcards /\ coversHead w (u ++ a) (v++b)) as H7 by eauto.
        eapply coversHead_flat_agree in H7 as (fincard & H7 & H8). 2-4: eauto.
        econstructor 3. 2-3: rewrite map_length; auto.
        * now eapply IHvalid.
        * apply H7. 
        * rewrite H4, H5 in H8. now rewrite !map_app in H8. 
  Qed. 

  (** we re-use the lemma proven above which asserts that list_ofFlatType is invariant *)
  (** for that, we need more assumptions than are required in principle, but this is okay *)
  Lemma valid_flat_isFlatListOf_invariant (X : finType) (s1 : list X) fs1 fs2: 
    finRepr X Sigma
    -> isFlatListOf fs1 s1
    -> |fs1| >= width 
    -> valid offset width cards fs1 fs2
    -> exists (s2 : list X), isFlatListOf fs2 s2. 
  Proof. 
    intros. 
    apply isFlatListOf_list_ofFlatType in H0. rewrite <- H in H0. 
    specialize (@valid_list_ofFlatType_invariant fpr A B fs1 fs2 H0 H1 H2) as H4. 
    apply (finRepr_exists_list H) in H4. destruct H4 as (s2 & H4); easy.
  Qed. 

  Lemma relpower_valid_flat_agree (X : finType) (fincards : list (CCCard X)) s1 s2 fs1 fs2 n:
    finRepr X Sigma
    -> |fs1| >= width 
    -> isFlatListOf fs1 s1
    -> isFlatListOf fs2 s2
    -> isFlatCardsOf cards fincards
    -> relpower (valid offset width cards) n fs1 fs2 <-> relpower (valid offset width fincards) n s1 s2.
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
End fixFCCInstance. 

(*well-formedness is equivalent, of course *)
Lemma isFlatCCOf_wf_equivalent (pr : CC) (fpr : FlatCC) : 
  isFlatCCOf fpr pr -> (FlatCC_wellformed fpr <-> CC_wellformed pr). 
Proof. 
  intros [H1 H2 H3 H4]. split; intros; unfold FlatCC_wellformed, CC_wellformed in *.
  - destruct H as (F1 & F2 & F3 & F4 & F5 & F6). repeat split.  
    + easy.
    + easy.
    + destruct F3 as (k & F3 & F3'). exists k. nia.
    + rewrite -> H4 in F4. rewrite map_length in F4. lia. 
    + apply HCards in H as (flatcard & H & H5). apply F5 in H. 
      destruct H5. destruct H as (H & _). rewrite Hprem in H. rewrite map_length in H. lia.  
    + apply HCards in H as (flatcard & H & H5). apply F5 in H. 
      destruct H5. destruct H as (_ & H). rewrite Hconc in H. rewrite map_length in H. lia.  
    + destruct F6 as (k & F6). rewrite H4 in F6. rewrite map_length in F6. exists k; nia.
  - destruct H as (F1 & F2 & F3 & F4 & F5 & F6). repeat split. 
    + easy. 
    + easy. 
    + destruct F3 as (k & F3 & F3'). exists k. nia. 
    + rewrite H4, map_length. lia.  
    + apply HCards in H as (fincard & H & H5). apply F5 in H. 
      destruct H5. destruct H as (H & _). rewrite Hprem, map_length. lia.  
    + apply HCards in H as (fincard & H & H5). apply F5 in H. 
      destruct H5. destruct H as (_ & H). rewrite Hconc, map_length. lia. 
    + destruct F6 as (k & F6). rewrite H4, map_length. exists k. nia. 
Qed. 

(** now we can derive equivalence of instances related via isFlatCCOf *)
Lemma isFlatCCOf_equivalence (pr : CC) (fpr : FlatCC) : 
  isFlatCCOf fpr pr -> (FlatCCLang fpr <-> CCLang pr). 
Proof. 
  intros. split. 
  - intros (H1 & H2 & H3). split; [ now eapply isFlatCCOf_wf_equivalent | ]. 
    destruct H as [F1 F2 F3 F4 F5].
    destruct H3 as (sf & H3 & H4 & H5).
    apply (finRepr_exists_list F1) in H3 as (SF & H3).
    exists SF. split. 
    + rewrite <- F2, <- F3, <- HSteps. eapply relpower_valid_flat_agree; eauto. apply H1.    
    + rewrite <- F2. rewrite F4, map_length in H5. eapply final_flat_agree; eauto.
  - intros (H1 & H2). split; [ now eapply isFlatCCOf_wf_equivalent | ]. 
    split; [now eapply isFlatCCOf_isValidFlattening | ].
    destruct H as [F1 F2 F3 F4 F5]. 
    destruct H2 as (sf & H3 & H4). 
    exists (map index sf). repeat split. 
    + unfold list_ofFlatType, ofFlatType. 
      setoid_rewrite in_map_iff. intros a (x & <- & H). rewrite F1. apply index_le. 
    + eapply relpower_valid_flat_agree; eauto.
      * now rewrite isFlatCCOf_wf_equivalent. 
      * now eapply isFlatCCOf_isValidFlattening with (pr := pr). 
      * rewrite F4, map_length, F3. apply H1. 
      * unfold isFlatListOf. reflexivity. 
      * rewrite  F2,  F3, HSteps. apply H3. 
    + eapply final_flat_agree; eauto. 
      * unfold isFlatListOf; reflexivity. 
      * rewrite F2, F4, map_length. apply H4. 
Qed. 

(** ** Unflattening *)
(** given a well-formed flat instance, we can derive a "canonical" (up to bijections of the finite type) CC instance *)
(** we use Fin.t as the canonical finite type *)
 
Import Coq.Init.Specif.
Lemma unflattenString (f : list nat) k : list_ofFlatType k f -> {f' : list (finType_CS (Fin.t k)) & isFlatListOf f f'}.
Proof. 
  intros H. 
  eapply finRepr_exists_list with (X := finType_CS (Fin.t k)) in H as (a' & H). 
  2: { unfold finRepr. specialize (Fin_cardinality k). easy. }
  eauto.
Qed. 

Lemma unflattenCarddow (w : CCCard nat) k : CCCard_ofFlatType w k -> {w' : CCCard (finType_CS (Fin.t k)) & isFlatCCCardOf w w'}. 
Proof. 
  intros. destruct w. destruct H as (H1 & H2). cbn in *.
  apply unflattenString in H1 as (prem' & H1). 
  apply unflattenString in H2 as (conc' & H2).
  exists (Build_CCCard prem' conc'). split; easy.
Qed. 

Lemma unflattenCards (l : list (CCCard nat)) k : isValidFlatCards l k -> {l' : list (CCCard (finType_CS (Fin.t k))) & isFlatCardsOf l l'}.
Proof. 
  intros. unfold isValidFlatCards in H. induction l. 
  - exists []. easy.
  - edestruct IHl as (l' & IH);[ easy | ]. specialize (H a (or_introl eq_refl)). 
    apply unflattenCarddow in H as (a' & H). exists (a' :: l'). split; intros.
    + destruct H0 as [-> | H0]; [easy | ]. apply IH in H0 as (card & ? & ?); eauto.
    + destruct H0 as [-> | H0]; [ easy | ]. apply IH in H0 as (card' & ? & ?); eauto.
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

Lemma unflattenCC (f : FlatCC) : isValidFlattening f -> {f' : CC & isFlatCCOf f f'}.
Proof. 
  intros (H1 & H2 & H3).
  apply unflattenCards in H3 as (w' & H3). 
  apply unflattenFinal in H2 as (f' & H2). 
  apply unflattenString in H1 as (i' & H1). 
  exists (Build_CC (offset f) (width f) i' w' f' (steps f)). 
  constructor; eauto.
  cbn. unfold finRepr. specialize (Fin_cardinality (Sigma f)). easy.  
Qed.

(** ** extraction *)

From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Import  LProd LOptions.

Section fix_X.
  Variable (X:Type).
  Context `{X_encodable: encodable X}.

  MetaCoq Run (tmGenEncode "CCCard_enc" (CCCard X)).
  Hint Resolve CCCard_enc_correct : Lrewrite.

  Global Instance term_Build_CCCard : computableTime' (@Build_CCCard X) (fun _ _ => (1, fun _ _ => (1, tt))).
  Proof.
    extract constructor. solverec. 
  Qed. 

  Definition cnst_prem := 5. 
  Global Instance term_prem : computableTime' (@prem X) (fun _ _ => (cnst_prem, tt)).
  Proof.
    extract. unfold cnst_prem. solverec.
  Qed. 

  Definition cnst_conc := 5.
  Global Instance term_conc : computableTime' (@conc X) (fun _ _ => (cnst_conc, tt)). 
  Proof.
    extract. unfold cnst_conc. solverec. 
  Qed.

  Definition c__sizeCCCard := 4.
  Lemma CCCard_enc_size (card : CCCard X) : size (enc card) = size (enc (prem card)) + size (enc (conc card)) + c__sizeCCCard.
  Proof. 
    destruct card. cbn. unfold enc at 1, c__sizeCCCard. cbn. nia.
  Qed. 
End fix_X. 

#[export]
Hint Resolve CCCard_enc_correct : Lrewrite.

MetaCoq Run (tmGenEncode "FlatCC_enc" (FlatCC)).
#[export]
Hint Resolve FlatCC_enc_correct : Lrewrite. 

From Complexity.Libs.CookPrelim Require Import PolyBounds. 

#[export]
Instance term_Build_FlatCC : computableTime' Build_FlatCC (fun _ _ => (1, fun _ _ => (1, fun _ _ => (1, fun _ _ => (1, fun _ _ => (1, fun _ _ => (1, fun _ _ => (1, tt)))))))).
Proof.
  extract constructor. solverec. 
Qed. 

Definition c__Sigma := 10.
#[export]
Instance term_FlatCC_Sigma : computableTime' Sigma (fun _ _ => (c__Sigma, tt)). 
Proof.
  extract. unfold c__Sigma. solverec. 
Qed. 

Definition c__offset := 10.
#[export]
Instance term_FlatCC_offset : computableTime' offset (fun _ _ => (c__offset, tt)). 
Proof. 
  extract. unfold c__offset. solverec. 
Qed. 

Definition c__width := 10.
#[export]
Instance term_FlatCC_width : computableTime' width (fun _ _ => (c__width, tt)). 
Proof. 
  extract. unfold c__width. solverec. 
Qed. 

Definition c__init := 10.
#[export]
Instance term_FlatCC_init : computableTime' init (fun _ _ => (c__init, tt)). 
Proof. 
  extract. unfold c__init. solverec. 
Qed. 

Definition c__cards := 10.
#[export]
Instance term_FlatCC_cards : computableTime' cards (fun _ _ => (c__cards, tt)). 
Proof. 
  extract. unfold c__cards. solverec. 
Qed. 

Definition c__final := 10.
#[export]
Instance term_FlatCC_final : computableTime' final (fun _ _ => (c__final, tt)). 
Proof. 
  extract. unfold c__final. solverec. 
Qed. 

Definition c__steps := 10.
#[export]
Instance term_FlatCC_steps : computableTime' steps (fun _ _ => (c__steps, tt)). 
Proof. 
  extract. unfold c__steps. solverec. 
Qed. 

Lemma FlatCC_enc_size (fpr : FlatCC) : size (enc fpr) = size (enc (Sigma fpr)) + size(enc (offset fpr)) + size (enc (width fpr)) + size (enc (init fpr)) + size (enc (cards fpr)) + size (enc (final fpr)) + size (enc (steps fpr)) + 9. 
Proof. 
  destruct fpr. cbn.  
  unfold enc at 1. cbn. nia.
Qed. 

(** extraction of CCCard_of_size_dec *)
Section CCCard_of_size. 
  Variable ( X : Type). 
  Context `{X_encodable: encodable X}.

  Definition c__prcardOfSizeDec := 2 * (cnst_prem + 2 * 5 + cnst_conc + 6 + c__length).
  Definition CCCard_of_size_dec_time (width : nat) (card : CCCard X) := c__prcardOfSizeDec * (1 + |prem card| + |conc card|) + eqbTime (X := nat) (size (enc (|prem card|))) (size (enc width)) + eqbTime (X := nat) (size (enc (|conc card|))) (size (enc width)).
  Global Instance term_CCCard_of_size_dec : computableTime' (@CCCard_of_size_dec X) (fun width _ => (1, fun card _ => (CCCard_of_size_dec_time width card, tt))). 
  Proof. 
    extract. solverec. unfold CCCard_of_size_dec_time, c__prcardOfSizeDec. nia.  
  Qed. 

  Definition c__prcardOfSizeDecBound := c__prcardOfSizeDec + c__eqbComp nat. 
  Lemma CCCard_of_size_dec_time_bound width (card : CCCard X) : CCCard_of_size_dec_time width card <= (size(enc card) + 1) * c__prcardOfSizeDecBound. 
  Proof. 
    unfold CCCard_of_size_dec_time. rewrite !eqbTime_le_l. rewrite !list_size_enc_length, !list_size_length. 
    rewrite CCCard_enc_size. unfold c__prcardOfSizeDecBound, c__sizeCCCard. nia.
  Qed. 
End CCCard_of_size. 

(*extraction of FlatCC_wf_dec *)
Definition c__FlatCCWfDec := 3 * c__leb2 + 4 * c__width + 3 * c__offset + 2 * 5 + 2 * c__init + 2 * c__length + c__cards + 32 + 4 * c__leb + 2 * c__eqbComp nat * size (enc 0).
Definition FlatCC_wf_dec_time x := 2 * c__length * (|init x|) + leb_time (width x) (|init x|) + forallb_time (@CCCard_of_size_dec_time nat (width x)) (cards x) + modulo_time (|init x|) (offset x) + modulo_time (width x) (offset x) + c__FlatCCWfDec.  


#[export]
Instance term_FlatCC_wf_dec : computableTime' FlatCC_wf_dec (fun fpr _ => (FlatCC_wf_dec_time fpr, tt)).
Proof. 
  extract. solverec. unfold FlatCC_wf_dec_time, c__FlatCCWfDec, leb_time. rewrite !eqbTime_le_r.
  (*ring_simplify.*)
  rewrite !Nat.le_min_l with (n:=1). 
  simp_comp_arith. ring_simplify. reflexivity.
Qed.
(*nia. *)
(*zify. clear. nia.*)


Definition c__FlatCCWfDecBound := 2*(2 * c__length + c__leb + c__prcardOfSizeDecBound + c__forallb + 2 * c__moduloBound + c__FlatCCWfDec).
Definition poly__FlatCCWfDec n := (n*n + 2* n + 1) * c__FlatCCWfDecBound.

Lemma FlatCC_wf_dec_time_bound fpr : 
  FlatCC_wf_dec_time fpr <= poly__FlatCCWfDec (size (enc fpr)). 
Proof. 
  unfold FlatCC_wf_dec_time. rewrite leb_time_bound_l. 
  rewrite !modulo_time_bound. rewrite list_size_enc_length.
  rewrite list_size_length.
  erewrite forallb_time_bound_env.
  2: {
    split; [intros | ].
    - specialize (CCCard_of_size_dec_time_bound (X := nat) y a) as H1.
      instantiate (2:= fun n => (n + 1) * c__prcardOfSizeDecBound). simp_comp_arith. nia. 
    - smpl_inO. 
  }
  rewrite list_size_length. 
  replace_le (size(enc (cards fpr))) with (size (enc fpr)) by (rewrite FlatCC_enc_size; lia). 
  replace_le (size(enc (init fpr))) with (size (enc fpr)) by (rewrite FlatCC_enc_size; lia). 
  replace_le (size(enc (width fpr))) with (size (enc fpr)) by (rewrite FlatCC_enc_size; lia). 
  replace_le (size(enc(offset fpr))) with (size (enc fpr)) by (rewrite FlatCC_enc_size; lia). 
  unfold poly__FlatCCWfDec, c__FlatCCWfDecBound. nia.
Qed. 
Lemma FlatCC_wf_dec_poly : monotonic poly__FlatCCWfDec /\ inOPoly poly__FlatCCWfDec.
Proof. 
  unfold poly__FlatCCWfDec; split; smpl_inO. 
Qed. 


(** CCCard_ofFlatType_dec *)
Definition c__CCCardOfFlatTypeDec := cnst_prem + cnst_conc +8.
Definition CCCard_ofFlatType_dec_time (sig : nat) (w : CCCard nat):= list_ofFlatType_dec_time sig (prem w) + list_ofFlatType_dec_time sig (conc w) + c__CCCardOfFlatTypeDec. 
#[export]
Instance term_CCCard_ofFlatType_dec : computableTime' CCCard_ofFlatType_dec (fun sig _ => (1, fun w _ => (CCCard_ofFlatType_dec_time sig w, tt))). 
Proof.
  extract. solverec. unfold CCCard_ofFlatType_dec_time, c__CCCardOfFlatTypeDec. nia.
Qed. 

Definition c__CCCardOfFlatTypeDecBound := 2 * (c__CCCardOfFlatTypeDec + 1).
Definition poly__CCCardOfFlatTypeDec n := (poly__listOfFlatTypeDec n + 1) * c__CCCardOfFlatTypeDecBound.
Lemma CCCard_ofFlatType_dec_time_bound sig w : CCCard_ofFlatType_dec_time sig w <= poly__CCCardOfFlatTypeDec (size (enc sig) + size (enc w)).
Proof. 
  unfold CCCard_ofFlatType_dec_time. rewrite !list_ofFlatType_dec_time_bound. 
  unfold poly__CCCardOfFlatTypeDec.
  poly_mono list_ofFlatType_dec_poly at 2.
  2: (replace_le (size (enc (conc w))) with (size (enc w)) by (rewrite CCCard_enc_size; lia)); reflexivity.
  poly_mono list_ofFlatType_dec_poly at 1.
  2: (replace_le (size (enc (prem w))) with (size (enc w)) by (rewrite CCCard_enc_size; lia)); reflexivity.
  unfold c__CCCardOfFlatTypeDecBound. nia. 
Qed. 
Lemma CCCard_ofFlatType_dec_poly : monotonic poly__CCCardOfFlatTypeDec /\ inOPoly poly__CCCardOfFlatTypeDec. 
Proof. 
  split; unfold poly__CCCardOfFlatTypeDec; smpl_inO; apply list_ofFlatType_dec_poly.  
Qed. 

(** isValidFlattening_dec *)
Definition c__isValidFlatteningDec := 3 * c__Sigma + c__init + c__final + c__cards + 16.
Definition isValidFlattening_dec_time x := list_ofFlatType_dec_time (Sigma x) (init x) + forallb_time (list_ofFlatType_dec_time (Sigma x)) (final x)+ forallb_time (CCCard_ofFlatType_dec_time (Sigma x)) (cards x) + c__isValidFlatteningDec.
#[export]
Instance term_isValidFlattening_dec : computableTime' isValidFlattening_dec (fun fpr _ => (isValidFlattening_dec_time fpr, tt)).
Proof.
  extract. solverec. unfold isValidFlattening_dec_time, c__isValidFlatteningDec.
  repeat change (fun x => ?h x) with h. solverec. 
Qed. 

Definition c__isValidFlatteningDecBound := 2 * c__forallb + c__isValidFlatteningDec. 
Definition poly__isValidFlatteningDec n :=(n + 2) * poly__listOfFlatTypeDec n + (n + 1) * poly__CCCardOfFlatTypeDec n + (n + 1) * c__isValidFlatteningDecBound. 
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
    - rewrite CCCard_ofFlatType_dec_time_bound, Nat.add_comm; reflexivity. 
    - apply CCCard_ofFlatType_dec_poly. 
  }

  rewrite !list_size_length. 
  poly_mono list_ofFlatType_dec_poly at 1. 
  2: (replace_le (size (enc (Sigma fpr)) + size (enc (init fpr))) with (size (enc fpr)) by (rewrite FlatCC_enc_size; lia)); reflexivity. 
  poly_mono list_ofFlatType_dec_poly at 2. 
  2: (replace_le (size (enc (final fpr)) + size (enc (Sigma fpr))) with (size (enc fpr)) by (rewrite FlatCC_enc_size; lia)); reflexivity. 
  replace_le (size (enc (final fpr))) with (size (enc fpr)) by (rewrite FlatCC_enc_size; lia) at 1. 
  replace_le (size (enc (cards fpr))) with (size (enc fpr)) by (rewrite FlatCC_enc_size; lia) at 1. 
  poly_mono CCCard_ofFlatType_dec_poly at 1. 
  2: (replace_le (size (enc (cards fpr)) + size (enc (Sigma fpr))) with (size (enc fpr)) by (rewrite FlatCC_enc_size; lia)); reflexivity. 
  unfold poly__isValidFlatteningDec, c__isValidFlatteningDecBound. nia.
Qed. 
Lemma isValidFlatteningDec_poly : monotonic poly__isValidFlatteningDec /\ inOPoly poly__isValidFlatteningDec. 
Proof. 
  split; (unfold poly__isValidFlatteningDec; smpl_inO; [apply list_ofFlatType_dec_poly |apply CCCard_ofFlatType_dec_poly ]). 
Qed. 
