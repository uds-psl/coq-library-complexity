From Complexity.L.Complexity Require Import MorePrelim Problems.Cook.FlatCC FlatFinTypes. 
From Complexity.L.Complexity.Problems.Cook Require Export TCC.
From Undecidability.Shared.Libs.PSL Require Import Base FinTypes. 
Require Import Lia.

(** * Flat 3-Covering Cards *)
(** ** Definition *)
Inductive FlatTCC := {
  Sigma : nat;
  init : list nat;
  cards : list (TCCCard nat);
  final : list (list nat);
  steps : nat
  }.

Definition TCCCardP_ofFlatType (cardp : TCCCardP nat) (k : nat) := cardEl1 cardp < k /\ cardEl2 cardp < k /\ cardEl3 cardp < k.
Definition TCCCard_ofFlatType (card : TCCCard nat) (k : nat) := TCCCardP_ofFlatType (prem card) k /\ TCCCardP_ofFlatType (conc card) k. 

Definition isValidFlatCards (l : list (TCCCard nat)) k := (forall card, card el l -> TCCCard_ofFlatType card k).
Definition isValidFlatFinal (l : list (list nat)) k := (forall s, s el l -> list_ofFlatType k s).
Definition isValidFlatInitial (l : list nat) k := list_ofFlatType k l.

(** well-formedness is defined similarly to TCC *)
Definition FlatTCC_wellformed ftpr := length (init ftpr) >= 3.

Definition isValidFlattening ftpr :=
  isValidFlatInitial (init ftpr) (Sigma ftpr)
  /\ isValidFlatFinal (final ftpr) (Sigma ftpr)
  /\ isValidFlatCards (cards ftpr) (Sigma ftpr). 

Definition FlatTCCLang (C : FlatTCC) :=
  FlatTCC_wellformed C /\ isValidFlattening C
  /\ exists (sf : list nat), list_ofFlatType  (Sigma C) sf
                     /\ relpower (valid (coversHeadList (cards C))) (steps C) (init C) sf
                     /\ satFinal (final C) sf.

(** ** Relation to TCC instances *)
(** We can define a relation to TCC instances such that TCC instances and FlatTCC instances are equivalent *)
Inductive isFlatTCCCardPOf (X : finType) (flatcardp : TCCCardP nat) (cardp : TCCCardP X) := 
  mkIsFlatTCCCardPOf (Helem1 : finReprEl' (cardEl1 flatcardp) (cardEl1 cardp))
    (Helem2 : finReprEl' (cardEl2 flatcardp) (cardEl2 cardp))
    (Helem3 : finReprEl' (cardEl3 flatcardp) (cardEl3 cardp))
  : isFlatTCCCardPOf flatcardp cardp. 

Inductive isFlatTCCCardOf (X : finType) (flatcard : TCCCard nat) (card : TCCCard X) := 
  mkIsFlatTCCCardOf (Hprem : isFlatTCCCardPOf (prem flatcard) (prem card)) 
    (Hconc : isFlatTCCCardPOf (conc flatcard) (conc card))
  : isFlatTCCCardOf flatcard card. 

Inductive isFlatTCardsOf (X : finType) (flatcards : list (TCCCard nat)) (cards : list (TCCCard X)) := 
  mkIsFlatCardsOf (Hsound : forall flatcard, flatcard el flatcards -> exists card, card el cards /\ isFlatTCCCardOf flatcard card)
    (Hcomplete : forall card, card el cards -> exists flatcard, flatcard el flatcards /\ isFlatTCCCardOf flatcard card)
  : isFlatTCardsOf flatcards cards. 

Inductive isFlatTCCOf (fpr : FlatTCC) (pr : TCC) := 
  mkIsFlatTCCOf (HSigma : finRepr (TCC.Sigma pr) (Sigma fpr))
    (HInit : isFlatListOf (init fpr) (TCC.init pr))
    (HCards : isFlatTCardsOf (cards fpr) (TCC.cards pr))
    (HFinal : isFlatFinalOf (final fpr) (TCC.final pr))
    (Hsteps : steps fpr = TCC.steps pr)
  : isFlatTCCOf fpr pr.

(*proof of agreement *)
Lemma isFlatTCCCardOf_map_index (X : finType) (card : TCCCard X) card' :
  isFlatTCCCardOf card' card -> (prem card' : list nat) = map index (prem card) /\ (conc card' : list nat) = map index (conc card). 
Proof. 
  intros ([H1 H2 H3] & [F1 F2 F3]). 
  destruct card. destruct prem, conc. cbn in *. 
  repeat match goal with
          | [H : finReprEl' _ _ |- _] => unfold finReprEl' in H; rewrite H; clear H
  end. 
  destruct card', prem, conc. now cbn. 
Qed. 

Lemma coversHeadList_flat_agree (X : finType) (cardsFin : list (TCCCard X)) cardsFlat finStr finStr' flatStr flatStr' :
  isFlatListOf flatStr finStr
  -> isFlatListOf flatStr' finStr'
  -> isFlatTCardsOf cardsFlat cardsFin 
  -> (coversHeadList cardsFin finStr finStr' <-> coversHeadList cardsFlat flatStr flatStr'). 
Proof. 
  intros. unfold coversHeadList. split; intros (card & H2 & H3).
  - apply H1 in H2 as (card' & F1 & F2). exists card'. split; [apply F1 | ]. 
    unfold coversHead, prefix in *. destruct H3 as ((b1 & ->) & (b2 & ->)). 
    unfold isFlatListOf in H, H0.
    rewrite map_app in H, H0. split.
    + exists (map index b1). rewrite H. enough (map index (prem card) = prem card') as H2.
      { now setoid_rewrite H2. }
      destruct card; cbn. destruct prem. 
      apply isFlatTCCCardOf_map_index in F2. 
      rewrite (proj1 F2). now cbn. 
    + exists (map index b2). rewrite H0. enough (map index (conc card) = conc card') as H2. 
      { now setoid_rewrite H2. }
      destruct card; cbn. destruct conc.
      apply isFlatTCCCardOf_map_index in F2.
      rewrite (proj2 F2). now cbn. 
  - apply H1 in H2 as (card' & F1 & F2). exists card'. split; [ apply F1 | ].
    unfold coversHead, prefix in *. destruct H3 as ((b1 & ->) & (b2 & ->)).
    unfold isFlatListOf in H, H0. split.
    + symmetry in H. apply map_eq_app in H as (finStr1  & finStr2 & -> & ? & ?). 
      exists finStr2.
      enough (finStr1 = prem card') as H3 by (now setoid_rewrite H3).
      apply isFlatTCCCardOf_map_index in F2. destruct F2 as (F2 & _). rewrite F2 in H. 
      apply map_injective in H; [easy | unfold injective; apply injective_index]. 
    + symmetry in H0. apply map_eq_app in H0 as (finStr1  & finStr2 & -> & ? & ?). 
      exists finStr2.
      enough (finStr1 = conc card') as H3 by (now setoid_rewrite H3).
      apply isFlatTCCCardOf_map_index in F2. destruct F2 as (_ & F2). rewrite F2 in H0. 
      apply map_injective in H0; [easy | unfold injective; apply injective_index].
Qed.

Lemma valid_flat_agree (X : finType) (cards : list (TCCCard X)) fcards s1 s2 fs1 fs2: 
  isFlatListOf fs1 s1 
  -> isFlatListOf fs2 s2
  -> isFlatTCardsOf fcards cards 
  -> valid (coversHeadList fcards) fs1 fs2 <-> valid (coversHeadList cards) s1 s2. 
Proof. 
  intros H H1 H2. 
  split.
  - intros H3. revert s1 s2 H H1. induction H3 as [ | a b x y H IH H4 | a b x y H IH H4]; intros s1 s2 H0 H1. 
    + destruct s1; [ | now unfold isFlatListOf in H0]. 
      destruct s2; [ | now unfold isFlatListOf in H1].
      constructor. 
    + unfold isFlatListOf in H0, H1. 
      destruct s1; cbn [map] in H0; [ congruence | ].
      destruct s2; cbn [map] in H1; [congruence | ]. 
      inv H0; inv H1. constructor 2. 
      2: now rewrite map_length in H4. apply IH; easy. 
    + unfold isFlatListOf in H0, H1.
      destruct s1; cbn [map] in H0; [ congruence | ].
      destruct s2; cbn [map] in H1; [congruence | ]. 
      inv H0; inv H1. constructor 3. 
      * eapply IH; easy.
      * eapply coversHeadList_flat_agree. all: easy. 
  - intros H3. revert fs1 fs2 H H1 H2. induction H3 as [ | a b x y H IH H2 | a b x y H IH H2]; intros fs1 fs2 H0 H1. 
    + rewrite H0, H1; cbn; constructor 1.  
    + rewrite H1, H0. cbn [map]. constructor.
      * now eapply IH.
      * rewrite map_length. auto.
    + rewrite H1, H0. cbn [map]. constructor 3. 
      * now eapply IH.
      * eapply coversHeadList_flat_agree in H2. all: easy. 
Qed. 

Lemma valid_flat_isFlatListOf_invariant (X : finType) (cards : list (TCCCard X)) fcards (s1 : list X) fs1 fs2: 
  isFlatTCardsOf fcards cards 
  -> isFlatListOf fs1 s1
  -> |fs1| >= 3
  -> valid (coversHeadList fcards) fs1 fs2
  -> exists (s2 : list X), isFlatListOf fs2 s2. 
Proof. 
  intros. revert s1 H0. induction H2 as [ | a b x y H0 IH H3 | a b x y H0 IH H3]; intros.
  - cbn in H1; lia.
  - cbn in H1; lia. 
  - cbn in H1. destruct s1; [unfold isFlatListOf in H2; cbn in H2; congruence | ].  
    apply isFlatListOf_cons in H2 as (H2' & H2). 
    destruct H3 as (card & (H3 & (_ & (c & H4)))). 
    destruct (le_lt_dec 3 (|a|)). 
    + eapply IH in l as (s2 & H5); [ | apply H2]. clear IH. 
      apply H in H3 as (card' & _ & (_ & [F1 F2 F3])). destruct (conc card). cbn in *.
      inv H4. exists (TCC.cardEl1 (conc card') :: s2). 
      apply isFlatListOf_cons. easy.
    + clear IH. apply valid_length_inv in H0. 
      apply H in H3 as (card' & _ & (_ & [F1 F2 F3])).
      destruct conc. 
      assert (c = []) as ->. { destruct c; [ easy | ]. cbn in H4. inv H4. cbn in H0. lia. }
      cbn in H4. inv H4. 
      destruct conc; cbn in *. 
      exists [cardEl0; cardEl4; cardEl5]. unfold isFlatListOf; cbn. 
      unfold finReprEl' in *. rewrite <- F1, <- F2, <- F3. easy.
Qed. 

Lemma relpower_valid_flat_agree (X : finType) (cards : list (TCCCard X)) fcards s1 s2 fs1 fs2 n:
  |fs1| >= 3
  -> isFlatListOf fs1 s1
  -> isFlatListOf fs2 s2
  -> isFlatTCardsOf fcards cards
  -> relpower (valid (coversHeadList fcards)) n fs1 fs2 <-> relpower (valid (coversHeadList cards)) n s1 s2.
Proof. 
  intros H0 H1 H2 H3. split.
  - intros H4. revert s1 s2 H1 H2. induction H4 as [ ? | ? ? ? ? H H4 IH]; intros s1 s2 H1 H2. 
    + specialize (isFlatListOf_functional H1 H2) as ->. eauto.
    + specialize (valid_flat_isFlatListOf_invariant H3 H1 H0 H) as (s3 & H5).  
      specialize (valid_length_inv H) as H6. rewrite H6 in H0. 
      specialize (IH H0  _ _ H5 H2). 
      econstructor. 
      * apply (valid_flat_agree H1 H5 H3) in H. apply H. 
      * apply IH. 
  - intros H4. clear H0. 
    revert fs1 fs2 H1 H2. induction H4 as [ ? | ? ? ? ? H H0 IH]; intros fs1 fs2 H1 H2. 
    + specialize (isFlatListOf_injective H1 H2) as ->. constructor. 
    + assert (isFlatListOf (map index b) b) as H4 by (unfold isFlatListOf; easy).
      specialize (IH _ _ H4 H2). apply (valid_flat_agree H1 H4 H3) in H. eauto. 
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

Lemma isFlatTCCOf_isValidFlattening (tpr : TCC) (ftpr : FlatTCC) : isFlatTCCOf ftpr tpr -> isValidFlattening ftpr. 
Proof. 
  intros [H1 H2 H3 H4].
  split; [ | split]. 
  + unfold isValidFlatInitial, list_ofFlatType. rewrite H2. 
    intros a. rewrite in_map_iff. intros (a' & <- & F1).
    unfold ofFlatType. rewrite H1. apply index_le. 
  + intros s H0%H4. destruct H0 as (s' & F1 & ->).
    intros a. rewrite in_map_iff. intros (a' & <- & F3). 
    rewrite H1. apply index_le. 
  + intros card H0%H3. destruct H0 as (card' & F1 & F2). 
    destruct F2 as ([F2 F3 F4] & [F5 F6 F7]).
    repeat split; rewrite H1; unfold finReprEl' in *;
    repeat match goal with [H : index _ = _ |- _] => try rewrite <- H; clear H end;
    apply index_le.  
Qed.

Lemma isFlatTCCOf_wf_equivalent (tpr : TCC) (ftpr : FlatTCC) : 
  isFlatTCCOf ftpr tpr -> (FlatTCC_wellformed ftpr <-> TCC_wellformed tpr). 
Proof. 
  intros [H1 H2 H3 H4]. split; intros; unfold FlatTCC_wellformed, TCC_wellformed in *.
  - rewrite H2 in H. now rewrite map_length in H.  
  - rewrite H2. rewrite map_length; apply H. 
Qed. 

Lemma isFlatTCCOf_equivalence (tpr : TCC) (ftpr : FlatTCC) : 
  isFlatTCCOf ftpr tpr -> (FlatTCCLang ftpr <-> TCCLang tpr). 
Proof. 
  intros. split. 
  - intros (H1 & H2 & H3). split; [ now eapply isFlatTCCOf_wf_equivalent | ]. 
    destruct H as [F1 F2 F3 F4 F5].
    destruct H3 as (sf & H3 & H4 & H5).
    apply (finRepr_exists_list F1) in H3 as (SF & H3).
    exists SF. split. 
    + eapply relpower_valid_flat_agree; eauto. rewrite <- F5. apply H4.    
    + eapply final_flat_agree; eauto.
  - intros (H1 & H2). split; [ now eapply isFlatTCCOf_wf_equivalent | ]. 
    split; [now eapply isFlatTCCOf_isValidFlattening | ].
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

(** ** Mapping FlatTCC instances to canonical TCC instances *)
(** from a flat instance, we can restore a canonical non-flat instance *)

Require Import Undecidability.Shared.Libs.PSL.FiniteTypes.VectorFin Undecidability.Shared.Libs.PSL.FiniteTypes.Cardinality. 
Lemma unflattenTCCCardP (w : TCCCardP nat) k : 
  TCCCardP_ofFlatType w k -> sigT (fun (w' : TCCCardP (finType_CS (Fin.t k))) => isFlatTCCCardPOf w w'). 
Proof. 
  intros. destruct w. destruct H as (H1 & H2 & H3). cbn in *.
  assert (finRepr (finType_CS (Fin.t k)) k). 
  { unfold finRepr. specialize (Fin_cardinality k) as H4. unfold Cardinality in H4. easy. }
  eapply (finRepr_exists H) in H1 as (a1 & H1).  
  eapply (finRepr_exists H) in H2 as (a2 & H2). 
  eapply (finRepr_exists H) in H3 as (a3 & H3). 
  exists (Build_TCCCardP a1 a2 a3). repeat split; eapply finReprEl_finReprEl'; easy.
Qed. 

Lemma unflattenCarddow (w : TCCCard nat) k : 
  TCCCard_ofFlatType w k -> sigT (fun (w' : TCCCard (finType_CS (Fin.t k))) => isFlatTCCCardOf w w'). 
Proof. 
  intros. destruct w. destruct H as (H1 & H2). cbn in *.
  apply unflattenTCCCardP in H1 as (prem' & H1). 
  apply unflattenTCCCardP in H2 as (conc' & H2).
  exists (Build_TCCCard prem' conc'). split; easy.
Qed. 

Lemma unflattenCards (l : list (TCCCard nat)) k : 
  isValidFlatCards l k -> sigT (fun (l' : list (TCCCard (finType_CS (Fin.t k)))) => isFlatTCardsOf l l').  
Proof. 
  intros. unfold isValidFlatCards in H. induction l. 
  - exists []. easy.
  - edestruct IHl as (l' & IH);[ easy | ]. specialize (H a (or_introl eq_refl)). 
    apply unflattenCarddow in H as (a' & H). exists (a' :: l'). split; intros.
    + destruct H0 as [-> | H0]; [easy | ]. apply IH in H0 as (card & ? & ?); eauto.
    + destruct H0 as [-> | H0]; [ easy | ]. apply IH in H0 as (card' & ? & ?); eauto.
Qed. 

Lemma unflattenString (f : list nat) k : 
  list_ofFlatType k f -> sigT (fun (f' : list (finType_CS (Fin.t k))) => isFlatListOf f f'). 
Proof. 
  intros H. 
  eapply finRepr_exists_list with (X := finType_CS (Fin.t k)) in H as (a' & H). 
  2: { unfold finRepr. specialize (Fin_cardinality k). easy. }
  eauto.
Qed. 

Lemma unflattenFinal (f : list (list nat)) k : 
  isValidFlatFinal f k -> sigT (fun (f' : list (list (finType_CS (Fin.t k)))) => isFlatFinalOf f f'). 
Proof. 
  intros. unfold isValidFlatFinal in H. induction f; intros.
  - exists []; easy.
  - edestruct IHf as (f' & IH); [easy | ]. specialize (H a (or_introl eq_refl)). 
    apply unflattenString in H as (a' &H).
    exists (a'::f'). split; intros. 
    + destruct H0 as [-> | H0]; [easy | ]. apply IH in H0 as (? & ? & ?); eauto.
    + destruct H0 as [-> | H0]; [easy | ]. apply IH in H0 as (? & ? & ?); eauto.
Qed. 

Lemma unflattenTCC (f : FlatTCC) : isValidFlattening f -> sigT (fun (f' : TCC) => isFlatTCCOf f f'). 
Proof. 
  intros (H1 & H2 & H3).
  apply unflattenCards in H3 as (w' & H3). 
  apply unflattenFinal in H2 as (f' & H2). 
  apply unflattenString in H1 as (i' & H1). 
  exists (Build_TCC i' w' f' (steps f)). 
  constructor; eauto.
  cbn. unfold finRepr. specialize (Fin_cardinality (Sigma f)). easy.
Qed.

(** ** extraction *)

From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Import  LProd LOptions.

Section fix_X.
  Variable (X:Type).
  Context `{X_encodable: encodable X}.

  (** TCCCardP *)
  MetaCoq Run (tmGenEncode "TCCCardP_enc" (TCCCardP X)).
  Hint Resolve TCCCardP_enc_correct : Lrewrite.

  Global Instance term_Build_TCCCardP : computableTime' (@Build_TCCCardP X) (fun _ _ => (1, fun _ _ => (1, fun _ _ => (1, tt)))). 
  Proof. 
    extract constructor. solverec. 
  Defined. 

  Definition cnst_cardEl1 := 6. 
  Global Instance term_cardEl1 : computableTime' (@cardEl1 X) (fun _ _ => (cnst_cardEl1, tt)). 
  Proof. 
    extract. unfold cnst_cardEl1. solverec. 
  Defined. 

  Definition cnst_cardEl2 := 6. 
  Global Instance term_cardEl2 : computableTime' (@cardEl2 X) (fun _ _ => (cnst_cardEl2, tt)). 
  Proof. 
    extract. unfold cnst_cardEl2. solverec. 
  Defined. 

  Definition cnst_cardEl3 := 6. 
  Global Instance term_cardEl3 : computableTime' (@cardEl3 X) (fun _ _ => (cnst_cardEl3, tt)). 
  Proof. 
    extract. unfold cnst_cardEl3. solverec. 
  Defined. 

  Definition c__sizeTCCCardP := 5. 
  Lemma TCCCardP_enc_size (w : TCCCardP X) : size (enc w) = size (enc (cardEl1 w)) + size (enc (cardEl2 w)) + size (enc (cardEl3 w)) + c__sizeTCCCardP. 
  Proof. 
    destruct w. cbn. unfold enc at 1; unfold c__sizeTCCCardP; cbn. nia. 
  Qed. 

  (** extraction of TCCCardP_to_list *)
  Definition c__TCCCardPToList := 12.
  Global Instance term_TCCCardP_to_list : computableTime' (@TCCCardP_to_list X) (fun _ _ => (c__TCCCardPToList, tt)).
  Proof. 
    extract. unfold c__TCCCardPToList. solverec. 
  Defined. 

  (** TCCCard*)
  MetaCoq Run (tmGenEncode "TCCCard_enc" (TCCCard X)). 
  Hint Resolve TCCCard_enc_correct : Lrewrite.

  Global Instance term_Build_TCCCard : computableTime' (@Build_TCCCard X) (fun _ _ => (1, fun _ _ => (1, tt))).
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

  Definition c__sizeTCCCard := 4.
  Lemma TCCCard_enc_size (card : TCCCard X) : size (enc card) = size (enc (prem card)) + size (enc (conc card)) + c__sizeCCCard.
  Proof. 
    destruct card. cbn. unfold enc at 1;unfold  c__sizeCCCard. cbn. nia.
  Qed. 
End fix_X. 

Hint Resolve TCCCardP_enc_correct : Lrewrite.
Hint Resolve TCCCard_enc_correct : Lrewrite.

MetaCoq Run (tmGenEncode "FlatTCC_enc" (FlatTCC)).
Hint Resolve FlatTCC_enc_correct : Lrewrite. 

From Complexity.L.Complexity Require Import PolyBounds. 

Instance term_Build_FlatTCC : computableTime' Build_FlatTCC (fun _ _ => (1, fun _ _ => (1, fun _ _ => (1, fun _ _ => (1, fun _ _ => (1, tt)))))).
Proof.
  extract constructor. solverec. 
Defined. 

Definition c__Sigma := 8.
Instance term_FlatTCC_Sigma : computableTime' Sigma (fun _ _ => (c__Sigma, tt)). 
Proof.
  extract. unfold c__Sigma. solverec. 
Defined. 

Definition c__init := 8.
Instance term_FlatTCC_init : computableTime' init (fun _ _ => (c__init, tt)). 
Proof. 
  extract. unfold c__init. solverec. 
Defined. 

Definition c__cards := 10.
Instance term_FlatTCC_cards : computableTime' cards (fun _ _ => (c__cards, tt)). 
Proof. 
  extract. unfold c__cards. solverec. 
Defined. 

Definition c__final := 10.
Instance term_FlatTCC_final : computableTime' final (fun _ _ => (c__final, tt)). 
Proof. 
  extract. unfold c__final. solverec. 
Defined. 

Definition c__steps := 10.
Instance term_FlatTCC_steps : computableTime' steps (fun _ _ => (c__steps, tt)). 
Proof. 
  extract. unfold c__steps. solverec. 
Defined. 

Definition c__sizeFlatTCC := 7.
Lemma FlatTCC_enc_size (fpr : FlatTCC) : size (enc fpr) = size (enc (Sigma fpr)) + size (enc (init fpr)) + size (enc (cards fpr)) + size (enc (final fpr)) + size (enc (steps fpr)) + c__sizeFlatTCC.
Proof. 
  destruct fpr. cbn. unfold enc at 1. cbn. unfold c__sizeFlatTCC. nia.
Qed. 


