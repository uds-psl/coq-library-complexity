From Undecidability.Shared.Libs.PSL Require Import Base FinTypes. 
From Undecidability.Shared.Libs.PSL Require Import Vectors.Vectors. 
From Complexity.Libs.CookPrelim Require Import MorePrelim FlatFinTypes.
From Complexity.NP.SAT.CookLevin Require Import FlatTCC FlatCC TCC_to_CC.

Require Import Lia.

(** * Reduction of FlatTCC to FlatCC*)

(** ** Definition of reduction *)

(**We can completely re-use the construction and correctness results of the TCC-CC reduction,
   as the reduction does not depend on the alphabet being finite.
*)
Definition FCC_instance (ftpr : FlatTCC) := 
  Build_FlatCC (FlatTCC.Sigma ftpr) 1 3 (FlatTCC.init ftpr) (CC_cards (FlatTCC.cards ftpr)) 
    (FlatTCC.final ftpr) (FlatTCC.steps ftpr).

Local Open Scope cc_scope. 
Lemma FlatTCC_to_FlatCC (ftpr : FlatTCC) : FlatTCCLang ftpr <-> FlatCCLang (FCC_instance ftpr). 
Proof. 
  split; intros. 
  - destruct H as (H & H0 & sf & H1 & H2 & H3). split; [ | split; [ | exists sf; repeat split]].
    + unfold FlatTCC_wellformed in H. unfold FlatCC_wellformed. cbn in *. unfold CC_cards.
      repeat split; try lia.   
      * exists 3. split; easy.  
      * apply in_map_iff in H4 as (card' & <- & H4). 
        destruct card', prem, conc; cbn in *. easy.  
      * apply in_map_iff in H4 as (card' & <- & H4). 
        destruct card', prem, conc; cbn in *. easy.  
      * setoid_rewrite Nat.mul_1_r. eauto. 
    + destruct H0 as (F1 & F2 & F3). repeat split. 
      * apply F1. 
      * apply F2. 
      * cbn in H0. unfold CC_cards in H0. 
        apply in_map_iff in H0 as (card' & <- & H0). cbn. destruct card', prem, conc; cbn.
        apply F3 in H0. destruct H0 as ((G1 & G2 & G3) & _). unfold list_ofFlatType; intros. cbn in *.
        repeat match goal with 
          |[H : ?a \/ ?b |- _] => destruct H
          | [H : False |- _] => destruct H
        end; subst; eauto.  
      * cbn in H0. unfold CC_cards in H0. 
        apply in_map_iff in H0 as (card' & <- & H0). cbn. destruct card', prem, conc; cbn.
        apply F3 in H0. destruct H0 as (_ & (G1 & G2 & G3)). unfold list_ofFlatType; intros. cbn in *.
        repeat match goal with 
          |[H : ?a \/ ?b |- _] => destruct H
          | [H : False |- _] => destruct H
        end; subst; eauto.  
    + apply H1. 
    + clear H1 H3. cbn in *. apply relpower_valid_agree, H2. apply H. 
    + apply final_agree, H3. now apply TCC.relpower_valid_length_inv in H2. 
  - destruct H as (H & H0 & sf & H1 & H2 & H3). split; [ | split; [ | exists sf; repeat split]].
    + clear H1 H2 H3. destruct H as (_ & _ & _ & F0 & _ & _).  
      unfold FlatTCC_wellformed. easy.  
    + clear H1 H2 H3. destruct H0 as (F1 & F2 & F3).
      split; [ | split]. 
      * cbn in F1; apply F1. 
      * cbn in F2. unfold FlatTCC.isValidFlatFinal. apply F2. 
      * intros [prem conc]. specialize (F3 (Build_CCCard prem conc)). 
        cbn in F3. intros H1. unfold CC_cards in F3. rewrite in_map_iff in F3. 
        assert (exists x, TCCCard_to_CCCard x = Build_CCCard prem conc /\ x el FlatTCC.cards ftpr) as H2. 
        { exists (prem / conc). cbn. eauto. }
        apply F3 in H2. destruct H2 as (H2 & H3). destruct prem, conc. cbn in *. 
        unfold list_ofFlatType in H2, H3. unfold ofFlatType in *. repeat split; cbn; eauto. 
    + apply H1. 
    + clear H1 H3. cbn in H2. apply relpower_valid_agree, H2. apply H. 
    + eapply final_agree, H3. now apply relpower_valid_length_inv in H2. 
Qed. 

(** ** extraction *)
From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Import  LProd LOptions.
From Complexity.Libs.CookPrelim Require Import PolyBounds. 


Section fixX. 
  Variable (X : Type).
  Context `{X_encodable: encodable X}.

  (** extraction of TCCCard_to_CCCard *)
  Definition c__TCCCardToCCCard := FlatTCC.cnst_prem + 2 * c__TCCCardPToList + FlatTCC.cnst_conc + 3.
  Global Instance term_TCCCard_to_CCCard : computableTime' (@TCCCard_to_CCCard X) (fun _ _ => (c__TCCCardToCCCard, tt)). 
  Proof. 
    extract. unfold c__TCCCardToCCCard. solverec. 
  Defined. 

  Definition c__TCCCardToCCCardSize := c__listsizeCons * 6 + c__listsizeNil *2. 
  Lemma TCCCard_to_CCCard_size (w : TCCCard X): size (enc (TCCCard_to_CCCard w)) <= size (enc (w)) + c__TCCCardToCCCardSize. 
  Proof. 
    unfold TCCCard_to_CCCard, c__TCCCardToCCCardSize. rewrite CCCard_enc_size. 
    rewrite TCCCard_enc_size. destruct w. destruct prem, conc.
    rewrite !size_list. rewrite !TCCCardP_enc_size. cbn -[Nat.add Nat.mul]. nia.
  Qed. 

  (** extraction of CC_cards *)
  Definition c__CCCards := 2.
  Definition CC_cards_time (w : list (TCCCard X)) := map_time (fun _ : TCCCard X => c__TCCCardToCCCard) w + c__CCCards.
  Global Instance term_CC_cards : computableTime' (@CC_cards X) (fun w _ => (CC_cards_time w, tt)).
  Proof. 
    extract. solverec. unfold CC_cards_time, c__CCCards; solverec.
  Defined. 

  Definition c__CCCardsBound := (c__TCCCardToCCCard + 1) * (c__map + 1).
  Definition poly__CCCards n := (n+1) * c__CCCardsBound + c__CCCards. 
  Lemma CC_cards_time_bound w : CC_cards_time w <= poly__CCCards (size (enc w)). 
  Proof. 
    unfold CC_cards_time. unfold poly__CCCards, c__CCCardsBound. 
    rewrite (map_time_bound_env (Y := unit) (X := (TCCCard X)) (fT := fun _ _ => c__TCCCardToCCCard) (f__bound := fun n => c__TCCCardToCCCard)).
    3: easy. 
    2: { 
      split.
      - intros _ _. reflexivity. 
      - smpl_inO.
    }
    rewrite list_size_length. nia. 
  Qed. 

  Lemma CCCards_poly : monotonic poly__CCCards /\ inOPoly poly__CCCards. 
  Proof. 
    split; unfold poly__CCCards; smpl_inO. 
  Qed. 

  Definition CC_cards_size (w : list (TCCCard X)): size (enc (CC_cards w)) <= size (enc (w)) + (|w|) * c__TCCCardToCCCardSize. 
  Proof. 
    unfold CC_cards. rewrite size_list. 
    induction w; cbn -[Nat.add Nat.mul]. 
    - easy. 
    - rewrite <- Nat.add_assoc. rewrite IHw. rewrite TCCCard_to_CCCard_size. 
      rewrite list_size_cons. nia.
  Qed. 
End fixX. 

(** extraction of FCC_instance *)

Definition c__FCC_instance :=  FlatTCC.c__Sigma + FlatTCC.c__init + FlatTCC.c__cards + FlatTCC.c__final + FlatTCC.c__steps + 12.
Definition FCC_instance_time (fpr : FlatTCC) := c__FCC_instance + CC_cards_time (FlatTCC.cards fpr).
Instance term_FCC_instance : computableTime' FCC_instance (fun fpr _ => (FCC_instance_time fpr, tt)). 
Proof. 
  extract. solverec. unfold FCC_instance_time, c__FCC_instance. solverec. 
Defined. 

Lemma FlatTCC_to_FlatCC_poly : FlatTCCLang ⪯p FlatCCLang.
Proof. 
  apply reducesPolyMO_intro with (f := FCC_instance).
  - exists (fun n => c__FCC_instance + poly__CCCards n).  
    + extract. solverec. rewrite CC_cards_time_bound. 
      poly_mono CCCards_poly. 
      2: (replace_le (size (enc (FlatTCC.cards x))) with (size (enc x)) by (rewrite FlatTCC_enc_size; lia)); reflexivity. unfold c__FCC_instance; lia. 
    + smpl_inO. apply CCCards_poly. 
    + smpl_inO. apply CCCards_poly. 
    + evar (f : nat -> nat). exists f. repeat split.
      * intros fpr. unfold FCC_instance. rewrite FlatCC_enc_size; cbn. 
        rewrite CC_cards_size. rewrite list_size_length. 
        rewrite (size_nat_enc 1). rewrite (size_nat_enc 3). 
        instantiate (f := fun n => (1 + c__TCCCardToCCCardSize) * n + 4 * c__natsizeS + 2 * c__natsizeO + 9). subst f. 
        rewrite FlatTCC_enc_size. cbn -[Nat.add Nat.mul]. nia.
      * subst f. smpl_inO. 
      * subst f. smpl_inO. 
  - apply FlatTCC_to_FlatCC. 
Qed. 
