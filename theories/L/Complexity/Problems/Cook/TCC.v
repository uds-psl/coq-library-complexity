From PslBase Require Import Base. 
From PslBase Require Import FiniteTypes. 
From Complexity.L.Complexity Require Import MorePrelim.
Require Import Lia.

(** * 3-Covering Cards *)
(** We define a variant of Covering Cards where the width is fixed to 3 and the offset is fixed to 1. 
  The resulting specialised definitions make the reduction from Turing machines easier to construct.

Moreover, we generalise the definition of CC-steps (here called "valid") to arbitrary coversHead predicates. 
This allows us to define the reduction from Turing machines using inductive predicates. 
The list-based version (with a set of cards given as a list) is obtained as a special case.

To that end, we define two variants of 3-CC in this file:
- the usual variant (TCC) which is based on lists of cards
- the propositional variant PTCC over an abstract coversHead predicate 
*)

Section abstractDefs.
  Variable (X : Type). 
  Notation string := (list X). 

  (** We first define some general notions for an arbitrary coversHead predicate *)
  Definition coversHeadAbstract := string -> string -> Prop. 

  Section fixCoversHead.
    Variable (p : coversHeadAbstract). 

    (** coverings inside a string *)
    Definition coversAt (i : nat) a b := p (skipn i a) (skipn i b).
    Lemma coversAt_head a b : p a b <-> coversAt 0 a b. 
    Proof. 
      unfold coversAt.
      rewrite <- firstn_skipn with (n:= 0) (l:= a) at 1.
      rewrite <- firstn_skipn with (n:= 0) (l:= b) at 1.
      repeat rewrite firstn_O; now cbn. 
    Qed. 

    Lemma coversAt_step a b x y (i:nat) : coversAt i a b <-> coversAt (S i) (x :: a) (y:: b). 
    Proof. intros. unfold coversAt. now cbn. Qed. 

    (** validity of a covering *)
    Inductive valid : string -> string -> Prop :=
    | validB: valid [] [] 
    | validSA a b x y: valid a b -> length a < 2 -> valid (x:: a) (y:: b)
    | validS a b x y : valid a b -> p (x::a) (y::b) -> valid (x::a) (y::b). 

    Hint Constructors valid : core. 

    Lemma valid_vacuous a b : |a| <= 2 -> |a| = |b| -> valid a b. 
    Proof. 
      intros. 
      destruct a as [ | a1 a]; [ | destruct a as [ | a2 a]; [ | destruct a; cbn in *; [ | lia]]];
      (destruct b as [ | b1 b]; [ | destruct b as [ | b2 b]; [ | destruct b; cbn in *; [ | lia]]]); 
          cbn in *; try congruence; eauto. 
    Qed. 

    Lemma valid_length_inv a b : valid a b -> length a = length b. 
    Proof. induction 1; cbn; lia. Qed. 

    Lemma relpower_valid_length_inv n a b : relpower valid n a b -> length a = length b. 
    Proof.  induction 1; [solve [eauto] | ]. apply valid_length_inv in H. congruence. Qed. 

    Lemma valid_base (a b c d e f : X) : valid [a; b ; c] [d; e; f] <-> p [a; b; c] [d; e; f]. 
    Proof. 
      split.
      - intros; inv H. cbn in H5; lia. apply H5.  
      - constructor 3. 2: apply H. repeat constructor.
    Qed. 

    (** a different characterisation not allocardg vacuous coverings *)
    (** this is conceptually nicer, but it has the problem that p is used in two cases, which makes some proofs harder *)
    Inductive validDirect : string -> string -> Prop :=
    | validDirectB a b : |a| = 3 -> |b| = 3 -> p a b -> validDirect a b 
    | validDirectS a b x y : validDirect a b -> p (x::a) (y::b) -> validDirect (x::a) (y::b). 

    Lemma validDirect_valid a b : validDirect a b <-> valid a b /\ |a| >= 3. 
    Proof. 
      split. 
      - induction 1 as [a b H0 H1 H2 | a b x y H0 IH H1]. 
        + split; [ | lia]. list_length_inv. eauto 10.
        + destruct IH as [IH H2]. split; [ | cbn; lia]. eauto 10.
      - intros (H1 & H2). induction H1 as [ | a b x y H0 IH H1 | a b x y H0 IH H1]; cbn in H2; [easy | easy | ]. 
        list_length_inv. destruct a. 
        + clear IH. apply valid_length_inv in H0. cbn in H0. constructor; cbn; easy. 
        + constructor 2; [ | apply H1]. apply IH. now cbn. 
    Qed. 

    (** the explicit characterisation using bounded quantification *)
    Definition validExplicit a b := 
      length a = length b 
      /\ forall i, 0 <= i < length a - 2  -> coversAt i a b.

    Lemma valid_iff a b :
      valid a b <-> validExplicit a b.
    Proof.
      unfold validExplicit. split.
      - induction 1. 
        + cbn; split; [reflexivity | ]. 
          intros; lia. 
        + destruct IHvalid as (IH1 & IH2). split; [cbn; congruence | ]. 
          cbn [length]; intros. lia. 
        + destruct IHvalid as (IH1 & IH2); split; [cbn; congruence | ].
          cbn [length]; intros.
          destruct i. 
          * eauto. 
          * assert (0 <= i < (|a|) - 2) by lia. eauto. 
      - revert b. induction a; intros b (H1 & H2). 
        + inv_list. constructor. 
        + inv_list. destruct (le_lt_dec 2 (length a0)). 
          * cbn [length] in H2.
            assert (0 <= 0 < S (|a0|) - 2) by lia. specialize (H2 0 H) as H3. 
            eapply (@validS a0 b a x). 2: assumption. 
            apply IHa. split; [congruence | ]. 
            intros. assert (0 <= S i < S (|a0|) - 2) by lia. 
            specialize (H2 (S i) H4). eauto. 
          * constructor. 
            2: assumption. 
            apply IHa. split; [congruence | intros ]. 
            cbn [length] in H2. assert (0 <= S i < S(|a0|) - 2) by lia. 
            specialize (H2 (S i) H0); eauto. 
    Qed. 
  End fixCoversHead.

  Hint Constructors valid : core. 

  (** valid is congruent with regards to coversHead predicates*)
  Lemma valid_monotonous (p1 p2 : coversHeadAbstract) : (forall x y, p1 x y -> p2 x y) -> forall x y, valid p1 x y -> valid p2 x y.
  Proof. 
    intros H x y. induction 1.  
    - eauto. 
    - constructor 2; eauto. 
    - apply H in H1. eauto. 
  Qed. 

  Corollary valid_congruent p1 p2 : 
    (forall u v, p1 u v <-> p2 u v) 
    -> forall a b, valid p1 a b <-> valid p2 a b.
  Proof.
    intros; split; [apply valid_monotonous; intros; now apply H | ].
    assert (forall u v, p2 u v <-> p1 u v) by (intros; now rewrite H).
    apply valid_monotonous. intros; now apply H. 
  Qed.

End abstractDefs. 

Arguments valid {X}. 
Hint Constructors valid : core. 

Ltac inv_valid := match goal with
                    | [ H : valid _ _ _ |- _] => inv H
                  end;
                  try match goal with
                  | [ H : | _ | < 2 |- _] => now cbn in H
                  end.


(** ** 3-CC using list-based cards *)

(** use an explicit representation instead of vectors of size 3 since this will make the problem closer to the flattened extractable problem *)
Inductive TCCCardP (Sigma : Type) := {
         cardEl1 : Sigma;
         cardEl2 : Sigma;
         cardEl3 : Sigma
       }.

Inductive TCCCard (Sigma : Type) := {
          prem : TCCCardP Sigma;
          conc : TCCCardP Sigma
        }.

Definition TCCCardP_to_list (sig : Type) (a : TCCCardP sig) := match a with Build_TCCCardP a b c => [a; b; c] end. 
Coercion TCCCardP_to_list : TCCCardP >-> list. 

Declare Scope cc_scope. 
Local Open Scope cc_scope.
Notation "'{' a ',' b ',' c '}'" := (Build_TCCCardP a b c) (format "'{' a ',' b ',' c '}'") : cc_scope. 
Notation "a / b" := ({|prem := a; conc := b|}) : cc_scope. 

Record TCC := {
               Sigma : finType;
               init : list Sigma;  (* length is encoded implicitly as the length of init*) 
               cards : list (TCCCard Sigma);
               final : list (list Sigma);
               steps : nat
             }.

Definition TCC_wellformed C := length (init C) >= 3. 

Implicit Type (C : TCC).

(** the final constraint*)
Definition satFinal (X : Type) final (s : list X) := 
  exists subs, subs el final /\ substring subs s.

(** specific definitions and results for list-based cards*)
Section fixInstance.
  Variable (Sigma : Type).
  Variable (init : list Sigma).
  Variable (cards : list (TCCCard Sigma)).
  Variable (final : list (list Sigma)).
  Variable (steps : nat). 

  Notation string := (list Sigma). 
  Notation card := (TCCCard Sigma).

  Implicit Type (s a b: string). 
  Implicit Type (w card : card).
  Implicit Type (x y : Sigma).

  Definition isCard w := w el cards.
  Lemma isRule_length w : length (prem w) = 3 /\ length (conc w) = 3.
  Proof. 
    intros. destruct w. 
    cbn. destruct prem0, conc0. now cbn. 
  Qed. 

  (** we now define a concrete covering predicate based on a set of cards *)
  Definition coversHead card a b := prefix (prem card) a /\ prefix (conc card) b.

  Lemma coversHead_length_inv card a b : coversHead card a b -> isCard card -> length a >= 3 /\ length b >= 3. 
  Proof. 
    intros. unfold coversHead, prefix in *. firstorder.
    - rewrite H. rewrite app_length, (proj1 (isRule_length card)). lia.  
    - rewrite H1. rewrite app_length, (proj2 (isRule_length card)). lia. 
  Qed. 

  Definition coversHeadList cards a b := exists card, card el cards /\ coversHead card a b. 

  Lemma coversHeadList_subset cards1 cards2 a b :
    cards1 <<= cards2 -> coversHeadList cards1 a b -> coversHeadList cards2 a b.
  Proof. intros H (r & H1 & H2). exists r. split; [ apply H, H1 | apply H2]. Qed. 

  Lemma coversHead_card_inv r a b (σ1 σ2 σ3 σ4 σ5 σ6 : Sigma) : coversHead r (σ1 :: σ2 :: σ3 :: a) (σ4 :: σ5 :: σ6 :: b) -> r = {σ1, σ2 , σ3} / {σ4 , σ5, σ6}. 
  Proof. 
    unfold coversHead. unfold prefix. intros [(b' & H1) (b'' & H2)]. destruct r. destruct prem0, conc0. cbn in H1, H2. congruence. 
  Qed. 

  Lemma coversAt_HeadList_add_at_end i (a b c d : string) : 
    coversAt (coversHeadList cards) i a b -> coversAt (coversHeadList cards) i (a ++ c) (b ++ d). 
  Proof. 
    intros. unfold coversAt, coversHeadList in *.
    destruct H as (card & H0 & H). exists card; split; [assumption | ]. 
    unfold prefix in *. destruct H as ((b1 & H1) & (b2 & H2)). 
    split.
    - exists (b1 ++ c). rewrite app_assoc. apply skipn_app2 with (c := prem card ++ b1); [ | assumption]. 
      destruct card, prem. now cbn.  
    - exists (b2 ++ d). rewrite app_assoc. apply skipn_app2 with (c := conc card ++ b2); [ | assumption]. 
      destruct card, conc. now cbn. 
   Qed. 
End fixInstance. 


(** we define it using the coversHead_pred rewrite predicate *)
Definition TCCLang (C : TCC) := 
  TCC_wellformed C 
  /\ exists (sf : list (Sigma C)), relpower (valid (coversHeadList (cards C))) (steps C) (init C) sf 
    /\ satFinal (final C) sf. 

(** ** variant P-3-CC using propositional rules (defined via inductive predicates) *)

Record PTCC := {
             PSigma : finType;
             Pinit : list PSigma;  (* length is encoded implicitly as the length of init*) 
             Pcards : PSigma -> PSigma -> PSigma -> PSigma -> PSigma -> PSigma -> Prop;
             Pfinal : list (list PSigma);
             Psteps : nat
           }.

Definition PTCC_wellformed D := length (Pinit D) >= 3. 

Section fixRulePred.
  (** We define the equivalent of coversHeadList for predicate-based rules  *)

  Variable (X : Type).
  Definition cardPred := X -> X -> X -> X -> X -> X -> Prop.
  Variable (p : cardPred). 

  Inductive coversHeadInd: list X -> list X -> Prop :=
    | coversHead_indC (x1 x2 x3 x4 x5 x6 : X) s1 s2 : 
        p x1 x2 x3 x4 x5 x6 -> coversHeadInd (x1 :: x2 :: x3 :: s1) (x4 :: x5 :: x6 :: s2). 

  Hint Constructors coversHeadInd : core. 

  (** a few facts which will be useful *)
  Lemma coversHeadInd_tail_invariant (γ1 γ2 γ3 γ4 γ5 γ6 : X) s1 s2 s1' s2' :
    coversHeadInd (γ1 :: γ2 :: γ3 :: s1) (γ4 :: γ5 :: γ6 :: s2) <-> coversHeadInd (γ1 :: γ2 :: γ3 :: s1') (γ4 :: γ5 :: γ6 :: s2').
  Proof. split; intros; inv H; eauto. Qed. 

  Corollary coversHeadInd_rem_tail (γ1 γ2 γ3 γ4 γ5 γ6 : X) h1 h2 :
    coversHeadInd [γ1; γ2; γ3] [γ4; γ5; γ6] <-> coversHeadInd (γ1 :: γ2 :: γ3 :: h1) (γ4 :: γ5 :: γ6 :: h2).
  Proof. now apply coversHeadInd_tail_invariant. Qed. 

  Lemma coversHeadInd_append_invariant (γ1 γ2 γ3 γ4 γ5 γ6 : X) s1 s2 s1' s2' :
    coversHeadInd (γ1 :: γ2 :: γ3 :: s1) (γ4 :: γ5 :: γ6 :: s2) <-> coversHeadInd (γ1 :: γ2 :: γ3 :: s1 ++ s1') (γ4 :: γ5 :: γ6 :: s2 ++ s2').
  Proof. now apply coversHeadInd_tail_invariant. Qed.

  Lemma coversAt_coversHeadInd_add_at_end i a b h1 h2 :
    coversAt coversHeadInd i a b -> coversAt coversHeadInd i (a ++ h1) (b ++ h2).
  Proof. 
    intros. unfold coversAt in *. inv H; symmetry in H0; symmetry in H1; repeat erewrite skipn_app2; eauto; try congruence; cbn; eauto. 
  Qed.

  Lemma coversAt_coversHeadInd_rem_at_end i a b h1 h2 :
    coversAt coversHeadInd i (a ++ h1) (b ++ h2) -> i < |a| - 2 -> i < |b| - 2 -> coversAt coversHeadInd i a b.
  Proof. 
    intros. unfold coversAt in *.
    assert (i <= |a|) by lia. destruct (skipn_app3 h1 H2) as (a' & H3 & H4). rewrite H3 in H. 
    assert (i <= |b|) by lia. destruct (skipn_app3 h2 H5) as (b' & H6 & H7). rewrite H6 in H. 
    clear H2 H5.
    rewrite <- firstn_skipn with (l := a) (n := i) in H4 at 1. apply app_inv_head in H4 as <-. 
    rewrite <- firstn_skipn with (l := b) (n := i) in H7 at 1. apply app_inv_head in H7 as <-. 
    specialize (skipn_length i a) as H7. specialize (skipn_length i b) as H8. 
    remember (skipn i a) as l. do 3 (destruct l as [ | ? l] ; [cbn in H7; lia | ]). 
    remember (skipn i b) as l'. do 3 (destruct l' as [ | ? l']; [cbn in H8; lia | ]). 
    cbn in H. rewrite coversHeadInd_tail_invariant in H. apply H. 
  Qed. 
 
End fixRulePred. 

Hint Constructors coversHeadInd : core. 

Definition cardPred_subs (X : Type) (p1 p2 : cardPred X) := forall x1 x2 x3 x4 x5 x6, p1 x1 x2 x3 x4 x5 x6 -> p2 x1 x2 x3 x4 x5 x6.

Lemma coversHeadInd_monotonous (X : Type) (p1 p2 : cardPred X) : cardPred_subs p1 p2 -> forall x y, coversHeadInd p1 x y -> coversHeadInd p2 x y.
Proof. 
  intros H x y H1. inv H1. apply H in H0. eauto.  
Qed. 

Lemma coversHeadInd_congruent (X : Type) (p1 p2 : cardPred X) : (forall x1 x2 x3 x4 x5 x6, p1 x1 x2 x3 x4 x5 x6 <-> p2 x1 x2 x3 x4 x5 x6) -> forall x y, coversHeadInd p1 x y <-> coversHeadInd p2 x y.
Proof.  intros H; intros. split; apply coversHeadInd_monotonous; unfold cardPred_subs; apply H. Qed. 

Hint Constructors coversHeadInd : core.

Definition PTCCLang (C : PTCC) := 
  PTCC_wellformed C 
  /\ exists (sf : list (PSigma C)), relpower (valid (coversHeadInd (@Pcards C))) (Psteps C) (Pinit C) sf 
    /\ satFinal (Pfinal C) sf. 

(** ** results for agreement of P-3-CC and 3-CC *)
Definition cards_list_ind_agree {X : Type} (p : X -> X -> X -> X -> X -> X -> Prop) (l : list (TCCCard X)) :=
  forall x1 x2 x3 x4 x5 x6, p x1 x2 x3 x4 x5 x6 <-> {x1, x2, x3} / {x4, x5, x6} el l. 

Lemma cards_list_ind_coversHead_agree {X : Type} (p : X -> X -> X -> X -> X -> X -> Prop) (l : list (TCCCard X)) :
  cards_list_ind_agree p l -> forall s1 s2, (coversHeadInd p s1 s2 <-> coversHeadList l s1 s2). 
Proof. 
  intros; split; intros. 
  + inv H0. exists ({x1, x2, x3} / {x4, x5, x6}). split.
    * apply H, H1. 
    * split; unfold prefix; cbn; eauto. 
  + destruct H0 as (r & H1 & ((b & ->) & (b' & ->))). 
    destruct r as [prem0 conc0], prem0, conc0. cbn. constructor. apply H, H1.  
Qed.

Lemma tpr_ptpr_agree (X : finType) s final steps indcards (listcards : list (TCCCard X)): 
  cards_list_ind_agree indcards listcards 
  -> (TCCLang (Build_TCC s listcards final steps) <-> PTCCLang (Build_PTCC s indcards final steps)).
Proof. 
  intros; split; intros (H0 & sf & H1 & H2); cbn in *. 
  - split; [apply H0 | ]. 
    exists sf; cbn. split; [ | apply H2]. 
    eapply relpower_congruent; [ apply valid_congruent, cards_list_ind_coversHead_agree, H | apply H1].  
  - split; [apply H0 | ].  
    exists sf; cbn. split; [ | apply H2]. 
    eapply relpower_congruent; [ apply valid_congruent; symmetry; apply cards_list_ind_coversHead_agree, H | apply H1]. 
Qed. 

