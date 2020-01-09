From PslBase Require Import Base. 
From PslBase Require Import Vectors.Vectors. 
From PslBase Require Import FiniteTypes. 
From Undecidability Require Import L.Complexity.Cook.Prelim.
Require Import Lia.

(*we first define some notions for an arbitrary rewritesHead predicate *)
Section abstractDefs.
  Variable (X : Type). 
  Notation string := (list X). 

  Definition rewritesHeadAbstract := string -> string -> Prop. 

  Section fixRewritesHead.
    Variable (p : rewritesHeadAbstract). 

    (* rewrites inside a string *)
    Definition rewritesAt (i : nat) a b := p (skipn i a) (skipn i b).
    Lemma rewritesAt_head a b : p a b <-> rewritesAt 0 a b. 
    Proof. 
      unfold rewritesAt.
      rewrite <- firstn_skipn with (n:= 0) (l:= a) at 1.
      rewrite <- firstn_skipn with (n:= 0) (l:= b) at 1.
      repeat rewrite firstn_O; now cbn. 
    Qed. 

    Lemma rewritesAt_step a b x y (i:nat) : rewritesAt i a b <-> rewritesAt (S i) (x :: a) (y:: b). 
    Proof. intros. unfold rewritesAt. now cbn. Qed. 


    (*validity of a rewrite *)
    Inductive valid : string -> string -> Prop :=
    | validB: valid [] [] 
    | validSA a b x y: valid a b -> length a < 2 -> valid (x:: a) (y:: b)
    | validS a b x y : valid a b -> p (x::a) (y::b) -> valid (x::a) (y::b). 

    Hint Constructors valid. 

    Lemma valid_length_inv a b : valid a b -> length a = length b. 
    Proof.
      induction 1. 
      - now cbn.
      - cbn; congruence.
      - cbn; congruence. 
    Qed. 

    Lemma relpower_valid_length_inv n a b : relpower valid n a b -> length a = length b. 
    Proof.  induction 1; [solve [eauto] | ]. apply valid_length_inv in H. congruence. Qed. 

    Lemma valid_base (a b c d e f : X) : valid [a; b ; c] [d; e; f] <-> p [a; b; c] [d; e; f]. 
    Proof. 
      split.
      - intros; inv H. cbn in H5; lia. apply H5.  
      - constructor 3. 2: apply H. repeat constructor.
    Qed. 

    (*the explicit characterisation using bounded quantification *)
    Definition validExplicit a b := length a = length b /\ forall i, 0 <= i < length a - 2  -> rewritesAt i a b.

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
            eapply (@validS a0 b a x). 2-3: assumption. 
            apply IHa. split; [congruence | ]. 
            intros. assert (0 <= S i < S (|a0|) - 2) by lia. 
            specialize (H2 (S i) H4). eauto. 
          * constructor. 
            2: assumption. 
            apply IHa. split; [congruence | intros ]. 
            cbn [length] in H2. assert (0 <= S i < S(|a0|) - 2) by lia. 
            specialize (H2 (S i) H0); eauto. 
    Qed. 


  End fixRewritesHead.
  Hint Constructors valid. 

  Lemma valid_congruent' (p1 p2 : rewritesHeadAbstract) : (forall u v, p1 u v -> p2 u v) -> forall a b, valid p1 a b -> valid p2 a b. 
  Proof. 
    intros.
    induction H0. 
    - constructor. 
    - now constructor. 
    - constructor 3. apply IHvalid. 
      now apply H. 
  Qed.

  Corollary valid_congruent p1 p2 : (forall u v, p1 u v <-> p2 u v) -> forall a b, valid p1 a b <-> valid p2 a b.
  Proof.
    intros; split; [apply valid_congruent'; intros; now apply H | ].
    assert (forall u v, p2 u v <-> p1 u v) by (intros; now rewrite H).
    apply valid_congruent'. intros; now apply H. 
  Qed.

  Lemma valid_monotonous (p1 p2 : rewritesHeadAbstract) : (forall x y, p1 x y -> p2 x y) -> forall x y, valid p1 x y -> valid p2 x y.
  Proof. 
    intros H x y. induction 1.  
    - eauto. 
    - constructor 2; eauto. 
    - apply H in H1. eauto. 
  Qed. 
End abstractDefs. 

Arguments valid {X}. 
Hint Constructors valid. 

Ltac inv_valid := match goal with
                    | [ H : valid _ _ _ |- _] => inv H
                  end;
                  try match goal with
                  | [ H : | _ | < 2 |- _] => now cbn in H
                  end.


(** *TPR using list-based rules *)

(*use an explicit representation instead of vectors of size 3 since this will make the problem closer to the flattened extractable problem *)
Record TPRWinP (Sigma : Type) := {
                                   winEl1 : Sigma;
                                   winEl2 : Sigma;
                                   winEl3 : Sigma
                                 }.

Record TPRWin (Sigma : Type) := {
                                            prem : TPRWinP Sigma;
                                            conc : TPRWinP Sigma
                                   }.

Definition TPRWinP_to_list (sig : Type) (a : TPRWinP sig) := match a with Build_TPRWinP a b c => [a; b; c] end. 
Coercion TPRWinP_to_list : TPRWinP >-> list. 

Notation "'{' a ',' b ',' c '}'" := (Build_TPRWinP a b c) (format "'{' a ',' b ',' c '}'").
Notation "a / b" := ({|prem := a; conc := b|}). 

Record TPR := {
               Sigma : Type;
               init : list Sigma;  (* length is encoded implicitly as the length of init*) 
               windows : list (TPRWin Sigma);
               final : list (list Sigma);
               steps : nat
             }.

Implicit Type (C : TPR).

(* the final constraint*)
Definition satFinal (X : Type) final (s : list X) := exists subs, subs el final /\ substring subs s.

(*specific definitions and results for list-based rules*)
Section fixInstance.
  Variable (Sigma : Type).
  Variable (init : list Sigma).
  Variable (windows : list (TPRWin Sigma)).
  Variable (final : list (list Sigma)).
  Variable (steps : nat). 

  Notation string := (list Sigma). 
  Definition window := TPRWin Sigma.

  Implicit Type (s a b: string). 
  Implicit Type (r rule : window).
  Implicit Type (x y : Sigma).

  Definition isRule r := r el windows.
  Lemma isRule_length r : length (prem r) = 3 /\ length (conc r) = 3.
  Proof. 
    intros. destruct r. 
    cbn. destruct prem0, conc0. now cbn. 
  Qed. 

  (*we now define a concrete rewrite predicate based on a set of rules *)
  Definition rewritesHead rule a b :=
    prefix (prem rule) a /\ prefix (conc rule) b.

  Lemma rewritesHead_length_inv rule a b : rewritesHead rule a b -> isRule rule -> length a >= 3 /\ length b >= 3. 
  Proof. 
    intros. unfold rewritesHead, prefix in *. firstorder.
    - rewrite H. rewrite app_length, (proj1 (isRule_length rule)). lia.  
    - rewrite H1. rewrite app_length, (proj2 (isRule_length rule)). lia. 
  Qed. 

  Definition rewritesHeadList ruleset a b := exists rule, rule el ruleset /\ rewritesHead rule a b. 

  Lemma rewritesHeadList_subset ruleset1 ruleset2 a b :
    ruleset1 <<= ruleset2 -> rewritesHeadList ruleset1 a b -> rewritesHeadList ruleset2 a b.
  Proof. intros H (r & H1 & H2). exists r. split; [ apply H, H1 | apply H2]. Qed. 


  Lemma rewritesHead_rule_inv r a b (σ1 σ2 σ3 σ4 σ5 σ6 : Sigma) : rewritesHead r (σ1 :: σ2 :: σ3 :: a) (σ4 :: σ5 :: σ6 :: b) -> r = {σ1, σ2 , σ3} / {σ4 , σ5, σ6}. 
  Proof. 
    unfold rewritesHead. unfold prefix. intros [(b' & H1) (b'' & H2)]. destruct r. destruct prem0, conc0. cbn in H1, H2. congruence. 
  Qed. 

  Lemma rewritesAt_HeadList_add_at_end i ruleset (a b c d : string) : rewritesAt (rewritesHeadList ruleset) i a b -> rewritesAt (rewritesHeadList ruleset) i (a ++ c) (b ++ d). 
  Proof. 
    intros. unfold rewritesAt, rewritesHeadList in *.
    destruct H as (rule & H0 & H). exists rule; split; [assumption | ]. 
    unfold Prelim.prefix in *. destruct H as ((b1 & H1) & (b2 & H2)). 
    split.
    - exists (b1 ++ c). rewrite app_assoc. apply skipn_app2 with (c := prem rule ++ b1); [ | assumption]. 
      destruct rule, prem. now cbn.  
    - exists (b2 ++ d). rewrite app_assoc. apply skipn_app2 with (c := conc rule ++ b2); [ | assumption]. 
      destruct rule, conc. now cbn. 
   Qed. 
End fixInstance. 



(*we define it using the rewritesHead_pred rewrite predicate *)
Definition TPRLang (C : TPR) :=  exists (sf : list (Sigma C)), relpower (valid (rewritesHeadList (windows C))) (steps C) (init C) sf /\ satFinal (final C) sf. 

(** *variant PTPR using propositional rules *)

Record PTPR := {
             PSigma : Type;
             Pinit : list PSigma;  (* length is encoded implicitly as the length of init*) 
             Pwindows : PSigma -> PSigma -> PSigma -> PSigma -> PSigma -> PSigma -> Prop;
             Pfinal : list (list PSigma);
             Psteps : nat
           }.

Section fixRulePred.
  (*We define the equivalent of rewritesHeadList for predicate-based rules  *)

  Variable (X : Type).
  Definition windowPred := X -> X -> X -> X -> X -> X -> Prop.
  Variable (p : windowPred). 

  Inductive rewritesHeadInd: list X -> list X -> Prop :=
    | rewHead_indC (x1 x2 x3 x4 x5 x6 : X) s1 s2 : p x1 x2 x3 x4 x5 x6 -> rewritesHeadInd (x1 :: x2 :: x3 :: s1) (x4 :: x5 :: x6 :: s2). 

  Hint Constructors rewritesHeadInd. 

  (*a few facts which will be useful *)
  Lemma rewritesHeadInd_tail_invariant (γ1 γ2 γ3 γ4 γ5 γ6 : X) s1 s2 s1' s2' :
    rewritesHeadInd (γ1 :: γ2 :: γ3 :: s1) (γ4 :: γ5 :: γ6 :: s2) <-> rewritesHeadInd (γ1 :: γ2 :: γ3 :: s1') (γ4 :: γ5 :: γ6 :: s2').
  Proof. split; intros; inv H; eauto. Qed. 

  Corollary rewritesHeadInd_rem_tail (γ1 γ2 γ3 γ4 γ5 γ6 : X) h1 h2 :
    rewritesHeadInd [γ1; γ2; γ3] [γ4; γ5; γ6] <-> rewritesHeadInd (γ1 :: γ2 :: γ3 :: h1) (γ4 :: γ5 :: γ6 :: h2).
  Proof. now apply rewritesHeadInd_tail_invariant. Qed. 

  Lemma rewritesHeadInd_append_invariant (γ1 γ2 γ3 γ4 γ5 γ6 : X) s1 s2 s1' s2' :
    rewritesHeadInd (γ1 :: γ2 :: γ3 :: s1) (γ4 :: γ5 :: γ6 :: s2) <-> rewritesHeadInd (γ1 :: γ2 :: γ3 :: s1 ++ s1') (γ4 :: γ5 :: γ6 :: s2 ++ s2').
  Proof. now apply rewritesHeadInd_tail_invariant. Qed.

  Lemma rewritesAt_rewritesHeadInd_add_at_end i a b h1 h2 :
    rewritesAt rewritesHeadInd i a b -> rewritesAt rewritesHeadInd i (a ++ h1) (b ++ h2).
  Proof. 
    intros. unfold rewritesAt in *. inv H; symmetry in H0; symmetry in H1; repeat erewrite skipn_app2; eauto; try congruence; cbn; eauto. 
  Qed.

  Lemma rewritesAt_rewritesHeadInd_rem_at_end i a b h1 h2 :
    rewritesAt rewritesHeadInd i (a ++ h1) (b ++ h2) -> i < |a| - 2 -> i < |b| - 2 -> rewritesAt rewritesHeadInd i a b.
  Proof. 
    intros. unfold rewritesAt in *.
    assert (i <= |a|) by lia. destruct (skipn_app3 h1 H2) as (a' & H3 & H4). rewrite H3 in H. 
    assert (i <= |b|) by lia. destruct (skipn_app3 h2 H5) as (b' & H6 & H7). rewrite H6 in H. 
    clear H2 H5.
    rewrite <- firstn_skipn with (l := a) (n := i) in H4 at 1. apply app_inv_head in H4 as <-. 
    rewrite <- firstn_skipn with (l := b) (n := i) in H7 at 1. apply app_inv_head in H7 as <-. 
    specialize (skipn_length i a) as H7. specialize (skipn_length i b) as H8. 
    remember (skipn i a) as l. do 3 (destruct l as [ | ? l] ; [cbn in H7; lia | ]). 
    remember (skipn i b) as l'. do 3 (destruct l' as [ | ? l']; [cbn in H8; lia | ]). 
    cbn in H. rewrite rewritesHeadInd_tail_invariant in H. apply H. 
  Qed. 
 
End fixRulePred. 

Hint Constructors rewritesHeadInd. 

Definition windowPred_subs (X : Type) (p1 p2 : windowPred X) := forall x1 x2 x3 x4 x5 x6, p1 x1 x2 x3 x4 x5 x6 -> p2 x1 x2 x3 x4 x5 x6.

Lemma rewritesHeadInd_monotonous (X : Type) (p1 p2 : windowPred X) : windowPred_subs p1 p2 -> forall x y, rewritesHeadInd p1 x y -> rewritesHeadInd p2 x y.
Proof. 
  intros H x y H1. inv H1. apply H in H0. eauto.  
Qed. 

Lemma rewritesHeadInd_congruent (X : Type) (p1 p2 : windowPred X) : (forall x1 x2 x3 x4 x5 x6, p1 x1 x2 x3 x4 x5 x6 <-> p2 x1 x2 x3 x4 x5 x6) -> forall x y, rewritesHeadInd p1 x y <-> rewritesHeadInd p2 x y.
Proof.  intros H; intros. split; apply rewritesHeadInd_monotonous; unfold windowPred_subs; apply H. Qed. 

Hint Constructors rewritesHeadInd.

Definition PTPRLang (C : PTPR) :=  exists (sf : list (PSigma C)), relpower (valid (rewritesHeadInd (@Pwindows C))) (Psteps C) (Pinit C) sf /\ satFinal (Pfinal C) sf. 

(** *results for agreement of PTPR and TPR *)
Definition rules_list_ind_agree {X : Type} (p : X -> X -> X -> X -> X -> X -> Prop) (l : list (window X)) :=
  forall x1 x2 x3 x4 x5 x6, p x1 x2 x3 x4 x5 x6 <-> {x1, x2, x3} / {x4, x5, x6} el l. 

Lemma rules_list_ind_rewritesHead_agree {X : Type} (p : X -> X -> X -> X -> X -> X -> Prop) (l : list (window X)) :
  rules_list_ind_agree p l -> forall s1 s2, (rewritesHeadInd p s1 s2 <-> rewritesHeadList l s1 s2). 
Proof. 
  intros; split; intros. 
  + inv H0. exists ({x1, x2, x3} / {x4, x5, x6}). split.
    * apply H, H1. 
    * split; unfold prefix; cbn; eauto. 
  + destruct H0 as (r & H1 & ((b & ->) & (b' & ->))). 
    destruct r as [prem0 conc0], prem0, conc0. cbn. constructor. apply H, H1.  
Qed.

Lemma tpr_ptpr_agree (X : Type) s final steps indrules (listrules : list (window X)): 
  rules_list_ind_agree indrules listrules 
  -> (TPRLang (Build_TPR s listrules final steps) <-> PTPRLang (Build_PTPR s indrules final steps)).
Proof. 
  intros; split; intros (sf & H1 & H2); cbn in *. 
  - exists sf; cbn. split; [ | apply H2]. 
    eapply relpower_congruent; [ apply valid_congruent, rules_list_ind_rewritesHead_agree, H | apply H1].  
  - exists sf; cbn. split; [ | apply H2]. 
    eapply relpower_congruent; [ apply valid_congruent; symmetry; apply rules_list_ind_rewritesHead_agree, H | apply H1]. 
Qed. 

