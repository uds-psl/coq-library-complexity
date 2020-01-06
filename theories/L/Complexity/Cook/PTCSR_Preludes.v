From Undecidability.L.Complexity Require Import Cook.TCSR Cook.Prelim.
From PslBase Require Import Base. 
Require Import Lia. 

Section fixPTCSRInstance. 
  (*original instance lacking an initial string*)
  Variable (Sigma : Type). 
  Variable (p : Sigma -> Sigma -> Sigma -> Sigma -> Sigma -> Sigma -> Prop). 
  Variable (finalCondition : list (list Sigma)). 
  Variable (t : nat). 

  (*instead of an initial string, we have an initial condition and a length l*)
  Variable (initCond: list Sigma -> Prop). 
  Variable (l : nat).

  (*otherwise, vacuous rewrites destroy everything *)
  Variable (A0 : l >= 3). 

  (*the question now is: does there exists x0 satisfying initCond such that it ends up in a final state? *)
  Definition ExPTCSR := exists x0, |x0| = l /\ initCond x0 /\ PTCSRLang (Build_PTCSR x0 p finalCondition t). 

  (*a prelude generates initial strings satisfying initCond *)
  Variable (Sigma' : Type). 
  Notation combSigma := (sum Sigma Sigma').

  Variable (p' : Sigma' -> Sigma' -> Sigma' -> combSigma -> combSigma -> combSigma -> Prop). 


  Variable (initialString : list Sigma').   
  Variable (t' : nat). 

  Definition isOrigString (s : list combSigma) := exists s', s = map inl s'.  
  Definition isPreludeString (s : list combSigma) := exists s', s = map inr s'. 

  Inductive liftPrelude : windowPred combSigma := 
    | liftPreludeC (a b c : Sigma') (d e f : combSigma) : p' a b c d e f -> liftPrelude (inr a) (inr b) (inr c) d e f. 

  Inductive liftOrig : windowPred combSigma := 
    | liftOrigC (a b c d e f : Sigma) : p a b c d e f -> liftOrig (inl a) (inl b) (inl c) (inl d) (inl e) (inl f).  

  Hint Constructors liftPrelude liftOrig.

  Definition combP a b c d e f := liftPrelude a b c d e f \/ liftOrig a b c d e f.
  Hint Unfold combP. 

  (*the prelude rules always produce a string that is a valid initial string for the original instance, up to the injection inl *)
  Variable (A1: forall x0, relpower (valid (rewritesHeadInd liftPrelude)) t' (map inr initialString) x0 -> isOrigString x0). 

  (*disjointness: string is produced too early *)
  Variable (A2 : forall k x, k < t' -> relpower (valid (rewritesHeadInd liftPrelude)) k (map inr initialString) x -> isPreludeString x).  

  (*completeness *)
  Variable (A3 : forall x0, initCond x0 /\ |x0| = l -> relpower (valid (rewritesHeadInd liftPrelude)) t' (map inr initialString) (map inl x0)). 

  (*soundness *)
  Variable (A4 : forall x0, relpower (valid (rewritesHeadInd liftPrelude)) t' (map inr initialString) x0 -> exists x0', x0 = map inl x0' /\ initCond x0'). 

  (*compatibility *)
  Variable (A5 : |initialString| = l). 


  Lemma liftPrelude_subs_combP : windowPred_subs liftPrelude combP. 
  Proof. 
    unfold windowPred_subs. intros. inv H. eauto. 
  Qed. 


  Hint Constructors valid. 

  Ltac inv_eqn_map := repeat match goal with 
    | [H : _ :: ?a = map _ ?s |- _] => is_var s; destruct s; cbn in H; [congruence | inv H]
    | [H : [] = map _ ?s |- _] => is_var s; destruct s; cbn in H; [ clear H| congruence]
  end. 

  Lemma relpower_inr_liftPrelude' n b: 
    n < t' 
    -> relpower (valid (rewritesHeadInd combP)) n (map inr initialString) b 
    -> relpower (valid (rewritesHeadInd liftPrelude)) n (map inr initialString) b /\ isPreludeString b.
  Proof. 
    intros H0 H. clear A0 A1 A3 A4 A5. 
    remember (map inr initialString). 
    (*we use the version of relpower defined by adding transitions at the tail of a chain since we need to keep A2, which requires the initialString at the head (otherwise, we could not apply the IH) *)
    apply relpower_relpowerRev in H. setoid_rewrite relpower_relpowerRev. 
    induction H; cbn; intros; subst. 
    - eauto. 
    - edestruct (IHrelpowerRev) as (IH & (? & ->)). 
      + reflexivity. 
      + apply A2. 
      + lia. 
      + clear IHrelpowerRev. assert (valid (rewritesHeadInd liftPrelude) (map inr x) y') as H3.   
        { 
          clear IH H0 H. remember (map inr x) as x' eqn:H2. revert x H2. 
          induction H1; cbn; intros; eauto; inv_eqn_map. 
          + constructor 2; [eapply IHvalid; reflexivity | apply H]. 
          + constructor 3; [eapply IHvalid; reflexivity | clear IHvalid]. 
            inv H. inv_eqn_map.
            inv H2;  [eauto |  ]. inv H. 
        } 
        split. 
        * apply relpowerRevS with (y := map inr x); [ apply IH | apply H3]. 
        * (*we use A2 to derive that b is a preludeString *)
          assert (relpower (valid (rewritesHeadInd liftPrelude)) (S n) (map inr initialString) y') as H2. 
          { apply relpower_relpowerRev. eauto. }
          now apply A2 in H2. 
  Qed.  

  Corollary relpower_inr_liftPrelude n b : 
    n <= t' 
    -> relpower (valid (rewritesHeadInd combP)) n (map inr initialString) b 
    -> relpower (valid (rewritesHeadInd liftPrelude)) n (map inr initialString) b.
  Proof. 
    intros. clear A0 A1 A3 A4 A5. destruct (lt_dec n t') as [l0 | l0]. 
    - eapply relpower_inr_liftPrelude' in H0; [ | apply l0]. tauto. 
    - assert (n = t') by lia. clear H l0. destruct n. 
      + inv H0. auto. 
      + assert (n < t') as H2 by lia. apply relpower_relpowerRev in H0. inversion H0. 
        apply relpower_relpowerRev in H3. apply relpower_inr_liftPrelude' in H3 as (H3 & (? & ->)); subst; [ | apply H2].
        apply relpower_relpowerRev. econstructor; [ apply relpower_relpowerRev, H3 | ]. 
        clear H2 H3 H0 A2. remember (map inr x0) as x1 eqn:Heqn. revert x0 Heqn. induction H4; intros.  
        * eauto. 
        * inv_eqn_map; constructor; eauto.
        * inv_eqn_map; constructor 3; [eauto | ]. inv H. inv_eqn_map. inv H1; [ eauto | ]. inv H. 
  Qed. 

  Lemma relpower_add_split (X : Type) (R : X -> X -> Prop) n m x y: relpower R (n + m) x y -> exists z, relpower R n x z /\ relpower R m z y.
  Proof. 
    clear A0 A1 A2 A3 A4 A5. 
    revert x y. induction n; intros. 
    - cbn in H. eauto. 
    - inv H. apply IHn in H2 as (z & H3 & H4). exists z. eauto.
  Qed. 

  Lemma relpower_inl_liftOrig n s b : 
    |s| >= 3  
    -> relpower (valid (rewritesHeadInd combP)) n (map inl s) b 
    -> relpower (valid (rewritesHeadInd liftOrig)) n (map inl s) b /\ isOrigString b. 
  Proof. 
    clear A0 A1 A2 A3 A4 A5. intros H0 H. remember (map inl s) as s' eqn:Heqn. 
    enough (relpower (valid (rewritesHeadInd liftOrig)) n s' b /\ isOrigString b) by tauto. 
    revert s H0 Heqn. 
    induction H; intros.  
    - subst; split; unfold isOrigString; eauto. 
    - assert (valid (rewritesHeadInd liftOrig) a b /\ isOrigString b) as (H2 & (? & ->)). 
      { 
        clear IHrelpower H0. revert s H1 Heqn. unfold isOrigString. induction H; intros. 
        + eauto. 
        + inv_eqn_map. rewrite map_length in H0; cbn in H1; lia.   
        + inv_eqn_map. inv H0. inv_eqn_map. inv H3. 
          * inv H0.   
          * inv H0. destruct s4; cbn in *. 
            -- apply valid_length_inv in H; destruct s2; [ | cbn in H; congruence]. 
               split.
               ++ constructor 3. constructor 2; cbn; eauto.  eauto.
               ++ exists [d; e; f]; eauto. 
            -- edestruct (IHvalid (s0::s3::s1::s4)) as (H2 & (? & H3)); [now cbn | now cbn | inv_eqn_map ]. 
               split; [eauto | ]. exists (d :: s5 :: s6 :: x); eauto.  
      } 
      subst. 
      edestruct (IHrelpower) as (IH1 & IH2). 
      2: { reflexivity. }
      + apply valid_length_inv in H. rewrite !map_length in H. lia. 
      + split; [ | apply IH2]. apply relpowerS with (b := map inl x); [ apply H2 |apply IH1].  
  Qed. 

  Lemma relpower_comb_split sf : 
    relpower (valid (rewritesHeadInd combP)) (t' + t) (map inr initialString) sf 
    -> exists x0, relpower (valid (rewritesHeadInd liftPrelude)) t' (map inr initialString) x0 
                  /\ relpower (valid (rewritesHeadInd liftOrig)) t x0 sf /\ isOrigString sf.
  Proof. 
    clear A3 A4. 
    intros (z & H1 & H2)%relpower_add_split. 
    exists z. apply relpower_inr_liftPrelude in H1; [ | auto]. split. 
    - eauto. 
    - specialize (A1 H1) as (? & ->). eapply relpower_inl_liftOrig. 
      + clear H2 A2. 
        apply relpower_valid_length_inv in H1. rewrite !map_length in H1. lia. 
      + apply H2. 
  Qed. 

  Lemma valid_liftOrig_isOrigString a b : |a| >= 3 -> valid (rewritesHeadInd liftOrig) a b -> isOrigString b. 
  Proof. 
    clear A1 A2 A3 A4 A5 A0. intros H. induction 1; unfold isOrigString. 
    - exists []; eauto.
    - cbn in H; lia. 
    - cbn in H. inv H1. destruct s1. 
      + apply valid_length_inv in H0. destruct s2; [ | cbn in H0; congruence]. 
        inv H3. exists [d; e; f]; eauto. 
      + cbn in *. edestruct IHvalid as (? & ->); [ lia| ]. inv H3. 
        exists (d :: x0); eauto. 
  Qed. 

  Lemma liftOrig_valid_p x x': valid (rewritesHeadInd liftOrig) (map inl x) (map inl x') -> valid (rewritesHeadInd p) x x'.
  Proof. 
    clear A1 A2 A3 A4 A5 A0. 
    remember (map inl x) as x0 eqn:eqnx0. remember (map inl x') as x0' eqn:eqnx0'. 
    induction 1 in x, x', eqnx0, eqnx0' |- *; inv_eqn_map. 
    - eauto. 
    - constructor; [ | rewrite map_length in H0; apply H0]. now apply IHvalid. 
    - constructor 3. 
      + inv H0; inv_eqn_map. inv H2. eauto. 
      + inv H0; inv_eqn_map. inv H2. eauto. 
  Qed. 

  Lemma liftOrig_relpower_p n x sf : 
    |x| >= 3
    -> relpower (valid (rewritesHeadInd liftOrig)) n (map inl x) (map inl sf) 
    -> relpower (valid (rewritesHeadInd p)) n x sf. 
  Proof. 
    clear A1 A2 A3 A4 A5 A0. intros H0 H. remember (map inl x) as x' eqn:Hx'. remember (map inl sf) as sf' eqn:Hsf'. 
    revert x sf H0 Hx' Hsf'. induction H; intros. 
    - subst; apply Prelim.map_inj in Hsf'; [ subst; auto| unfold injective; intros; congruence]. 
    - assert (|a| >= 3). { subst. rewrite map_length. apply H1. } 
      specialize (valid_liftOrig_isOrigString H2 H) as (? & ->). econstructor. 
      + subst. apply liftOrig_valid_p, H.  
      + eapply IHrelpower; [ | reflexivity | eauto].  
        subst. apply valid_length_inv in H. now rewrite !map_length in H.  
  Qed. 

  Lemma prelude_ok : ExPTCSR <-> PTCSRLang (Build_PTCSR (map inr initialString) combP (map (map inl) finalCondition) (t' + t)). 
  Proof. 
    split. 
    - intros (x0 & H1 & H2 & (sf & F1 & F2)). cbn in *. exists (map inl sf). cbn. split. 
      + eapply relpower_trans.
        * eapply relpower_monotonous. 
          { eapply valid_monotonous. eapply rewritesHeadInd_monotonous. apply liftPrelude_subs_combP. }
          apply A3. eauto. 
        * clear H1 H2 F2. (*TODO: maybe more general form using retracts?*)
          induction F1. 
          -- constructor. 
          -- econstructor. 2: apply IHF1. 
             clear F1 IHF1. induction H.
             ++ cbn; constructor. 
             ++ cbn; constructor; [ apply IHvalid | rewrite map_length; apply H0]. 
             ++ cbn; constructor 3; [apply IHvalid | ]. inv H0. cbn; eauto.  
      + unfold satFinal in *. destruct F2 as (subs & F2 & F3). exists (map inl subs). 
        split. 
        * apply in_map_iff. eauto.  
        * unfold substring. destruct F3 as (b1 & b2 & F3). 
          exists (map inl b1), (map inl b2). now rewrite F3, !map_app. 
    - intros (sf & F1 & F2). cbn in *. unfold ExPTCSR. 
      (*we need to split up F1 into the prelude and original part *)
      apply relpower_comb_split in F1 as (x0 & H1 & H2 & H3). 
      specialize (A1 H1) as (x & ->). exists x. split; [ | split]. 
      + apply relpower_valid_length_inv in H2. rewrite map_length in H2. 
        apply relpower_valid_length_inv in H1. rewrite !map_length in H1. lia. 
      + apply A4 in H1. destruct H1 as (? & H1 & H4). apply Prelim.map_inj in H1; [subst; apply H4 | ]. 
        unfold injective. intros. congruence. 
      + unfold PTCSRLang. cbn. destruct H3 as (sf' & ->). exists sf'. split. 
        * clear F2 A2 A3 A4. apply liftOrig_relpower_p, H2. 
          apply relpower_valid_length_inv in H1.  rewrite !map_length in H1. lia.
        * clear A0 A2 A3 A4 A5 H1 H2. unfold satFinal in *. 
          destruct F2 as (subs & H1 & H2). apply in_map_iff in H1 as (subs' & <- & H1).
          exists subs'; split; [apply H1 | ]. 
          unfold substring in *. destruct H2 as (b1 & b2 & H). 
          apply map_eq_app in H as (b1' & b & H & -> & H2). 
          symmetry in H2. apply map_eq_app in H2 as (b' & b2' & -> & H2 & ->). 
          exists b1', b2'. enough (subs' = b') by (subst; reflexivity). 
          apply Prelim.map_inj in H2; [apply H2 | unfold injective; congruence].  
  Qed. 
End fixPTCSRInstance. 
