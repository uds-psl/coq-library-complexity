(* -*- company-coq-local-symbols: (("|_|" .?␣)); -*- *)
From Undecidability.L.Complexity.Cook Require Import GenNP TCSR Prelim GenNP_PR_Basics GenNP_PR_Tape GenNP_PR_Transition.
From PslBase Require Import FiniteTypes. 
From Undecidability.TM Require Import TM.
Require Import Lia. 

Module multistep (sig : TMSig). 
  Module trans' := transition sig. 
  Export trans'. 

  Definition sstepRel s s' := halt (configState s) = false /\ sstep s = s'.

  Notation "s '≻(' k ')' s'" := (relpower sstepRel k s s') (at level 40). 

  (*this is similar to what loopM does, but using the unfolded TM *)
  Notation "s '▷(' k ')' s'" := (s ≻(k) s' /\ halt (configState s') = true) (at level 40).

  Notation "s '▷(≤' k ')' s'" := (exists l, l <= k /\ s ▷(l) s') (at level 40).

  Notation "s '⇝' s'" := (valid rewHeadSim s s') (at level 40). 
  Notation "s '⇝(' k ')' s'" := (relpower (valid rewHeadSim) k s s') (at level 40).

  (** *multi-step simulation *)
  (*with each step, a Turing machine needs at most one additional cell *)
  Lemma tm_step_size q tp q' tp' k: (q, tp) ≻ (q', tp') -> sizeOfTape tp = k -> sizeOfTape tp' <= S k. 
  Proof. 
    intros. 
    destruct H as (_ & H). unfold sstep in H. destruct tp; destruct trans; destruct p as ([] & []); cbn in *; simp_eqn; rewrite <- H2; cbn in *.
    all: try lia.
    all: repeat match goal with
    | [H : context[midtape ?l _ _]  |- _] => is_var l; destruct l; cbn in *
    | [H : context[midtape _ _ ?l]  |- _] => is_var l; destruct l; cbn in *
    | [H : context[tape_move_left' ?l _ _]  |- _] => is_var l; destruct l; cbn in *
    | [H : context[tape_move_left' _ _ ?l]  |- _] => is_var l; destruct l; cbn in *
    | [H : context[tape_move_right' ?l _ _]  |- _] => is_var l; destruct l; cbn in *
    | [H : context[tape_move_right' _ _ ?l]  |- _] => is_var l; destruct l; cbn in *
    | [H : context[(| _ ++ _ |)] |- _] => rewrite app_length in H
    | [H : context[(| rev _ |)] |- _ ] => rewrite rev_length in H
    | [ |- context[(| _ ++ _|)]] => rewrite app_length
    | [ |- context[(| rev _ |)]] => rewrite rev_length
    end; cbn in * ; try lia.
  Qed. 

  (*Lemma 23 *)
  (*the formulation here is a bit different than in the memo: *)
  (* - we additionally require that sizeOfTape tp < z'. While the statement is true without this restriction, we don't need the stronger version and its proof is a LOT more tedious *)
  Lemma step_inversion q tp s s' : (q, tp) ≃c s -> sizeOfTape tp < z' -> halt q = false -> s ⇝ s' -> exists! q' tp', (q', tp') ≃c s' /\ (q, tp) ≻ (q', tp'). 
  Proof.
    intros. 
    destruct (sstep (q, tp)) as (q', tp') eqn:H3. 
    assert ((q, tp) ≻ (q', tp')) as H4 by auto. 
    specialize (stepsim H H4 H0) as (s'' & F1 & F2 & F3 ). 
    apply F2 in H2.  subst.
    exists q'. split.
    + exists tp'. split.
      * repeat split. apply F3. now cbn. 
      * intros. destruct H2 as (_ & _ & H2); congruence. 
    + intros. destruct H2 as (? & (_ & _ & H2) & _).  congruence. 
  Qed. 

  (*same thing without the uniqueness because of the hassle of dealing with exists! if one doesn't need uniqueness *)
  Lemma step_inversion' q tp s s' : (q, tp) ≃c s -> sizeOfTape tp < z' -> halt q = false -> s ⇝ s' -> exists q' tp', (q', tp') ≃c s' /\ (q, tp) ≻ (q', tp'). 
  Proof. 
    intros. specialize (step_inversion H H0 H1 H2). intros. rewrite <- !unique_existence in H3.
    destruct H3 as ((q' & tp' & (H3 & _ )) & _ ). eauto. 
  Qed. 

  (*Lemma 24 *)
  Lemma halting_inversion q tp s s' : (q, tp) ≃c s -> halt q = true -> s ⇝ s' -> (q, tp) ≃c s'. 
  Proof. 
    intros. specialize (haltsim H H0 ) as (s'' & H2 & H3 & H4). 
    apply H3 in H1. subst. apply H4.  
  Qed. 

  (*Lemma 25 *)
  Lemma multistep_simulation q tp q' tp' k s : (q, tp) ≃c s -> (q, tp) ≻(k) (q', tp') -> z' >= k -> (sizeOfTape tp) <= z' - k -> exists s', s ⇝(k) s' /\ (forall s'', s ⇝(k) s'' -> s'' = s') /\ (q', tp') ≃c s'. 
  Proof.
    intros H1 H2 H4. 
    revert s H1. 
    remember (q, tp) as c1.  remember (q', tp') as c2. 
    revert q tp q' tp' Heqc1 Heqc2. 
    induction H2 as [ | a b c n H H2 IH]; intros q tp q' tp' -> -> s H1 H3. 
    - exists s. repeat split. 
      + constructor. 
      + intros. now inv H. 
      + apply H1. 
    - destruct b as (q''& tp''). assert (z' >= n) as X by lia. specialize (IH X q'' tp'' q' tp' eq_refl eq_refl). clear X.
      unfold sstepRel in H. 
      assert (sizeOfTape tp < z') as X by lia. specialize (stepsim H1 H X) as (s' & F1 & F2 & F3). clear X.
      specialize (IH s' F3) as (s'' & G1 & G2 & G3). 
      apply tm_step_size with (k := sizeOfTape tp)in H. 2: reflexivity. lia. 
      exists s''. repeat split. 
      + eauto.  
      + intros. inv H0. apply F2 in H6. rewrite H6 in *. clear H6. now apply G2. 
      + apply G3. 
  Qed.

  (*Lemma 26 *)
  Lemma multistep_halt q tp s : (q, tp) ≃c s -> halt q = true -> forall k, exists s', s ⇝(k) s' /\ (forall s'', s ⇝(k) s'' -> s'' = s') /\ (q, tp) ≃c s'. 
  Proof. 
    intros. 
    revert s H.
    induction k0 as [ | k0 IH]; intros s H.
    - exists s. repeat split; eauto. intros. now inv H1. 
    - specialize (haltsim H H0) as (s' & F1 & F2 & F3). 
      destruct (IH s' F3) as (s'' & G1 & G2 & G3). exists s''. repeat split.
      + eauto. 
      + intros. inv H1. apply F2 in H3. rewrite H3 in *; clear H3. now apply G2. 
      + apply G3. 
  Qed. 

  (*our final constraint. we don't use the definition via a list of final substrings from the TCSR definition, but instead use this more specific form *)
  (*we will later show that the two notions are equivalent for a suitable list of final substrings*)
  (*there exists the symbol of a halting state in the string s *)
  Definition containsHaltingState s := exists q qs, halt q = true /\ isSpecStateSym q qs /\ qs el s.  
  


  (*Lemma 27 *)
  (*currently differs from the version in the memo: the additional sizeOfTape tp <= z' - j constraint is due to the similar constraint in Lemma 23 *)
  (*the additional assumption z' >= j is needed for the same reason *)
  Lemma multistep_inversion q tp s s' j: (q, tp) ≃c s -> s ⇝(j) s' -> sizeOfTape tp <= z' - j -> z' >= j -> exists q' tp' j', (q', tp') ≃c s' /\ j' <= j /\ (q, tp) ≻(j') (q', tp') /\ sizeOfTape tp' <= sizeOfTape tp + j'. 
  Proof. 
    intros. apply relpower_relpowerRev in H0.
    induction H0 as [ | s y y' j H0 IH].  
    - exists q, tp, 0. rewrite Nat.add_0_r. repeat split; eauto.  
    - assert (sizeOfTape tp <= z' - j) as H4 by lia.  assert (z' >= j) as H5 by lia. 
      specialize (IH H H4 H5) as (q' & tp' & j' & F1 & F2 & F3 & F4). 
      clear H4 H5. 
      destruct (halt q') eqn:H4. 
      + exists q', tp', j'.
        specialize (halting_inversion F1 H4 H3) as H5. eauto. 
      + assert (sizeOfTape tp' < z') as H6 by lia.
        specialize (step_inversion' F1 H6 H4 H3) as (q'' & tp'' & G1 & G2). 
        exists q'', tp'', (S j'). repeat split; eauto. 
        * lia.  
        * apply relpower_relpowerRev. econstructor.
          -- apply relpower_relpowerRev in F3; eauto.
          -- apply G2.  
        * apply tm_step_size with (k := sizeOfTape tp') in G2; [lia | reflexivity ].  
  Qed. 

  (*Lemma 28 *)
  Lemma finalCondition q tp s : (q, tp) ≃c s -> (halt q = true <-> containsHaltingState s). 
  Proof.
    intros; split; intros.
    - destruct H as (ls & qm & rs & -> & H2). exists q, qm. repeat split; eauto. 
      destruct H2 as (p & -> & H3 & H4). unfold isSpecStateSym. unfold embedState. eauto. 
    - destruct H0 as (q' & qs & H1 & H2 & H3). enough (q = q') by congruence. 
      destruct H as (ls & qm & rs & -> & H4). destruct H4 as (p & -> & H5 & H6).
      apply in_app_or in H3; destruct H3 as [ | H3]; [ | apply in_app_or in H3; destruct H3 as [ | H3 ] ].
      + clear H6. destruct H2 as (m & ->). 
        apply in_rev in H. destruct H5 as (_ & _ & ->). apply in_app_iff in H. destruct H as [H | H]. 
        * unfold mapPolarity in H. apply in_map_iff in H as (σ & H & _). congruence. 
        * apply E_alphabet in H. destruct H; congruence.
      + destruct H as [ <- | []]. destruct H2. unfold embedState in H. congruence. 
      + clear H5. destruct H2 as (m & ->).
        destruct H6 as (_ & _ & ->). apply in_app_iff in H3. destruct H3 as [H | H]. 
        * unfold mapPolarity in H. apply in_map_iff in H as (σ & H & _). congruence. 
        * apply E_alphabet in H. destruct H; congruence.
  Qed. 

  (*Theorem 29 *)
  Lemma reprTape_exists u p w : |u| <= w -> exists s, u ≃t(p, w) s. 
  Proof. 
    intros. exists (mapPolarity p u ++ E p (wo + w - |u|)). 
    repeat split.
    + rewrite app_length. unfold mapPolarity. rewrite E_length, map_length. lia. 
    + apply H. 
  Qed. 

  Lemma reprConfig_exists q tp: sizeOfTape tp <= k -> exists s, (q, tp) ≃c s. 
  Proof.
    intros. enough (exists ls qm rs, (q, tp) ≃c (ls, qm, rs)). 
    { destruct H0 as (ls & qm & rs & H0). exists (rev ls ++ [qm] ++ rs). unfold reprConfig. exists ls, qm, rs. eauto. }
    rewrite sizeOfTape_lcr in H. 
    assert (|left tp| <= z') as H1 by (unfold z'; lia). 
    assert (|right tp| <= z') as H2 by (unfold z'; lia). 
    destruct (reprTape_exists neutral H1) as (ls & F1). 
    destruct (reprTape_exists neutral H2) as (rs & F2). 
    exists ls, (inl (q, current tp)), rs. exists neutral. destruct F1 as (? & ? & ?), F2 as (? & ? & ?); repeat split; assumption. 
  Qed. 

  Theorem completeness q tp q' tp' s : sizeOfTape tp <= k -> (q, tp) ≃c s -> (q, tp) ▷(≤t) (q', tp') -> exists s', s ⇝(t) s' /\ (q', tp') ≃c s' /\ containsHaltingState s'. 
  Proof. 
    intros. 
    destruct H1 as (t' & H1 & (H2 & H3)). cbn in H3. 
    assert (z' >= t') as H4 by (unfold z'; lia). 
    assert (sizeOfTape tp <= z' - t') as H5 by (unfold z'; lia). 
    specialize (multistep_simulation H0 H2 H4 H5) as (s' & F1 & _ & F3). 
    specialize (multistep_halt F3 H3 (t - t')) as (s'' & G1 & _ & G3).
    exists s''. repeat split. 
    + replace t with (t' + (t - t')) by lia. eauto using relpower_trans. 
    + apply G3. 
    + eapply finalCondition; eauto. 
  Qed. 

  (*Theorem 30 *)
  Theorem soundness q tp s s' : (q, tp) ≃c s -> sizeOfTape tp <= k -> s ⇝(t) s' -> containsHaltingState s' -> exists q' tp', (q', tp') ≃c s' /\ (q, tp) ▷(≤t) (q', tp') /\ sizeOfTape (tp') <= z. 
  Proof.
    intros.
    assert (sizeOfTape tp <= z' - t) as H3 by (unfold z'; lia). 
    assert (z' >= t) as H4 by (unfold z'; lia). 
    specialize (multistep_inversion H H1 H3 H4) as (q' & tp' & t' & F1 & F2 & F3 & F4). 
    exists q', tp'. repeat split. 
    - apply F1. 
    - exists t'. apply (finalCondition F1) in H2. split; [apply F2 | ]. split; cbn; eauto. 
    - unfold z. lia. 
  Qed. 
    
End multistep.
