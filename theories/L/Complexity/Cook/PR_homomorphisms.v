From PslBase Require Import Base FiniteTypes. 
From PslBase Require Import Vectors.Vectors. 
From Undecidability.L.Complexity.Cook Require Import Prelim PR.
From Undecidability.L.Complexity.Cook Require BinaryPR.
Require Import Lia.

(*We define uniform homomorphisms (of strings): Given strings of the same length, they output strings of the same length.*)
Section fixX.
  Variable (X Y : Type). 

  Definition homomorphism (h : list X -> list Y) := forall x1 x2, h (x1 ++ x2) = h x1 ++ h x2. 

  Lemma homo_nil h : homomorphism h -> h [] = []. 
  Proof. 
    intros. unfold homomorphism in H. specialize (H [] []). 
    cbn in H; rewrite H. destruct (h []) eqn:Heqn; cbn; [ congruence | ].  
    assert (|y :: l| = |(y :: l) ++ y :: l|) as H0 by congruence. 
    cbn in H0. rewrite app_length in H0. cbn in H0; lia. 
  Qed. 

  Lemma homo_cons h x l : homomorphism h -> h (x::l) = h [x] ++ h l.
  Proof. 
    intros. replace (x :: l) with ([x] ++ l) by now cbn. apply H. 
  Qed.

  Lemma homo_concat h : homomorphism h -> forall x, h (concat x) = concat (map h x). 
  Proof. 
    intros. induction x. 
    - cbn. apply homo_nil, H. 
    - cbn. rewrite H. now rewrite IHx. 
  Qed. 

  (*the last condition excludes the trivial homomorphism x ↦ ε *)
  Definition uniform_homomorphism (h : list X -> list Y) := homomorphism h /\ (forall x y, |h [x]| = |h [y]|) /\ (forall x, |h[x]| >= 1).

  Lemma unif_homo_length h x y : uniform_homomorphism h -> |x| = |y| -> |h x| = |h y|. 
  Proof. 
    intros (H1 & H2 & _). 
    revert y. induction x; intros. 
    - destruct y; cbn in *; [ | congruence]. now cbn. 
    - destruct y; cbn in *; [ congruence | ]. 
      replace (a :: x) with ([a] ++ x) by now cbn. replace (x0 :: y) with ([x0] ++ y) by now cbn. 
      rewrite !H1. rewrite !app_length. erewrite H2 with (y := x0). 
      rewrite IHx with (y := y); eauto. 
  Qed. 

  (*given an arbitrary function mapping elements of X into strings over Y, we can derive a homomorphism *)
  Definition canonicalHom (h' : X -> list Y) := fun (l : list X) => concat (map h' l). 
  Lemma canonicalHom_is_homomorphism h' : homomorphism (canonicalHom h'). 
  Proof. 
    unfold homomorphism. intros. unfold canonicalHom. 
    now rewrite map_app, concat_app. 
  Qed. 
End fixX. 

(*We show that we can apply a uniform homomorphism to a PR instance if the homomorphism is injective on its alphabet *)
Section fixInstance.  
  Variable (Y : finType).
  (*Context (Yeq : eq_dec Y). *)
  (*Context (Yfin : finTypeC (EqType Y)). *)


  Variable (fpr : PR). 

  Notation Sigma := (Sigma fpr).
  Notation offset := (offset fpr).
  Notation width := (width fpr).
  Notation init := (init fpr).
  Notation windows := (windows fpr).
  Notation final := (final fpr).
  Notation steps := (steps fpr). 

  Variable (h' : Sigma -> list Y).

  Definition h := canonicalHom h'. 
  
  Context (A0 : forall x, |h' x| >= 1). 
  Context (A1 : forall x y, |h' x| = |h' y|). 
  Context (A2 : injective h'). 
  Context (A3 : |elem Sigma| > 0). 

  Lemma h_unifHom : uniform_homomorphism h. 
  Proof. 
    repeat split. 
    - apply canonicalHom_is_homomorphism. 
    - intros. cbn. rewrite !app_nil_r. apply A1. 
    - intros. cbn. rewrite app_nil_r. apply A0. 
  Qed. 

  Lemma h_nil_cons x l : not (|h []| = |h (x :: l)|). 
  Proof. 
    intros H. replace (x ::l) with ([x] ++ l) in H by now cbn.
    rewrite (proj1 h_unifHom) in H. rewrite (homo_nil (proj1 h_unifHom)) in H. 
    rewrite !app_length in H. cbn in H. rewrite app_nil_r in H. 
    specialize (A0 x). lia.
  Qed. 

  Lemma h_length_inv l1 l2 : |h l1| = |h l2| -> |l1| = |l2|. 
  Proof. 
    revert l2. induction l1; intros. 
    + destruct l2; [easy | now apply h_nil_cons in H].  
    + destruct l2; [ symmetry in H; now apply h_nil_cons in H | ]. 
      cbn. f_equal. apply IHl1. 
      rewrite homo_cons in H; [ | apply h_unifHom]. 
      rewrite homo_cons with (x := e) in H; [ | apply h_unifHom].
      rewrite !app_length in H.
      rewrite (proj1 (proj2 h_unifHom)) with (y := e) in H. lia. 
  Qed. 

  Lemma h_length_inv' l1 l2 : h l1 = h l2 -> |l1| = |l2|. 
  Proof. intros; now apply h_length_inv. Qed. 

  Lemma list_eqn_length (X : Type) (l1 l2 : list X) : l1 = l2 -> |l1| = |l2|. 
  Proof. congruence. Qed. 

  Lemma h_injective l1 l2 : h l1 = h l2 -> l1 = l2. 
  Proof. 
    revert l2. induction l1; intros l2 H0. 
    - destruct l2; [cbn in *; reflexivity | ]. 
      cbn in H0. apply list_eqn_length in H0. rewrite app_length in H0. cbn in H0. 
      specialize (A0 e). lia. 
    - destruct l2; [ apply h_length_inv' in H0; cbn in *; congruence | ]. 
      rewrite homo_cons in H0; [ | apply h_unifHom ]. 
      rewrite homo_cons with (x := e) in H0; [ | apply h_unifHom]. 
      apply app_eq_length in H0 as (H0 & H0'); [ | apply (proj1 (proj2 (h_unifHom)))]. 
      apply IHl1 in H0'. 
      cbn in H0; rewrite !app_nil_r in H0. now apply A2 in H0. 
  Qed. 

  Lemma h_multiplier' : { k & (forall x, |h x| = k * (|x|)) /\ k >= 1}.
  Proof. 
    destruct elem; [ exists 0; cbn in A3; lia | ]. 
    exists (|h' e|). split; [ | apply A0]. intros x. 
    induction x; cbn. 
    - lia. 
    - rewrite app_length. unfold h, canonicalHom in IHx. rewrite IHx.       
      rewrite Nat.mul_succ_r. rewrite (A1 a e). lia. 
  Qed. 

  Definition k := projT1 h_multiplier'. 
  Lemma h_multiplier : forall x, |h x| = k * |x|. 
  Proof. intros. unfold k. destruct h_multiplier'. apply a. Qed. 

  Lemma k_ge : k >= 1. 
  Proof. unfold k. destruct h_multiplier'. apply a.  Qed. 

  Lemma h_nil_inv a : h a = [] -> a = []. 
  Proof. 
    specialize (h_multiplier a) as H. 
    destruct a; [ easy | ]. intros H0. 
    rewrite H0 in H. specialize k_ge as H1. cbn in *; nia. 
  Qed. 

  Lemma h_app_inv1 a u v : h a = u ++ v -> |u| = k -> exists a1 a2, a = a1::a2 /\ h [a1] = u /\ h a2 = v. 
  Proof. 
    intros.  destruct a. 
    - specialize (h_multiplier []) as H1. rewrite H in H1. rewrite app_length in H1. cbn in H1. specialize (k_ge) as H2. nia. 
    - rewrite homo_cons in H; [ | apply h_unifHom]. 
      specialize (h_multiplier [e]) as H1. cbn in H1. rewrite Nat.mul_1_r, app_nil_r in H1. 
      apply app_eq_length in H; [ | cbn in *; rewrite app_nil_r; lia]. 
      exists e, a. split;  [easy | tauto ]. 
  Qed. 

  Lemma h_app_inv a c u v : h a = u ++ v -> |u| = c * k -> exists a1 a2, a = a1 ++ a2 /\ h a1 = u /\ h a2 = v. 
  Proof. 
    intros. revert a u H0 H. induction c; intros. 
    - cbn in H0; destruct u; [ | cbn in H0; congruence]. 
      exists [], a. split; [ now cbn | split; [apply homo_nil, h_unifHom | cbn in H; apply H]]. 
    - cbn in H0. assert (k <= |u|) by lia. apply list_length_split1 in H1 as (s1 & s2 & H2 & H3 & ->). 
      rewrite H0 in H3. replace (k + c * k - k) with ( c * k) in H3 by nia. 
      rewrite <- app_assoc in H. apply h_app_inv1  in H as (a1 & a' & -> & H4 & H5); [ | apply H2] . 
      apply IHc in H5 as (a0 & a2 & -> & H5 & H6); [ | apply H3]. 
      exists (a1 :: a0), a2. cbn; split; [easy | split]. 
      + unfold h, canonicalHom in H5. cbn in H4; rewrite app_nil_r in H4. easy. 
      + apply H6. 
  Qed. 

  Definition hoffset := k * offset. 
  Definition hwidth := k * width. 
  Definition hinit := h init. 
  Definition hwindow win := match win with Build_PRWin prem conc => Build_PRWin (h prem) (h conc) end.
  Definition hwindows := map hwindow windows. 
  Definition hfinal := map h final. 
  Definition hsteps := steps. 

  Context (A : PR_wellformed fpr). 

  Lemma rewritesHead_homomorphism1 win a b : 
    win el windows -> rewritesHead win a b -> rewritesHead (hwindow win) (h a) (h b). 
  Proof. 
    unfold hwindow. destruct win. intros H0 ((c1 & H1) & (c2 & H2)). 
    subst. split; cbn -[canonicalHom]; rewrite (proj1 h_unifHom); unfold prefix; eauto.
  Qed. 

  Lemma rewritesHead_homomorphism2 win a1 a2 u v: 
    win el hwindows 
    -> |a1| = offset 
    -> |u| = k * offset 
    -> rewritesHead win (h a1 ++ h a2) (u ++ v) 
    -> exists b1, u = h b1 /\ |b1| = offset 
        /\ rewritesHead win (h a1 ++ h a2) (h b1 ++ v). 
  Proof. 
    intros. destruct H2 as ((c1 & H3) & (c2 & H4)). 
    unfold hwindows in H; apply in_map_iff in H as (win' & <- & H).  
    destruct win'; cbn in *. 
    destruct A as (_ & _ & (ak & A5 & ->) & _ & A4 & _). 
    apply A4 in H as (H & H'). cbn in *. 
    assert (|u| <= |h conc|) by (rewrite h_multiplier; nia). 
    apply list_length_split1 in H2 as (b1' & b2' & H2 & _ & H2'). 
    eapply h_app_inv in H2' as (b1 & b2 & -> & <- & <-); [ | rewrite H2, H1, Nat.mul_comm; reflexivity ]. 
    rewrite (proj1 h_unifHom), <-app_assoc in H4.
    apply app_eq_length in H4 as (-> & ->); [ | easy]. 
    exists b1. 
    split; [ easy | split]. 
    - rewrite h_multiplier in H1; specialize k_ge; nia. 
    - split; cbn. 
      + unfold prefix. exists c1. easy. 
      + unfold prefix. exists c2. now rewrite (proj1 h_unifHom), <- app_assoc. 
  Qed. 

  Lemma rewritesHead_homomorphism_iff win a b : 
    win el windows -> rewritesHead win a b <-> rewritesHead (hwindow win) (h a) (h b). 
  Proof. 
    split; intros.
    - now apply rewritesHead_homomorphism1.
    - unfold hwindow in H0. destruct win. destruct H0 as ((c1 & H1) & (c2 & H2)). 
      cbn in *. destruct A as (_ & _ & _ & _ & A4 & _ ). 
      eapply h_app_inv in H1 as (a1 & a2 & -> & H1 & <-); [ | rewrite Nat.mul_comm; apply h_multiplier].  
      eapply h_app_inv in H2 as (b1 & b2 & -> & H2 & <-); [ | rewrite Nat.mul_comm; apply h_multiplier]. 
      apply h_injective in H1 as <-.
      apply h_injective in H2 as <-.
      split; unfold prefix; eauto.  
  Qed. 

  Hint Constructors valid. 

  Lemma valid_homomorphism1 a b : |a| >= width -> valid offset width windows a b -> valid hoffset hwidth hwindows (h a) (h b).
  Proof. 
    intros H0. unfold hwidth, hoffset.
    induction 1. 
    + rewrite homo_nil; [eauto | apply h_unifHom]. 
    + rewrite app_length in H0. nia. 
    + rewrite !(proj1 h_unifHom). destruct win as [prem conc]. 
      econstructor 3. 
      * destruct (le_lt_dec width (|a|)). 
        -- apply IHvalid. nia. 
        --(*we show that for this case, the whole string is covered by the rule *)
          clear IHvalid H2 H3. 
          specialize (valid_multiple_of_offset H) as (m & H').
          eapply valid_vacuous with (m := m). 
          ++ rewrite !h_multiplier. apply valid_length_inv in H. nia. 
          ++ rewrite !h_multiplier. specialize k_ge. nia. 
          ++ rewrite h_multiplier. nia. 
      * rewrite h_multiplier. specialize k_ge. nia. 
      * rewrite h_multiplier. specialize k_ge. nia. 
      * unfold hwindows. apply in_map_iff. exists (Build_PRWin prem conc). split; [ | apply H3]. reflexivity. 
      * rewrite <- !(proj1 h_unifHom). apply rewritesHead_homomorphism_iff; assumption.
  Qed. 

  Lemma valid_homomorphism2 a b' : |a| >= width -> valid hoffset hwidth hwindows (h a) b' -> exists b, b' = h b /\ valid offset width windows a b.
  Proof. 
    unfold hoffset, hwidth. intros.  
    remember (h a). revert a Heql H. induction H0. 
    - intros. symmetry in Heql. apply h_nil_inv in Heql. subst. exists []. 
      split; [symmetry; apply homo_nil, (proj1 h_unifHom) | eauto ]. 
    - intros. clear IHvalid. symmetry in Heql.
      eapply h_app_inv in Heql as (a1 & a2 & -> & F1 & F2); [ | rewrite Nat.mul_comm; apply H1]. 
      rewrite <- F1, h_multiplier in H1. 
      rewrite <- F2, h_multiplier in H. rewrite app_length in H3. specialize k_ge. nia. 
    - intros. symmetry in Heql.  
      eapply h_app_inv in Heql as (a1 & a2 & -> & F1 & F2); [ | rewrite Nat.mul_comm; apply H]. 
      subst. 
      specialize (k_ge) as F. 
      apply rewritesHead_homomorphism2 in H3 as (b1 & -> & H7 & H3); 
        [ | easy | rewrite h_multiplier in H; specialize k_ge; nia | easy ]. 
      specialize (h_multiplier a1) as H6. 
      assert (|a1| = offset) by nia. 
      destruct (le_lt_dec width (|a2|)) as [l|l]. 
      + (*we can apply the IH *)
        unfold hwindows in H2. apply in_map_iff in H2 as (rule' & <- & H10). 
        assert (|a2| >= width) as l' by lia; clear l.
        specialize (IHvalid a2 eq_refl l') as (b0 & -> & IH). 
        exists (b1 ++ b0). repeat split.
        * now rewrite (proj1 h_unifHom). 
        * econstructor 3; [ easy | easy | easy | easy | ]. 
          rewrite <- !(proj1 h_unifHom) in H3. apply rewritesHead_homomorphism_iff in H3; eauto.
      + (*the interesting base case *)
        clear IHvalid H6. unfold hwindows in H2. apply in_map_iff in H2 as (rule' & <- & H10). 
        (*we show: the rule actually matches the whole string *)
        remember H3 as H30. clear HeqH30. (*we'll need the original hypothesis later *)
        specialize H3 as ((rest' & H3') & (rest & H3)). (*show rest = [] *)
        (*we need some structural assumptions *)
        destruct A as (_ & _ & A4 & _ & A5 & _ ). 
        assert (rest = []) as ->. 
        { 
          assert (|a1++a2| = width). 
          { 
            specialize (valid_multiple_of_offset H0) as (k1 & H0').
            rewrite app_length. destruct A4 as (ak & _ & A4). rewrite A4 in *. 
            rewrite app_length in H4. 
            rewrite h_multiplier in H0'. 
            enough (ak = S k1) by nia. nia. 
          }
          clear H4 A4. 
          specialize (A5 _ H10) as (A5 & A5'). 
          assert (rest' = []) as ->. 
          { (*we now know: | h(a1 ++ a2)| = k * width, but also |prem (hwindow rule')| = k * width *)
            clear l H7 H3. 
            assert (|h a1 ++ h a2| = | prem (hwindow rule') ++ rest'|) by congruence. 
            rewrite <- (proj1 h_unifHom) in H3. 
            destruct rule' as (prem & conc); cbn in *. rewrite app_length in H3. 
            rewrite !h_multiplier, H2, A5 in H3.  destruct rest'; cbn in H3; [easy | nia]. 
          } 
          enough (|h b1 ++ b| = |h a1 ++ h a2|) as H11.
          { rewrite H3, H3' in H11. rewrite !app_length in H11. 
            destruct rule'; cbn in *. rewrite !h_multiplier, A5, A5' in H11. 
            destruct rest; cbn in H11; [auto | lia]. 
          }
          rewrite !app_length. apply valid_length_inv in H0. lia.
        }
        rewrite app_nil_r in H3.  destruct rule'; cbn in *.  

        symmetry in H3. eapply h_app_inv in H3 as (b1' & b2 & -> & H3 & <-); [ | rewrite h_multiplier, Nat.mul_comm; reflexivity]. 
        apply h_injective in H3 as ->. 
        (*we have now arrived at a point where we know that the conclusion is also of the form h _  *)
        exists (b1 ++ b2). split; [now rewrite !(proj1 h_unifHom) | ].
        (*thus, we can show the validity *)
        econstructor 3. 
        -- specialize (valid_multiple_of_offset H0) as (k1 & H0'). eapply valid_vacuous.  
           ++ apply valid_length_inv in H0. rewrite !h_multiplier in H0. nia. 
           ++ apply l.  
           ++ rewrite h_multiplier in H0'. enough (|a2| = k1 * offset) as G by apply G. nia. 
        -- easy. 
        -- easy.  
        -- easy.  
        -- apply rewritesHead_homomorphism_iff; [ apply H10 | rewrite !(proj1 h_unifHom); apply H30].
  Qed. 

  (*we can obtain an equivalence, but its second direction is significantly weaker than the direction which we've just shown *)
  Lemma valid_homomorphism_iff a b : 
    |a| >= width -> valid offset width windows a b <-> valid hoffset hwidth hwindows (h a) (h b).
  Proof. 
    intros H0; split. unfold hwidth, hoffset. 
    - apply valid_homomorphism1; easy.  
    - intros. apply valid_homomorphism2 in H as (b' & Heq & H1 ). 
      + symmetry in Heq. apply h_injective in Heq; easy. 
      + apply H0. 
  Qed. 

  Lemma valid_relpower_homomorphism1 a b steps : 
    |a| >= width -> relpower (valid offset width windows) steps a b -> relpower (valid (k * offset) (k * width) hwindows) steps (h a) (h b).
  Proof. 
    intros H. induction 1; [ eauto | ]. econstructor. 
    + apply valid_homomorphism_iff; [ apply H | easy ]. 
    + apply IHrelpower.  apply valid_length_inv in H0. lia. 
  Qed. 

  Lemma valid_relpower_homomorphism2 a b' steps: 
    |a| >= width -> relpower (valid (k * offset) (k * width) hwindows) steps (h a) b' -> exists b, b' = h b /\ relpower (valid offset width windows) steps a b. 
  Proof. 
    intros. remember (h a). revert a Heql H. induction H0; intros. 
    - exists a0. split; eauto. 
    - subst. apply valid_homomorphism2 in H as (b' & -> & H); [ | easy ]. 
      edestruct (IHrelpower b' eq_refl) as (c' & -> & IH). 
      + apply valid_length_inv in H; lia. 
      + exists c'; split; [ easy | ]. econstructor; easy. 
  Qed. 

  (*again a slightly weaker equivalence *)
  Lemma valid_relpower_homomorphism_iff a b steps : 
    |a| >= width -> relpower (valid offset width windows) steps a b <-> relpower (valid (k * offset) (k * width) hwindows) steps (h a) (h b).
  Proof. 
    intros. split. 
    - now apply valid_relpower_homomorphism1.  
    - intros (b' & Heq & H1)%valid_relpower_homomorphism2; [ | easy ]. 
      symmetry in Heq; apply h_injective in Heq. easy. 
  Qed. 

  Lemma final_agree sf : |init| = |sf| -> satFinal offset (length init) final sf <-> satFinal hoffset (length hinit) hfinal (h sf). 
  Proof. 
    intros G. unfold satFinal, hoffset, hfinal. split; intros (subs & k0 & H1 & H2 & H3). 
    - rewrite G in H2. exists (h subs), (k0). 
      split; [now apply in_map_iff | split; [ unfold hinit; rewrite h_multiplier; nia | ]]. 
      destruct H3 as (b & H3). rewrite <- (firstn_skipn (k0 * offset) sf). 
      rewrite (proj1 h_unifHom). 
      (*we make a case analysis: if subs = [], the claim holds trivially *)
      (*otherwise, we know that sf has a length of at least k0 * offset *)
      destruct subs. 
      + rewrite homo_nil; [ | apply h_unifHom]. unfold prefix; cbn; eauto. 
      + rewrite skipn_app. 
        * rewrite H3. rewrite (proj1 h_unifHom). exists (h b); eauto. 
        * rewrite h_multiplier. rewrite firstn_length. 
          enough (|sf| >= k0 * offset) by nia. 
          specialize (skipn_length (k0 * offset) sf). rewrite H3. cbn. nia. 
    - apply in_map_iff in H1 as (subs' & <- & H1). 
      exists subs', k0; split; [ apply H1 | ]. 
      destruct H3 as (b & H3). unfold prefix. 
      rewrite <- (firstn_skipn (k0 * offset) sf), (proj1 h_unifHom) in H3. 
      unfold hinit in H2; rewrite h_multiplier in H2. split; [ specialize k_ge; nia | ]. 
      rewrite skipn_app in H3. 
      + eapply h_app_inv in H3 as (a1 & a2 & -> & H4 & H5); [ | rewrite Nat.mul_comm, h_multiplier; easy ].
        exists a2. enough (a1 = subs') by easy. 
        symmetry; apply h_injective. easy.
      + rewrite h_multiplier. rewrite firstn_length. nia. 
  Qed. 
      
  Lemma PR_homomorphism_iff : 
    (exists sf, relpower (valid offset width windows) steps init sf /\ satFinal offset (|init|) final sf) 
    <-> (exists sf, relpower (valid hoffset hwidth hwindows) hsteps hinit sf /\ satFinal hoffset (|hinit|) hfinal sf). 
  Proof. 
    unfold hsteps, hinit, hoffset, hwidth. 
    destruct A as (_ & _ & _  & A4 &_). 
    split; intros. 
    - destruct H as (sf & H1 & H2 ). 
      exists (h sf). split. 
      + apply valid_relpower_homomorphism_iff; easy. 
      + clear A4. apply final_agree. 
        * apply relpower_valid_length_inv in H1. lia. 
        * apply H2. 
    - destruct H as (sf & H1 & H2). 
      apply valid_relpower_homomorphism2 in H1 as (sf' & -> & H1).
      + exists sf'. split; [ easy | ].
        clear A4. apply final_agree. 
        * apply relpower_valid_length_inv in H1; easy. 
        * apply H2. 
      + apply A4. 
  Qed. 

End fixInstance. 


