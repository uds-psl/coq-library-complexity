From PslBase Require Import Base. 
From Undecidability.L.Complexity.Cook Require Import Prelim FSAT BinaryPR. 
From Undecidability.L.Complexity Require Import Tactics. 

From Undecidability.L.Datatypes Require Import Lists. 

Require Import Lia. 

(*a generator type - given an index for the first variable to use, generate a formula *)
Definition formulagen := nat -> formula. 

Section fixInstance. 
  Variable (bpr : BinaryPR). 
  
  Notation offset := (offset bpr). 
  Notation width := (width bpr). 
  Notation init := (init bpr). 
  Notation windows := (windows bpr).
  Notation final := (final bpr).
  Notation steps := (steps bpr). 

  Context (A : BinaryPR_wellformed bpr). 
  Notation llength := (length init). 

  Implicit Types (a : assgn) (v : var). 

  Notation Ffalse := (¬Ftrue). 
  Fixpoint listOr (l : list formula) := match l with
    | [] => Ffalse 
    | a :: l => a ∨ listOr l 
    end. 

  Fixpoint listAnd (l : list formula) := match l with 
    | [] => Ftrue
    | a :: l => a ∧ listAnd l
    end.  

  (*generate the list of values assigned to the variables in range [lower, lower + len) *)
  Fixpoint explicitAssignment a lower len := 
    match len with
      | 0 => [] 
      | S len => explicitAssignment a lower len ++ [list_in_decb Nat.eqb a (lower + len)]
    end. 


  Lemma explicitAssignment_length a lower len : |explicitAssignment a lower len| = len. 
  Proof. 
    revert lower. induction len; intros; cbn. 
    - reflexivity. 
    - rewrite app_length, IHlen. now cbn.
  Qed. 

  Lemma explicitAssignment_nth a lower len k : 
     k < len -> nth_error (explicitAssignment a lower len) k = Some (evalVar a (lower + k)). 
  Proof. 
    intros. induction len. 
    - lia. 
    - cbn. destruct (le_lt_dec len k).
      + assert (len = k) as <- by lia.
        rewrite nth_error_app2; rewrite explicitAssignment_length; [ rewrite Nat.sub_diag; cbn | lia]. easy.
      + rewrite nth_error_app1; [ | rewrite explicitAssignment_length; easy ]. now apply IHlen. 
  Qed. 

  Lemma explicitAssignment_lenO a s l : explicitAssignment a s l = [] <-> l = 0. 
  Proof. 
    specialize (explicitAssignment_length a s l). 
    split; intros. 
    - rewrite H0 in H. easy. 
    - subst. destruct explicitAssignment; cbn in *; congruence. 
  Qed. 

  Corollary explicitAssignment_lenO' a l : explicitAssignment a l 0 = []. 
  Proof. 
    apply explicitAssignment_lenO. easy.
  Qed. 

  Lemma explicitAssignment_app a l1 len1 len2: explicitAssignment a l1 (len1 + len2) = explicitAssignment a l1 len1 ++ explicitAssignment a (l1 + len1) len2. 
  Proof. 
    induction len2; cbn. 
    - now rewrite Nat.add_0_r, app_nil_r. 
    - rewrite Nat.add_succ_r. cbn. rewrite IHlen2, app_assoc. easy. 
  Qed. 

  Lemma explicitAssignment_length' a n: |explicitAssignment a 0 n| = n.
  Proof. rewrite explicitAssignment_length. lia. Qed. 


  Inductive varsInRange (min max : nat) : formula -> Prop := 
    | varsInRangeTrue : varsInRange min max Ftrue
    | varsInRangeVar v : v >= min -> v < max -> varsInRange min max v
    | varsInRangeNeg f : varsInRange min max f -> varsInRange min max (¬f)
    | varsInRangeAnd f1 f2 : varsInRange min max f1 -> varsInRange min max f2 -> varsInRange min max (f1 ∧ f2)
    | varsInRangeOr f1 f2 : varsInRange min max f1 -> varsInRange min max f2 -> varsInRange min max (f1 ∨ f2). 

  Hint Constructors varsInRange. 

  Lemma varsInRange_monotonous (min1 max1 min2 max2 : nat) f : min2 <= min1 -> max2 >= max1 -> varsInRange min1 max1 f -> varsInRange min2 max2 f. 
  Proof. intros. induction H1; eauto. constructor 2; lia. Qed. 

  (*we define what it means for a formula to encode a predicate *)
  Definition predicate := list bool -> Prop. 
  Implicit Type (p : predicate).
  Definition encodesPredicateAt (start : nat) (l : nat) f p:= 
    varsInRange start (l + start) f /\ forall a, satisfies a f <-> p (explicitAssignment a start l). 

  Definition projVars start len (l : list bool) := firstn len (skipn start l). 

  Lemma projVars_length l s m : |l| >= (s + m) -> |projVars s m l| = m. 
  Proof. 
    intros. unfold projVars. rewrite firstn_length. rewrite skipn_length. lia. 
  Qed. 

  Lemma projVars_app1 l1 l2 m : |l1| = m -> projVars 0 m (l1 ++ l2) = l1.
  Proof. 
    intros. unfold projVars. cbn. rewrite firstn_app. subst. 
    now rewrite Nat.sub_diag, firstn_O, app_nil_r, firstn_all.
  Qed. 

  Lemma projVars_app2 l1 l2 u m : |l1| = u -> projVars u m (l1 ++ l2) = projVars 0 m l2. 
  Proof. 
    intros. unfold projVars. rewrite skipn_app; [ | easy]. now cbn. 
  Qed. 

  Lemma projVars_app3 l1 l2 u1 u2 m : |l1| = u1 -> projVars (u1 + u2) m (l1 ++ l2) = projVars u2 m l2. 
  Proof. 
    intros. unfold projVars. erewrite skipn_add; [ easy| lia]. 
  Qed. 

  Lemma projVars_all l m : m = |l| -> projVars 0 m l = l. 
  Proof.
    intros. unfold projVars. cbn. rewrite H. apply firstn_all. 
  Qed. 

  (*encodings of two predicates can be combined*)
  Definition combinedLength start1 start2 l1 l2 := max (start1 +l1) (start2 + l2) - min start1 start2. 
  Definition combinedStart start1 start2 := min start1 start2. 

  Lemma list_eq_nth_error (X : Type) (l1 l2 : list X) : 
    l1 = l2 <-> (|l1| = |l2| /\ forall k, k < |l1| -> nth_error l1 k = nth_error l2 k). 
  Proof. 
    split; [intros -> | intros (H1 & H2)]. 
    - split; [easy | intros; easy ]. 
    - revert l2 H1 H2; induction l1; intros; destruct l2. 
      + easy. 
      + cbn in H1; congruence. 
      + cbn in H1; congruence. 
      + cbn in H1. apply Nat.succ_inj in H1. enough (a = x /\ l1 = l2) by easy; split. 
        * specialize (H2 0 (Nat.lt_0_succ (|l1|))). now cbn in H2. 
        * apply IHl1; [ apply H1 | ]. 
          intros. apply Nat.succ_lt_mono in H. specialize (H2 (S k) H). now cbn in H2. 
  Qed. 

  Lemma nth_error_firstn (X : Type) k m (l : list X): k < m -> nth_error (firstn m l) k = nth_error l k. 
  Proof. 
    revert k l. induction m; intros. 
    - lia.
    - destruct k; cbn; destruct l; easy. 
  Qed. 

  Lemma nth_error_skipn (X : Type) k m (l : list X) : nth_error (skipn m l) k = nth_error l (m + k). 
  Proof. 
    revert k l. induction m; intros. 
    - easy. 
    - destruct l; cbn; [ now destruct k | apply IHm]. 
  Qed. 

  Lemma projVars_combined1 s1 s2 l1 l2 a: explicitAssignment a s1 l1 = projVars (s1 - combinedStart s1 s2) l1 (explicitAssignment a (combinedStart s1 s2) (combinedLength s1 s2 l1 l2)).
  Proof. 
    unfold projVars. 
    apply list_eq_nth_error. split. 
    - rewrite explicitAssignment_length. unfold combinedStart, combinedLength. rewrite firstn_length. 
      rewrite skipn_length. rewrite explicitAssignment_length. lia. 
    - intros. rewrite explicitAssignment_length in H. unfold combinedStart, combinedLength. 
      rewrite nth_error_firstn; [ | apply H].  
      rewrite nth_error_skipn. rewrite !explicitAssignment_nth; [easy | lia | lia]. 
  Qed. 

  Lemma projVars_combined2 s1 s2 l1 l2 a: explicitAssignment a s2 l2 = projVars (s2 - combinedStart s1 s2) l2 (explicitAssignment a (combinedStart s1 s2) (combinedLength s1 s2 l1 l2)). 
  Proof. 
    unfold combinedStart, combinedLength. rewrite Nat.min_comm. rewrite Nat.max_comm. apply projVars_combined1. 
  Qed. 

  Lemma encodesPredicate_and start1 start2 l1 l2 f1 f2 p1 p2 : 
    encodesPredicateAt start1 l1 f1 p1 -> encodesPredicateAt start2 l2 f2 p2 
    -> encodesPredicateAt (combinedStart start1 start2) (combinedLength start1 start2 l1 l2) (f1 ∧ f2) (fun m => (p1 (projVars (start1 - combinedStart start1 start2) l1 m) /\ p2 (projVars (start2 - combinedStart start1 start2) l2 m)) /\ |m| = combinedLength start1 start2 l1 l2). 
  Proof. 
    intros (G1 & G2) (F1 & F2). split. 
    - constructor. 
      + eapply varsInRange_monotonous; [ | | apply G1]; unfold combinedStart, combinedLength; lia. 
      + eapply varsInRange_monotonous; [ | | apply F1]; unfold combinedStart, combinedLength; lia. 
    - intros a. split; intros H. 
      + apply evalFormula_and_iff in H as (H1%G2 & H2%F2). 
        rewrite <- projVars_combined1, <- projVars_combined2, explicitAssignment_length. easy. 
      + rewrite <- projVars_combined1, <- projVars_combined2 in H. 
        unfold satisfies. apply evalFormula_and_iff. 
        split; [apply G2, H | apply F2, H]. 
  Qed. 

  Lemma encodesPredicate_or start1 start2 l1 l2 f1 f2 p1 p2 : 
    encodesPredicateAt start1 l1 f1 p1 -> encodesPredicateAt start2 l2 f2 p2 
    -> encodesPredicateAt (combinedStart start1 start2) (combinedLength start1 start2 l1 l2) (f1 ∨ f2) (fun m => (p1 (projVars (start1 - combinedStart start1 start2) l1 m) \/ p2 (projVars (start2 - combinedStart start1 start2) l2 m)) /\ |m| = combinedLength start1 start2 l1 l2).
  Proof. 
    intros (G1 & G2) (F1 & F2). split. 
    - constructor. 
      + eapply varsInRange_monotonous; [ | | apply G1]; unfold combinedStart, combinedLength; lia. 
      + eapply varsInRange_monotonous; [ | | apply F1]; unfold combinedStart, combinedLength; lia. 
    - intros a. split; intros H. 
      + split; [ | rewrite explicitAssignment_length; easy]. 
        apply evalFormula_or_iff in H as [H1%G2 | H2%F2]. 
        * left. rewrite <- projVars_combined1. apply H1.
        * right. rewrite <- projVars_combined2. apply H2. 
      + rewrite <- projVars_combined1, <- projVars_combined2 in H. 
        destruct H as ([H | H] & _); apply evalFormula_or_iff; [left; apply G2, H | right; apply F2, H].  
  Qed. 

  (*encoding of single literals *)
  Definition encodeLiteral v (sign : bool) : formula := if sign then v else ¬ v. 

  Lemma encodeLiteral_correct v sign : forall a, satisfies a (encodeLiteral v sign) <-> evalVar a v = sign. 
  Proof. 
    intros. unfold satisfies, encodeLiteral. destruct sign; cbn; [ tauto |simp_bool; tauto ]. 
  Qed. 

  Lemma encodeLiteral_varsInRange v sign : varsInRange v (S v) (encodeLiteral v sign). 
  Proof. 
    unfold encodeLiteral. destruct sign; eauto. 
  Qed. 

  Lemma encodeLiteral_encodesPredicate v sign : encodesPredicateAt v 1 (encodeLiteral v sign) (fun l => l = [sign]). 
  Proof. 
    split. 
    - apply encodeLiteral_varsInRange. 
    - intros. split; intros. 
      + apply encodeLiteral_correct in H. specialize (explicitAssignment_length a v 1) as H1. 
        assert (0 < 1) as H2 by lia. 
        specialize (@explicitAssignment_nth a v 1 0 H2) as H3. 
        destruct explicitAssignment as [ | s l]; cbn in H1; [ congruence | destruct l; [ | cbn in H1; congruence]]. 
        cbn in H3. now inv H3. 
      + apply encodeLiteral_correct. assert (0 < 1) as H2 by lia.
        specialize (@explicitAssignment_nth a v 1 0 H2) as H1. 
        rewrite H in H1; cbn in H1. now inv H1. 
  Qed. 

  Lemma encodesPredicateAt_extensional s l f p1 p2 : (forall m, p1 m <-> p2 m) -> encodesPredicateAt s l f p1 <-> encodesPredicateAt s l f p2. 
  Proof. 
    intros. unfold encodesPredicateAt. setoid_rewrite H. easy. 
  Qed. 
  
  (*encoding of lists *)
  Fixpoint encodeListAt (startA : nat) (l : list bool) :=
    match l with 
    | [] => Ftrue
    | x :: l => (encodeLiteral startA x) ∧ (encodeListAt (1 + startA) l)
    end. 

  Lemma firstn_all_inv (X : Type) (m l : list X) : |l| = |m| -> firstn (|l|) m = l -> m = l.
  Proof. 
    revert l; induction m; intros.
    - destruct l; cbn; easy. 
    - destruct l; cbn in *; [easy | ]. inv H0. apply Nat.succ_inj in H. 
      rewrite H3. f_equal. now apply IHm. 
  Qed. 

  Lemma encodeListAt_encodesPredicate start l : encodesPredicateAt start (|l|) (encodeListAt start l) (fun m => m = l).
  Proof. 
    revert start. induction l; intros. 
    - cbn. split; [eauto | ]. unfold satisfies.  
      intros; split. 
      + intros _. destruct start; now cbn. 
      + intros _. easy. 
    - cbn. specialize (@encodesPredicate_and start (S start) 1 (|l|) (encodeLiteral start a) (encodeListAt (S start) l) _ _ (encodeLiteral_encodesPredicate start a) (IHl (S start))) as H1.
      replace (combinedStart start (S start)) with (start) in H1 by (unfold combinedStart; lia). 
      replace (combinedLength start (S start) 1 (|l|)) with (S (|l|)) in H1 by (unfold combinedLength; lia). 
      rewrite Nat.sub_diag in H1. replace (S start - start) with 1 in H1 by lia. 
      eapply encodesPredicateAt_extensional; [ | apply H1]. 
      intros. unfold projVars. 
      destruct m; cbn; [split; intros; easy | ]. 
      split. 
      + intros H. inv H. now rewrite firstn_all.
      + intros ((H0 & H2) & H3). inv H0. f_equal. apply Nat.succ_inj in H3. 
        now apply firstn_all_inv. 
  Qed. 

  Ltac encodesPredicateAt_comp_simp H := 
    unfold combinedStart, combinedLength in H;
    try (rewrite Nat.min_l in H by nia); try (rewrite Nat.min_r in H by nia);
    try (rewrite Nat.max_l in H by nia); try (rewrite Nat.max_r in H by nia);
    try rewrite !Nat.sub_diag in H; cbn -[projVars] in H.

  (*encoding of windows *)
  Definition encodeWindowAt (startA startB : nat) (win : PRWin bool) := encodeListAt startA (prem win) ∧ encodeListAt startB (conc win). 
  Lemma encodeWindowAt_encodesPredicate start len win : win el windows -> encodesPredicateAt start (len + width) (encodeWindowAt start (start + len) win) (fun m => projVars 0 width m = prem win /\ projVars len width m = conc win /\ |m| = len + width). 
  Proof. 
    intros H0. 
    specialize (encodesPredicate_and (encodeListAt_encodesPredicate start (prem win)) (encodeListAt_encodesPredicate (start + len) (conc win))) as H. 
    destruct A as (_ & _ & _ & A0 & A1 & _). apply A1 in H0 as (H0 & H0').
    encodesPredicateAt_comp_simp H. 
    rewrite !H0 in H. rewrite !H0' in H.
    replace (start + len + width - start) with (len + width) in H by lia. 
    replace (start + len - start) with len in H by lia.
    unfold encodeWindowAt. eapply encodesPredicateAt_extensional; [ | apply H].
    tauto.
  Qed.

  Definition encodeWindowsAt (startA startB : nat) := listOr (map (encodeWindowAt startA startB) windows). 

  Lemma skipn_firstn_shift (X : Type) (m : list X) len l : skipn l (firstn len m) = firstn (len - l) (skipn l m). 
  Proof. 
    revert l len. induction m; cbn; intros. 
    - rewrite !firstn_nil, !skipn_nil, firstn_nil. easy. 
    - destruct len. 
      + cbn. now destruct l.
      + cbn. destruct l; cbn; [ easy | ]. now rewrite IHm. 
  Qed. 

  Lemma skipn_skipn (X : Type) (m : list X) l1 l2 : skipn l1 (skipn l2 m) = skipn (l1 + l2) m. 
  Proof. 
    revert l1 l2. 
    induction m; intros; destruct l2; cbn; try now rewrite !skipn_nil. 
    - now rewrite Nat.add_0_r. 
    - rewrite IHm. rewrite Nat.add_succ_r. easy. 
  Qed. 

  Lemma skipn_firstn_skipn (X : Type) (m : list X) l1 l2 len2 : 
    skipn l1 (firstn len2 (skipn l2 m)) = firstn (len2 - l1) (skipn (l1 + l2) m). 
  Proof. 
    intros. 
    rewrite skipn_firstn_shift. now rewrite skipn_skipn. 
  Qed. 

  Lemma projVars_comp l1 l2 len1 len2 m: projVars l1 len1 (projVars l2 len2 m) = projVars (l1 + l2) (min len1 (len2 - l1)) m. 
  Proof. 
    unfold projVars. intros. 
    rewrite skipn_firstn_skipn. rewrite firstn_firstn. reflexivity. 
  Qed. 

  Lemma encodeWindowsAt_encodesPredicate len start : len >= width -> encodesPredicateAt start (len + width) (encodeWindowsAt start (start + len)) (fun m => exists win, win el windows /\ projVars 0 width m = prem win /\ projVars len width m = conc win /\ |m| = len + width). 
  Proof. 
    intros F0.
    specialize (encodeWindowAt_encodesPredicate) as H1. 
    unfold encodeWindowsAt. 
    induction windows. 
    - cbn. split. 
      + eauto. 
      + intros; split. 
        * unfold satisfies. cbn. congruence. 
        * intros (win & [] & _). 
    - cbn. match type of IHl with ?a -> _ => assert a as H by (intros; apply H1; eauto); apply IHl in H; clear IHl end. 
      specialize (H1 start len a (or_introl eq_refl)). 
      specialize (encodesPredicate_or H1 H) as H2. clear H1 H. 
      cbn in H2. 
      destruct A as (_ & _ & (k & A1 & A2) & _).
      encodesPredicateAt_comp_simp H2. 
      replace (start + (len + width) - start) with (len + width) in H2 by lia.
      eapply encodesPredicateAt_extensional; [ | apply H2]. 
      intros; cbn. 
      rewrite !projVars_comp. cbn. rewrite !Nat.min_l by lia. rewrite Nat.add_0_r. split; intros. 
      + destruct H as (win & [<- | H] & F1 & F2 & F3); (rewrite projVars_length; [ split; [ | easy] | easy]); [now left | right; eauto].
      + destruct H as ([(F1 & F2 & F3) | (win & H & F1 & F2 & F3)] & F4); eauto 7. 
  Qed. 

  (*we only need to place a window every offset fields, but subtracting offset isn't structurally recursive *)
  (*therefore we use a stepindex (initalise to the same value as l) *)
  Fixpoint encodeWindowsInLine' (stepindex l : nat) (startA startB : nat) := 
    if l <? width then Ftrue 
                  else match stepindex with 
                    | 0 => Ftrue
                    | S stepindex => encodeWindowsAt startA startB ∧ encodeWindowsInLine' stepindex (l - offset) (startA + offset) (startB + offset)
                    end.

  Lemma encodeWindowsInLine'_stepindex_monotone index index' startA startB : index' >= index -> encodeWindowsInLine' index index startA startB = encodeWindowsInLine' index' index startA startB. 
  Proof. 
    intros. 
    destruct A as (A1 & _).
    revert index' H.  induction index; intros. 
    - cbn. destruct index'; cbn; (destruct width; [ lia | easy]).
    - destruct index'; [lia | ]. apply le_S_n in H. apply IHindex in H. 
      cbn. 
  Admitted.

  SearchAbout firstn.
  Lemma firstn_add (X : Type) (m : list X) l1 l2 : firstn (l1 + l2) m = firstn l1 m ++ firstn l2 (skipn l1 m). 
  Proof. 
    revert l1 l2. induction m; intros. 
    - now rewrite !skipn_nil, !firstn_nil.
    - destruct l1; cbn; [ easy | ]. now rewrite IHm. 
  Qed. 

  Lemma projVars_add s l1 l2 m : projVars s (l1 + l2) m = projVars s l1 m ++ projVars (s + l1) l2 m. 
  Proof. 
    unfold projVars. rewrite firstn_add, skipn_skipn. now rewrite Nat.add_comm. 
  Qed.

  Lemma encodeWindowsInLine'_encodesPredicate start l : l <= llength -> (exists k, l = k * offset) -> encodesPredicateAt start (l + llength) (encodeWindowsInLine' l l start (start + llength)) (fun m => valid offset width windows (projVars 0 l m) (projVars llength l m) /\ |m| = l + llength). 
  Proof. 
    intros A0.
    (*need strong induction *)
    destruct A as (A1 & A4 & A2 & A5 & A7 & A3). 
    revert start A0.  
    apply complete_induction with (x := l). clear l. intros l IH. intros. 

    destruct l.
    - cbn. destruct width; [ lia | ]. split; [eauto | ]. 
      intros a. split; [ intros; split; [constructor | ] | intros _; unfold satisfies; eauto]. now rewrite explicitAssignment_length. 
    - destruct (le_lt_dec width (S l)). 
      + assert (~ (S l) < width) as H3%Nat.ltb_nlt by lia. cbn -[projVars]; setoid_rewrite H3. 
        destruct offset as [ | offset]; [ lia | ].
        (* we use the IH for l - offset *)
 
        assert (S l - S offset < S l) as H1 by lia. apply IH with (start := start + S offset) in H1. 2: nia. 
        2: { destruct H as (k & H). destruct k; [ lia | ]. exists k. lia. }
        clear H IH. 
        assert (llength >= width) as H0 by lia.
        apply (encodeWindowsAt_encodesPredicate start) in H0. 
        specialize (encodesPredicate_and H0 H1) as H2. clear H1 H0.
        encodesPredicateAt_comp_simp H2. 
        replace (start + S offset + llength) with (start + llength + S offset) in H2 by lia. 
        replace (start + S offset + (l - offset + llength) - start) with (S (l + llength)) in H2. 
        2: { destruct A2 as (? & A2 & A6). nia. }
        
        rewrite encodeWindowsInLine'_stepindex_monotone with (index' := l) in H2; [ | lia].
        eapply encodesPredicateAt_extensional; [ | apply H2].
        clear H2 H3. 
        intros. 
        destruct A2 as (k & A2 & A2').
        assert (S l = S offset + (S l - S offset)) as H by nia.  
        split; intros. 
        * destruct H0 as (H1 & H2). rewrite projVars_length; [ | easy]. 
          rewrite H in H1. clear H. 
          rewrite !projVars_add in H1. inv H1.
          2 : { exfalso. apply list_eq_length in H. rewrite !app_length in H. rewrite !projVars_length in H; [ | easy | easy]. nia. }
          1: { exfalso. apply list_eq_length in H0. rewrite !app_length in H0. rewrite projVars_length in H0; [ | cbn; nia]. cbn in H0. lia. } 

          apply app_eq_length in H as (-> & ->); [ | rewrite projVars_length; [easy | nia] ].
          apply app_eq_length in H0 as (-> & ->); [ | rewrite projVars_length; [easy | nia]]. 
          specialize (@projVars_length m 0 (S l)) as H8.
          rewrite projVars_length; [ | nia]. split; [ split; [ | split; [ | easy]] | easy]; clear H8.
          -- exists win. rewrite !projVars_comp; cbn. rewrite !Nat.min_l by lia. 
             rewrite !Nat.add_0_r.
             clear H3 H4 H5. rewrite <- !projVars_add in H7. 
             replace (S offset + (l - offset)) with (width + (S l - width)) in H7 by nia. 
             rewrite !projVars_add in H7.
             split; [ easy | split; [ | split; [ | easy]]]; apply A7 in H6 as (H6 & H6'). 
             ++ destruct H7 as ((b & H7) & _). eapply app_eq_length in H7; [ easy| rewrite projVars_length; easy ]. 
             ++ destruct H7 as (_ & (b & H7)). eapply app_eq_length in H7; [ easy | rewrite projVars_length; easy].
          -- clear H7 H6. 
             rewrite projVars_comp. cbn. replace (start + S offset - start) with (S offset) by lia. rewrite Nat.min_l by lia. 
             rewrite projVars_comp. cbn. rewrite Nat.min_l by lia. 
             apply H3. 
        * (*other direction of the equivalence *)
          destruct H0 as ((H1  & (H2 & H3)) & H4). split; [ | apply H4]. 
          rewrite H. rewrite !projVars_add. 
          destruct H1 as (win & H1 & F1 & F2 & _). 
          econstructor 3. 
          -- clear H1. rewrite !projVars_comp in H2. rewrite !Nat.min_l in H2 by lia.
             replace (start + S offset - start) with (S offset) in H2 by lia. 
             apply H2. 
          -- rewrite projVars_length; lia. 
          -- rewrite projVars_length; lia. 
          -- clear H2. apply H1. 
          -- clear H2. rewrite <- !projVars_add. 
             replace (S offset + (S l - S offset)) with (width + (S l - width)) by lia. 
             rewrite !projVars_add. 
             rewrite projVars_comp in F1, F2. rewrite !Nat.min_l in F1, F2 by lia. 
             rewrite Nat.add_0_r in F2; cbn in F1, F2.
             rewrite F1, F2. split; unfold prefix; eauto. 
    + (*the case where the remaining string is too short for a rewrite window to hold - validity holds vacuously *)
      clear IH. assert ( (S l) < width) as H3%Nat.ltb_lt by lia. cbn -[projVars]; setoid_rewrite H3.
      split; [eauto | ]. unfold satisfies; cbn [evalFormula]. setoid_rewrite explicitAssignment_length. 
      intros a; split; [intros _ | ]. 
      * split; [ | easy]. destruct H as (k & H). eapply valid_vacuous. 
        -- rewrite !projVars_length; [easy | rewrite explicitAssignment_length; lia | rewrite explicitAssignment_length; lia]. 
        -- rewrite projVars_length; [ easy | rewrite explicitAssignment_length; lia]. 
        -- rewrite projVars_length; [ | rewrite explicitAssignment_length; lia]. 
           (*here we need the assumption that l is a multiple of offset *)
           apply H. 
      * intros _; easy. 
  Qed.

  Definition encodeWindowsInLine start := encodeWindowsInLine' llength llength start (start + llength). 
  Lemma encodeWindowsInLine_encodesPredicate start : encodesPredicateAt start (llength + llength) (encodeWindowsInLine start) (fun m => valid offset width windows (projVars 0 llength m) (projVars llength llength m) /\ |m| = llength + llength). 
  Proof. 
    unfold encodeWindowsInLine.
    apply (@encodeWindowsInLine'_encodesPredicate start llength); [easy | apply A].
  Qed. 

  Fixpoint encodeWindowsInAllLines' (start : nat) (t : nat)  := 
    match t with 
    | 0 => Ftrue
    | S t => encodeWindowsInLine start ∧ encodeWindowsInAllLines' (start + llength) t
    end. 

  Definition encodeWindowsInAllLines := encodeWindowsInAllLines' 0 steps. 

  Lemma encodeWindowsInAllLines'_encodesPredicate start : encodesPredicateAt start ((S steps) * llength) (encodeWindowsInAllLines' start steps) 
    (fun m => (forall i, 0 <= i < steps -> valid offset width windows (projVars (i * llength) llength m) (projVars (S i * llength) llength m)) /\ |m| = (S steps) * llength). 
  Proof. 
    revert start. induction steps; cbn; intros. 
    - split; [ easy | ]. rewrite !Nat.add_0_r. 
      intros a; unfold satisfies; cbn; split; [ intros _; split; [intros; lia | rewrite explicitAssignment_length; lia]| easy]. 
    - specialize (encodeWindowsInLine_encodesPredicate start) as H1. 
      specialize (IHn (start + llength)). 
      specialize (encodesPredicate_and H1 IHn) as H. clear IHn H1. 
      encodesPredicateAt_comp_simp H. 
      replace (start + llength + S n * llength - start) with (llength + (llength + n * llength)) in H by lia. 
      replace (start + llength - start) with llength in H by lia. 
      eapply encodesPredicateAt_extensional; [ | apply H].
      clear H. intros m. cbn -[projVars]. 
      rewrite !projVars_comp. setoid_rewrite projVars_comp. cbn. rewrite !Nat.min_l by lia. 
      rewrite Nat.add_0_r. split. 
      + intros (H1 & H2). split; [ split |  easy]. 
        * specialize (H1 0). cbn in H1. rewrite Nat.add_0_r in H1. split; [apply H1; lia | now rewrite projVars_length].
        * split; [ | now rewrite projVars_length]. intros i H. 
          specialize (H1 (S i)). cbn in H1. rewrite Nat.add_comm. rewrite <- Nat.add_assoc. 
          rewrite !Nat.min_l by nia.
          setoid_rewrite Nat.add_comm at 3.
          apply H1. lia.
      + intros ((H1 & (H2 & _)) & H3). split; [ clear H3| apply H3]. intros i H. 
        destruct i. 
        * cbn. rewrite Nat.add_0_r. apply H1.
        * specialize (H2 i). 
          rewrite !Nat.min_l in H2 by nia.
          cbn. rewrite Nat.add_comm. rewrite Nat.add_assoc. now apply H2. 
  Qed.

  Corollary encodeWindowsInAllLines_encodesPredicate : encodesPredicateAt 0 ((S steps) * llength) encodeWindowsInAllLines 
    (fun m => (forall i, 0 <= i < steps -> valid offset width windows (projVars (i * llength) llength m) (projVars (S i * llength) llength m)) /\ |m| = (S steps) * llength). 
  Proof. 
    unfold encodeWindowsInAllLines. apply encodeWindowsInAllLines'_encodesPredicate. 
  Qed. 

  Fixpoint encodeSubstringInLine' (s : list bool) (stepindex l : nat) (start : nat) := 
    if l <? |s| then Ffalse
                  else match stepindex with 
                    | 0 => (match s with [] => Ftrue | _ => Ffalse end)
                    | S stepindex => encodeListAt start s ∨ encodeSubstringInLine' s stepindex (l - offset) (start + offset) 
                    end.

  Lemma encodeSubstringInLine'_stepindex_monotone s index1 index2 start : 
    index2 >= index1 -> encodeSubstringInLine' s index1 index1 start = encodeSubstringInLine' s index2 index1 start.
  Proof. 
  Admitted. 

  Lemma projVars_length_le start l m: |projVars start l m| <= |m|. 
  Proof. 
    unfold projVars. 
    rewrite firstn_length. rewrite skipn_length. lia. 
  Qed. 

  Lemma projVars_length_le2 start l m : |projVars start l m| <= l.
  Proof. 
    unfold projVars. rewrite firstn_length, skipn_length. lia. 
  Qed. 

  Lemma projVars_in_ge start l m : start <= |m| -> projVars start (|l|) m = l -> |m| >= start + |l|. 
  Proof. 
    intros H0 H. unfold projVars in H. rewrite <- H, firstn_length, skipn_length. lia.
  Qed. 

  Lemma encodeSubstringInLine'_encodesPredicate s start l : l <= llength -> (exists k, l = k * offset) -> encodesPredicateAt start l (encodeSubstringInLine' s l l start) (fun m => (exists k, k * offset <= l /\ projVars (k * offset) (|s|) m = s) /\ |m| = l). 
  Proof. 
    (*need strong induction *)
    destruct A as (A1 & A4 & A2 & A5 & A7 & A3). 
    revert start.  
    apply complete_induction with (x := l). clear l. intros l IH. intros. 

    destruct l.
    - cbn -[projVars]. destruct s; cbn -[projVars]. 
      + (*trivially true *) split; [ easy | intros; unfold satisfies; cbn; split; intros _; eauto].
        split; [exists 0; split; [lia | easy] | easy ].
      + (*trivially false *)
        split; [ easy | ]. intros a; split.
        * unfold satisfies; cbn; congruence. 
        * intros ((k & H1 & H2) & _). destruct k; [clear H1 | nia].
          cbn in H2. congruence. 
    - destruct (le_lt_dec (|s|) (S l)). 
      + assert (~ (S l) < (|s|)) as H3%Nat.ltb_nlt by lia. cbn -[projVars]; setoid_rewrite H3. 
        destruct offset as [ | offset]; [ lia | ].
        (* we use the IH for l - offset *)
 
        assert (S l - S offset < S l) as H1 by lia. apply IH with (start := start + S offset) in H1. 2: nia. 
        2: { destruct H0 as (k & H0). destruct k; [ lia | ]. exists k. lia. }
        clear H IH. 
        specialize (encodeListAt_encodesPredicate start s) as H2.
        specialize (encodesPredicate_or H2 H1) as H. clear H1 H2 H3.
        encodesPredicateAt_comp_simp H.
        destruct H0 as (k & H0).
        assert (k > 0) by nia. (*a hint for nia - without it, the following replace will not work *)
        replace (start + S offset + (S l - S offset) - start) with (S l) in H by nia.
        replace (start + S offset - start) with (S offset) in H by lia.

        rewrite encodeSubstringInLine'_stepindex_monotone with (index2 := l) in H; [ | lia].
        eapply encodesPredicateAt_extensional; [ | apply H]. clear H.
        intros. cbn. split.
        * intros ((k0 & H2 & H3) & H4). split; [ | easy]. 
          destruct k0; [ now left | right]. 
          split; [ | rewrite projVars_length; [ easy | nia] ]. 
          exists (k0). split; [ easy | ]. 
          rewrite projVars_comp. 
          cbn [Nat.mul] in H3.  
          enough (|s| <= l - offset - k0 * S offset).
          { rewrite Nat.min_l by lia. rewrite Nat.add_comm. apply H3. }
          apply projVars_in_ge in H3; nia.
        * intros (H & H2). split; [ | apply H2]. 
          destruct H as [H | (H & _)]; [ exists 0; cbn; easy | ]. 
          destruct H as (k0 & H & H'). 
          exists (S k0). split; [ nia | ].
          rewrite projVars_comp in H'. 

          enough (|s| <= l - offset - k0 * S offset).
          { rewrite Nat.min_l in H' by lia. cbn [Nat.mul]. rewrite <- Nat.add_comm. apply H'. }
          apply list_eq_length in H'. 
          match type of H' with (|projVars ?a ?b ?c| = _) => specialize (projVars_length_le2 a b c) as H3 end.
          lia. 
    + (*the case where the remaining string is too short in order to place the substring constraint *)
      clear IH. assert ( (S l) < (|s|)) as H3%Nat.ltb_lt by lia. cbn -[projVars]; setoid_rewrite H3.
      split; [eauto | ]. unfold satisfies; cbn [negb evalFormula]. setoid_rewrite explicitAssignment_length. 
      intros a; split; [congruence | ]. 
      intros ((k & H1 & H2) & _). 
      apply list_eq_length in H2. specialize (projVars_length_le (k * offset) (|s|) (explicitAssignment a start (S l))) as H4.
      rewrite explicitAssignment_length in H4. lia. 
  Qed.

  (*TODO: consistent argument order over all functions *)
  Definition encodeSubstringInLine s start l := encodeSubstringInLine' s l l start. 
  Definition encodeFinalConstraint (start : nat) := listOr (map (fun s => encodeSubstringInLine s start llength) final). 

  Lemma encodesPredicate_listOr (X : Type) (l : list X) (encode : X -> nat -> nat -> formula) (p : X -> list bool -> Prop) start len : 
    (forall x, x el l -> encodesPredicateAt start len (encode x start len) (p x)) 
   -> encodesPredicateAt start len (listOr (map (fun x => encode x start len) l)) (fun m => (exists x, x el l /\ p x m) /\ |m| = len). 
  Proof. 
    intros H. induction l. 
    - cbn. split; [easy | ]. unfold satisfies; cbn. intros a; split; [ congruence | intros ((_ & [] & _) & _)]. 
    - specialize (IHl (fun x Hel => H x (or_intror Hel))). cbn. 
      specialize (H a (or_introl eq_refl)). 
      specialize (encodesPredicate_or H IHl) as H1. clear IHl H. 
      encodesPredicateAt_comp_simp H1. 
      replace (start + len - start) with len in H1 by lia. 

      eapply encodesPredicateAt_extensional; [ clear H1| apply H1].
      intros; split.
      + intros ((x & [-> | H] & H1) & H2); (split; [ | easy]). 
        * left; now rewrite projVars_all.
        * right. rewrite projVars_length, projVars_all; easy. 
      + intros ([H | ((x & H & H') & H1)] & H2); (split; [ | easy]).
        * exists a. now rewrite projVars_all in H.
        * exists x. rewrite projVars_length in H1; [ | easy]. rewrite projVars_all in H'; easy.
  Qed. 

  Lemma encodeFinalConstraint_encodesPredicate start : encodesPredicateAt start llength (encodeFinalConstraint start) (fun m => satFinal offset llength final m /\ |m| = llength).
  Proof. 
    unfold encodeFinalConstraint. 
    eapply encodesPredicateAt_extensional; [ | apply encodesPredicate_listOr]. 
    2: { intros. apply encodeSubstringInLine'_encodesPredicate; [easy | apply A]. }
    intros. split. 
    - intros ((subs & k & H1 & H2 & H3) & H4). split; [ | easy].
      exists subs. split; [ apply H1 | split; [ | apply H4]]. 
      exists k. split; [ easy | ]. 
      destruct H3 as (b & H3). unfold projVars. rewrite H3. 
      rewrite firstn_app, firstn_all, Nat.sub_diag; cbn. now rewrite app_nil_r. 
    - intros ((subs & H1 & (k & H2 & H3) & H4) & _). split; [ | apply H4].
      exists subs, k. split; [apply H1 | split; [ apply H2 | ]].
      unfold prefix. unfold projVars in H3. 
      setoid_rewrite <- firstn_skipn with (l := skipn (k * offset) m) (n:= |subs|).
      setoid_rewrite H3. eauto.
  Qed. 

  Definition encodeTableau := encodeListAt 0 init ∧ encodeWindowsInAllLines ∧ encodeFinalConstraint (steps * llength).
  Lemma encodeTableau_encodesPredicate : 
    encodesPredicateAt 0 (S steps * llength) encodeTableau 
    (fun m => projVars 0 llength m = init 
      /\ (forall i, 0 <= i < steps -> valid offset width windows (projVars (i * llength) llength m) (projVars (S i * llength) llength m)) 
      /\ satFinal offset llength final (projVars (steps * llength) llength m)
      /\ |m| = (S steps * llength)). 
  Proof. 
    specialize (encodesPredicate_and (encodeListAt_encodesPredicate 0 init) encodeWindowsInAllLines_encodesPredicate) as H. 
    encodesPredicateAt_comp_simp H.  
    specialize (encodesPredicate_and H (encodeFinalConstraint_encodesPredicate (steps * llength))) as H1.
    clear H. 
    encodesPredicateAt_comp_simp H1. 
    unfold encodeTableau. 
    replace (llength + steps * llength - 0 - 0) with (S steps * llength) in H1 by lia.

    eapply encodesPredicateAt_extensional; [ clear H1| apply H1].
    intros m; cbn. rewrite !projVars_comp. setoid_rewrite projVars_comp.
    rewrite !Nat.min_l by nia. cbn. 
    setoid_rewrite Nat.add_0_r. setoid_rewrite Nat.sub_0_r. 
    split. 
    - intros (H1 & H2 & H3 & H4). 
      repeat split; try (rewrite projVars_length; nia); try nia; [easy | | easy].
      intros. rewrite !Nat.min_l by nia. now apply H2.
    - rewrite !and_assoc. intros (H1 & H2 & (_ & _ & H3 & _ & H4)); split; [easy |split;[ | easy]]. 
      intros. specialize (H2 i H). rewrite !Nat.min_l in H2 by nia. apply H2.
  Qed. 

  Lemma expAssgn_to_assgn s b : 
    {a & forall x, x el a <-> x >= s /\ nth_error b (x - s) = Some true}.
  Proof. 
    revert s. 
    induction b; cbn; intros. 
    - exists []. intros x. destruct (x-s); cbn; easy. 
    - destruct (IHb (S s)) as (assgn & IH). destruct a. 
      + exists (s :: assgn). intros x. split.
        * intros [-> | H]; [ rewrite Nat.sub_diag; easy | ]. 
          apply IH in H as (H1 & H2). split; [ lia | ]. 
          now eapply nth_error_step.
        * intros (H1 & H2). apply le_lt_eq_dec in H1 as [H1 | ->].
          -- right. apply IH. split; [ lia | ]. eapply nth_error_step, H2. lia. 
          -- now left. 
      + exists assgn. intros x. split.
        * intros (H1 & H2)%IH. split; [ lia | rewrite <- nth_error_step; easy]. 
        * intros (H1 & H2). apply le_lt_eq_dec in H1 as [H1 | ->]. 
          -- apply IH. split; [ lia | ]. apply nth_error_step in H2; easy.  
          -- rewrite Nat.sub_diag in H2. cbn in H2. congruence. 
  Qed. 

  Lemma expAssgn_to_assgn_inv a s b : (forall x, x el a <-> x >= s /\ nth_error b (x -s) = Some true) 
    -> explicitAssignment a s (|b|) = b. 
  Proof. 
    revert s. induction b; cbn; intros; [ easy | ].
    destruct list_in_decb eqn:H1. 
    - apply list_in_decb_iff in H1; [ | intros; now rewrite Nat.eqb_eq]. 
  Admitted. 

  Lemma relpower_valid_to_assignment n x y: 
    relpower (valid offset width windows) n x y -> |x| = llength 
    -> exists m, |m| = (S n * llength) /\ projVars 0 llength m = x /\ projVars (n * llength) llength m = y 
      /\ (forall i, 0 <= i < n -> valid offset width windows (projVars (i * llength) llength m) (projVars (S i * llength) llength m)). 
  Proof. 
    induction 1. 
    - cbn. exists a. rewrite projVars_all; [ | lia]. easy.
    - intros. specialize (valid_length_inv H) as H2. rewrite H1 in H2; symmetry in H2. 
      apply IHrelpower in H2 as (m & H2 & H3 & H4 & H5). clear IHrelpower. 
      exists (a ++ m). repeat split. 
      + rewrite app_length. lia. 
      + rewrite projVars_app1; easy. 
      + cbn. rewrite projVars_app3; easy.
      + intros i H6. destruct i. 
        * cbn. rewrite Nat.add_0_r. setoid_rewrite projVars_app2 at 2; [ | easy]. 
          rewrite !projVars_app1; [ | easy]. rewrite H3. apply H.
        * assert (0 <= i < n) as H7 by lia. apply H5 in H7; clear H5 H6. 
          cbn. rewrite !projVars_app3; [ | easy | easy].  apply H7.
  Qed. 
  
  Lemma reduction_wf : FSAT encodeTableau <-> exists sf, relpower (valid offset width windows) steps init sf /\ satFinal offset llength final sf. 
  Proof with (try (solve [rewrite explicitAssignment_length; cbn; nia | cbn; lia])). 
    specialize (encodeTableau_encodesPredicate) as (H1 & H2). split; intros. 
    - destruct H as (a & H). apply H2 in H as (H3 & H4 & H5). clear H2. rewrite Nat.add_0_r in *. 
      exists (projVars (steps * llength) llength (explicitAssignment a 0 (S steps * llength))). 
      split; [ | apply H5]. rewrite <- H3. clear H1 H3 H5. 

      cbn. rewrite projVars_length... rewrite explicitAssignment_app at 1... rewrite projVars_app1...
      rewrite Nat.add_comm. rewrite explicitAssignment_app, projVars_app2, projVars_all... 

      apply relpower_relpowerRev. induction steps. 
      + cbn. constructor. 
      + econstructor. 
        * apply IHn. intros. specialize (H4 i). clear IHn. 
          replace (S (S n) * llength) with (i * llength + (llength + (S n - i) * llength)) in H4 at 1 by nia. 
          replace (S (S n) * llength) with (S i * llength + (llength + (n - i) * llength)) in H4 by nia. 
          rewrite explicitAssignment_app, projVars_app2 in H4...
          rewrite explicitAssignment_app, projVars_app1 in H4...
          rewrite explicitAssignment_app, projVars_app2 in H4...
          rewrite explicitAssignment_app, projVars_app1 in H4...
          
          replace (S n * llength) with (i * llength + (llength + (n - i) * llength)) at 1 by nia. 
          replace (S n * llength) with (S i * llength + (llength + (n - S i) * llength)) by nia. 
          rewrite explicitAssignment_app, projVars_app2...
          rewrite explicitAssignment_app, projVars_app1...
          rewrite explicitAssignment_app, projVars_app2...
          rewrite explicitAssignment_app, projVars_app1...
          now apply H4. 
        * specialize (H4 n). clear IHn. 
          cbn in H4. rewrite Nat.add_comm in H4. setoid_rewrite Nat.add_comm in H4 at 2. setoid_rewrite <- Nat.add_assoc in H4 at 1.
          rewrite explicitAssignment_app, projVars_app2 in H4... cbn in H4. 
          rewrite explicitAssignment_app, projVars_app1 in H4... 
          rewrite explicitAssignment_app, projVars_app2, projVars_all in H4... cbn in H4. now apply H4. 
    - destruct H as (sf & H3 & H4). unfold encodeTableau in *. 
      specialize (relpower_valid_to_assignment H3 eq_refl) as (expAssgn & H5 & H6 & H7 & H8). 
      destruct (expAssgn_to_assgn 0 expAssgn) as (a & H9).
      exists a. apply H2. clear H2. 
      apply expAssgn_to_assgn_inv in H9. rewrite H5 in H9. rewrite H9. easy.
  Qed. 


End fixInstance.


