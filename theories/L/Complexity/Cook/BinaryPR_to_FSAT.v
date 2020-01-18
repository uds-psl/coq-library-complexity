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

  (*generate the list of values assigned to the variables in range [lower, upper) *)
  Fixpoint explicitAssignment a lower upper := 
    match upper with 0 => [] 
        | S upper => if upper <? lower then [] 
              else explicitAssignment a lower upper ++ [list_in_decb Nat.eqb a upper]
        end. 

  Lemma explicitAssignment_length a lower upper : |explicitAssignment a lower upper| = upper - lower. 
  Proof. 
    revert lower. induction upper; intros. 
    - cbn. destruct lower; now cbn. 
    - destruct lower. 
      + rewrite app_length, IHupper. cbn. lia. 
      + cbn. 
        destruct Nat.leb eqn:H1.
        * apply Nat.leb_le in H1. cbn. lia. 
        * rewrite app_length. rewrite IHupper. cbn. apply Nat.leb_nle in H1. lia. 
  Qed. 

  Lemma explicitAssignment_nth a lower upper k : 
     k < upper - lower -> nth_error (explicitAssignment a lower upper) k = Some (evalVar a (lower + k)). 
  Proof. 
    intros. induction upper. 
    - lia. 
    - unfold explicitAssignment. assert (not (upper < lower)) by (intros; lia). 
      rewrite (proj2 (Nat.ltb_nlt _ _) H0 ). 
      fold explicitAssignment. 
      destruct (le_lt_dec (upper - lower) k).
      + assert (upper - lower = k) as <- by lia.
        rewrite nth_error_app2; rewrite explicitAssignment_length; [ rewrite Nat.sub_diag; cbn | lia].  
        unfold evalVar. enough (upper = lower + (upper - lower)) by easy. lia.  
      + rewrite nth_error_app1; [ | rewrite explicitAssignment_length; easy ]. now apply IHupper. 
  Qed. 

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
    varsInRange start (l + start) f /\ forall a, satisfies a f <-> p (explicitAssignment a start (l + start)). 

  Definition projVars start len (l : list bool) := firstn len (skipn start l). 

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

  Lemma projVars_combined1 s1 s2 l1 l2 a: explicitAssignment a s1 (l1 + s1) = projVars (s1 - combinedStart s1 s2) l1 (explicitAssignment a (combinedStart s1 s2) (combinedLength s1 s2 l1 l2 + combinedStart s1 s2)).
  Proof. 
    unfold projVars. 
    apply list_eq_nth_error. split. 
    - rewrite explicitAssignment_length. unfold combinedStart, combinedLength. rewrite firstn_length. 
      rewrite skipn_length. rewrite explicitAssignment_length. lia. 
    - intros. rewrite explicitAssignment_length, Nat.add_sub in H. unfold combinedStart, combinedLength. 
      rewrite Nat.sub_add; [ | lia]. 
      rewrite nth_error_firstn; [ | apply H].  
      rewrite nth_error_skipn. rewrite !explicitAssignment_nth; [easy | lia | lia]. 
  Qed. 

  Lemma projVars_combined2 s1 s2 l1 l2 a: explicitAssignment a s2 (l2 + s2) = projVars (s2 - combinedStart s1 s2) l2 (explicitAssignment a (combinedStart s1 s2) (combinedLength s1 s2 l1 l2 + combinedStart s1 s2)). 
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
      + apply encodeLiteral_correct in H. specialize (explicitAssignment_length a v (S v)) as H1. 
        replace (S v - v) with 1 in H1 by lia. assert (0 < S v - v) as H2 by lia. 
        specialize (@explicitAssignment_nth a v (S v) 0 H2) as H3. 
        destruct explicitAssignment as [ | s l]; cbn in H1; [ congruence | destruct l; [ | cbn in H1; congruence]]. 
        cbn in H3. now inv H3. 
      + apply encodeLiteral_correct.  assert (0 < S v - v) as H2 by lia.
        specialize (@explicitAssignment_nth a v (S v) 0 H2) as H1. 
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
      + intros _. destruct start; cbn; [easy | rewrite Nat.leb_refl; easy]. 
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

  (*encoding of windows *)
  Definition encodeWindowAt (startA startB : nat) (win : PRWin bool) := encodeListAt startA (prem win) ∧ encodeListAt startB (conc win). 
  Lemma encodeWindowAt_encodesPredicate start win : encodesPredicateAt start (llength + offset) (encodeWindowAt start (start + llength) win) (fun m => firstn offset m = prem win /\ skipn llength m = conc win). 
  Proof. 
  Admitted. 

  Definition encodeWindowsAt (startA startB : nat) := listOr (map (encodeWindowAt startA startB) windows). 

  Lemma encodeWindowsAt_encodesPredicate start : encodesPredicateAt start (llength + offset) (encodeWindowsAt start (start + llength)) (fun m => exists win, win el windows /\ firstn offset m = prem win /\ skipn llength m = conc win). 
  Proof. 
  Admitted. 

  (*we only need to place a window every offset fields, but subtracting offset isn't structurally recursive *)
  (*therefore we use a stepindex (initalise to the same value as l) *)
  Fixpoint encodeWindowsInLine' (stepindex l : nat) (startA startB : nat) := 
    if l <? width then Ftrue 
                  else match stepindex with 
                    | 0 => Ftrue
                    | S stepindex => encodeWindowsAt startA startB ∧ encodeWindowsInLine' stepindex (l - offset) (startA + offset) (startB + offset)
                    end.

  (*TODO: need the additional constraint that variables do not overlap *)
  (*Lemma encodeWindowsInLine'_correct (l : nat) (startA startB : nat) :*)
    (*l >= width -> *)
    (*forall a, satisfies a (encodeWindowsInLine' l startA startB) <-> valid offset width windows (explicitAssignment a startA (startA + l)) (explicitAssignment a startB (startB + l)). *)
  (*Proof. *)
  (*Admitted. *)
 
  Definition encodeWindowsInLine start := encodeWindowsInLine' llength llength start (start + llength). 
  Lemma encodeWindowsInLine_encodesPredicate start : encodesPredicateAt start (llength + llength) (encodeWindowsInLine start) (fun m => valid offset width windows (firstn llength m) (skipn llength m)). 
  Proof. 
  Admitted.

  Fixpoint encodeAllLines' (t : nat) (start : nat) := 
    match t with 
    | 0 => Ftrue
    | S t => encodeWindowsInLine start ∧ encodeAllLines' t (start + llength)
    end. 

  Definition encodeAllLines := encodeAllLines' steps 0. 

  Lemma encodeAllLines_encodesPred : encodesPredicateAt 0 (steps * llength) encodeAllLines (fun m => relpower (valid offset width windows) steps (firstn llength m) (skipn ((steps -1) * llength) m)). 
  Proof. 
  Admitted. 

  Fixpoint encodeSubstringInLine (s : list bool) (l : nat) (start : nat) := 
    if l <? |s| then Ffalse
                else match l with 
                  | 0 => Ffalse
                  | S l => encodeListAt start s ∨ encodeSubstringInLine s l (S start) 
                  end. 
  Definition encodeFinalConstraint (start : nat) := listOr (map (fun s => encodeSubstringInLine s llength start) final). 

  Lemma encodeFinalConstraint_encodesPredicate start : encodesPredicateAt start llength (encodeFinalConstraint start) (satFinal offset llength final).
  Proof. 
  Admitted. 

  Definition encodeTableau := encodeListAt 0 init ∧ encodeAllLines ∧ encodeFinalConstraint ((steps -1) * llength).
  Lemma encodeTableau_encodesPredicate : encodesPredicateAt 0 (steps * llength) encodeTableau (fun m => firstn llength m = init /\ relpower (valid offset width windows) steps init (skipn ((steps -1) * llength) m) /\ satFinal offset llength final (skipn ((steps -1) * llength) m)). 
  Proof. 
  Admitted. 

  Lemma reduction_wf : FSAT encodeTableau <-> exists sf, relpower (valid offset width windows) steps init sf /\ satFinal offset llength final sf. 
  Proof. 
  Admitted. 

End fixInstance.


