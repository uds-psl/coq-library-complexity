From PslBase Require Import Base. 
From Undecidability.L.Complexity.Cook Require Import Prelim FSAT BinaryPR.
From Undecidability.L.Complexity Require Import Tactics. 
From Undecidability.L.Datatypes Require Import LLists. 
Require Import Lia. 

(** *Reduction of BinaryPR to FSAT *)
(*High-level overview:
We lay out the BinaryPR computation in a tableau which has (steps + 1) lines, where steps is the number of steps of the BPR instance, 
and each line has a length which is equal to the length of the BPR strings.
Each cell of the tableau corresponds to one symbol of a BPR string and is encoded using a single Boolean variable in the FSAT instance.

The FSAT formula consists of three gadgets, encoding:
- the constraint on the initial string
- the validity of rewrites 
- the final constraints.

The constraint on the initial string is straightforward to encode: We just have a big AND over the positions of the string.

For the validity of rewrites, we have a AND consisting of a subformula for each of the rewrites.
Each rewrite in turn forces that the successor string evolves validly from the current string - we have an AND over the offsets of the string
at which rewrite windows have to hold. 
For each of the offsets, we then have a disjunction over all rewrite windows. 
That a rewrite window holds at a position is encoded similarly to the initial string.

For the final constraint, we have a disjunction over the final strings and a nested disjunction over all positions at which a string can be a substring.
*)

(*Require Import BinNat BinNums.*)
(*Local Open Scope N_scope. *)

(*SearchAbout "peano_rec".*)
(*Definition bfirstn (X : Type) (n : N) (l : list X) : list X.*)
(*Proof. *)
  (*revert n l. apply (N.peano_rect (fun _ => list X -> list X)). *)
  (*- intros _. exact []. *)
  (*- intros n rec l. destruct l. *)
    (*+ exact []. *)
    (*+ apply rec in l. exact (x :: l). *)
(*Defined. *)
(*Locate firstn_firstn. *)

(*Lemma bfirstn_nil (X : Type) n:*)
  (*@bfirstn X n [] = [].*)
(*Proof. *)
  (*revert n. apply N.peano_ind; intros; unfold bfirstn; [rewrite N.peano_rect_base | rewrite N.peano_rect_succ ]; easy. *)
(*Qed. *)

(*Definition peano_case (P : N -> Type) (f0 : P 0) (f : forall n, P (N.succ n)) (n : N) : P n := N.peano_rect P f0 (fun n _ => f n) n. *)
(*Lemma peano_case_base (P : N -> Type) (f0 : P 0) (f : forall n, P (N.succ n)) : peano_case f0 f 0 = f0.*)
(*Proof. *)
  (*unfold peano_case. apply N.peano_rect_base. *)
(*Qed. *)
(*Lemma peano_case_succ (P : N -> Type) (f0 : P 0) (f : forall n, P (N.succ n)) n : peano_case f0 f (N.succ n) = f n. *)
(*Proof. *)
  (*unfold peano_case. apply N.peano_rect_succ. *)
(*Qed. *)

(*Lemma firstn_firstn (X : Type):*)
    (*forall l:list X,*)
    (*forall i j : N,*)
    (*bfirstn i (bfirstn j l) = bfirstn (N.min i j) l.*)
  (*Proof. induction l as [|x xs Hl].*)
    (*- intros. now rewrite ?bfirstn_nil.*)
    (*- intros i. apply peano_case with (n := i).      *)
      (** intro. rewrite N.min_l by lia. now simpl.*)
      (** intros. apply peano_case with (n := j).*)
        (*+ rewrite N.min_r by lia. unfold bfirstn. rewrite N.peano_rect_succ, !N.peano_rect_base. now simpl.*)
        (*+ simpl. f_equal. apply Hl.*)
  (*Qed.*)

(*SearchAbout firstn.*)
(*Print firstn_firstn. *)

(*Compute (bfirstn 0 [1; 2; 3; 4; 5]). *)

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

  (*convenience functions for creating formulas *)
  Notation Ffalse := (¬Ftrue). 
  Fixpoint listOr (l : list formula) := match l with
    | [] => Ffalse 
    | a :: l => a ∨ listOr l 
    end. 

  Fixpoint listAnd (l : list formula) := match l with 
    | [] => Ftrue
    | a :: l => a ∧ listAnd l
    end.  

  (*generate the list of values assigned to the variables by a in range [lower, lower + len) *)
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

  Lemma explicitAssignment_app a l1 len1 len2: explicitAssignment a l1 (len1 + len2) = explicitAssignment a l1 len1 ++ explicitAssignment a (l1 + len1) len2. 
  Proof. 
    induction len2; cbn. 
    - now rewrite Nat.add_0_r, app_nil_r. 
    - rewrite Nat.add_succ_r. cbn. rewrite IHlen2, app_assoc. easy. 
  Qed. 

  (*from an explicit assignment, we can go back to an assignment *)
  (*s is the variable index at which the explicit assignment is starting *)
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
    intros. apply list_eq_nth_error. split; [ apply explicitAssignment_length | ].
    intros k H1. rewrite explicitAssignment_length in H1. 
    rewrite explicitAssignment_nth by apply H1. 
    unfold evalVar. destruct list_in_decb eqn:H2. 
    - apply list_in_decb_iff in H2; [ | intros; now rewrite Nat.eqb_eq ].
      apply H in H2 as (_ & H2). now replace (s + k - s) with k in H2 by lia.
    - apply list_in_decb_iff' in H2; [ | intros; now rewrite Nat.eqb_eq].
      (*we do a case analysis, thus we do not need XM *)
      destruct (nth_error b k) eqn:H3. 
      + destruct b0; [ | easy]. exfalso; apply H2. apply H. 
        replace (s + k - s) with k by lia. easy.
      + apply nth_error_none in H3. lia.
  Qed.

  (*we define what it means for a formula to encode a predicate *)
  Definition predicate := list bool -> Prop. 
  Implicit Type (p : predicate).
  Definition encodesPredicateAt (start : nat) (l : nat) f p:= forall a, satisfies a f <-> p (explicitAssignment a start l). 

  (*given an explicitAssignment, we can project out a range of variables, given by [start, start+len) *)
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

  Lemma projVars_comp l1 l2 len1 len2 m: projVars l1 len1 (projVars l2 len2 m) = projVars (l1 + l2) (min len1 (len2 - l1)) m. 
  Proof. 
    unfold projVars. intros. 
    rewrite skipn_firstn_skipn. rewrite firstn_firstn. reflexivity. 
  Qed. 

  Lemma projVars_add s l1 l2 m : projVars s (l1 + l2) m = projVars s l1 m ++ projVars (s + l1) l2 m. 
  Proof. 
    unfold projVars. rewrite firstn_add, skipn_skipn. now rewrite Nat.add_comm. 
  Qed.

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

  (*encodings of two predicates can be combined*)
  Definition combinedLength start1 start2 l1 l2 := max (start1 +l1) (start2 + l2) - min start1 start2. 
  Definition combinedStart start1 start2 := min start1 start2. 

  (*from the combined assignment for the combination of two formulas, we can restore an assignment for the first formula *)
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

  (*...and for the second *)
  Lemma projVars_combined2 s1 s2 l1 l2 a: explicitAssignment a s2 l2 = projVars (s2 - combinedStart s1 s2) l2 (explicitAssignment a (combinedStart s1 s2) (combinedLength s1 s2 l1 l2)). 
  Proof. 
    unfold combinedStart, combinedLength. rewrite Nat.min_comm. rewrite Nat.max_comm. apply projVars_combined1. 
  Qed. 

  (*two formulae can be combined via ∧ *)
  Lemma encodesPredicate_and start1 start2 l1 l2 f1 f2 p1 p2 : 
    encodesPredicateAt start1 l1 f1 p1 -> encodesPredicateAt start2 l2 f2 p2 
    -> encodesPredicateAt (combinedStart start1 start2) (combinedLength start1 start2 l1 l2) (f1 ∧ f2) (fun m => (p1 (projVars (start1 - combinedStart start1 start2) l1 m) /\ p2 (projVars (start2 - combinedStart start1 start2) l2 m))). 
  Proof. 
    intros G1 G2. 
    intros a. split; intros H. 
    + apply evalFormula_and_iff in H as (H1 & H2). 
      rewrite <- projVars_combined1, <- projVars_combined2. 
      unfold encodesPredicateAt in G1, G2. rewrite <- G1, <- G2. easy. 
    + rewrite <- projVars_combined1, <- projVars_combined2 in H. 
      unfold satisfies. apply evalFormula_and_iff. 
      split; [apply G1, H | apply G2, H]. 
  Qed. 

  (*...and with ∨*)
  Lemma encodesPredicate_or start1 start2 l1 l2 f1 f2 p1 p2 : 
    encodesPredicateAt start1 l1 f1 p1 -> encodesPredicateAt start2 l2 f2 p2 
    -> encodesPredicateAt (combinedStart start1 start2) (combinedLength start1 start2 l1 l2) (f1 ∨ f2) (fun m => (p1 (projVars (start1 - combinedStart start1 start2) l1 m) \/ p2 (projVars (start2 - combinedStart start1 start2) l2 m))).
  Proof. 
    intros G1 G2. 
    intros a. split; intros H. 
    + apply evalFormula_or_iff in H as [H | H]; 
      rewrite <- projVars_combined1, <- projVars_combined2;
      unfold encodesPredicateAt in G1, G2; rewrite <- G1, <- G2; easy. 
    + rewrite <- projVars_combined1, <- projVars_combined2 in H. 
      unfold satisfies. apply evalFormula_or_iff. 
      destruct H as [H | H]; [left; apply G1, H | right; apply G2, H].
  Qed. 

  (*encoding of single literals *)
  Definition encodeLiteral v (sign : bool) : formula := if sign then v else ¬ v. 

  Lemma encodeLiteral_correct v sign : forall a, satisfies a (encodeLiteral v sign) <-> evalVar a v = sign. 
  Proof. 
    intros. unfold satisfies, encodeLiteral. destruct sign; cbn; [ tauto |simp_bool; tauto ]. 
  Qed. 

  Lemma encodeLiteral_encodesPredicate v sign : encodesPredicateAt v 1 (encodeLiteral v sign) (fun l => l = [sign]). 
  Proof. 
    intros. split; intros. 
    + apply encodeLiteral_correct in H. specialize (explicitAssignment_length a v 1) as H1. 
      assert (0 < 1) as H2 by lia. 
      specialize (@explicitAssignment_nth a v 1 0 H2) as H3. 
      destruct explicitAssignment as [ | s l]; cbn in H1; [ congruence | destruct l; [ | cbn in H1; congruence]]. 
      cbn in H3. now inv H3. 
    + apply encodeLiteral_correct. assert (0 < 1) as H2 by lia.
      specialize (@explicitAssignment_nth a v 1 0 H2) as H1. 
      rewrite H in H1; cbn in H1. now inv H1. 
  Qed. 

  (*for predicates which are equivalent, encoding is equivalent *)
  Lemma encodesPredicateAt_extensional s l f p1 p2 : (forall m, |m| = l -> p1 m <-> p2 m) -> encodesPredicateAt s l f p1 <-> encodesPredicateAt s l f p2. 
  Proof. 
    intros. unfold encodesPredicateAt. split; intros; specialize (H (explicitAssignment a s l) (explicitAssignment_length _ _ _)); [now rewrite <- H | now rewrite H]. 
  Qed. 

  (*a procedure that tries to simplify parts of the terms introduced by the combination lemmas for ∧ and ∨ *)
  Ltac encodesPredicateAt_comp_simp H := 
    unfold combinedStart, combinedLength in H;
    try (rewrite Nat.min_l in H by nia); try (rewrite Nat.min_r in H by nia);
    try (rewrite Nat.max_l in H by nia); try (rewrite Nat.max_r in H by nia);
    try rewrite !Nat.sub_diag in H.
  
  (*encoding of lists *)
  Fixpoint encodeListAt (startA : nat) (l : list bool) :=
    match l with 
    | [] => Ftrue
    | x :: l => (encodeLiteral startA x) ∧ (encodeListAt (1 + startA) l)
    end. 

  Lemma encodeListAt_encodesPredicate start l : encodesPredicateAt start (|l|) (encodeListAt start l) (fun m => m = l).
  Proof. 
    revert start. induction l; intros. 
    - cbn. split; [eauto | ]. unfold satisfies. intros; easy. 
    - cbn. specialize (@encodesPredicate_and start (S start) 1 (|l|) (encodeLiteral start a) (encodeListAt (S start) l) _ _ (encodeLiteral_encodesPredicate start a) (IHl (S start))) as H1.
      encodesPredicateAt_comp_simp H1. 
      replace (S start - start) with 1 in H1 by lia. 
      replace (S start + (|l|) - start) with (S (|l|)) in H1 by lia.
      eapply encodesPredicateAt_extensional; [ | apply H1]. 
      intros m H0. unfold projVars. 
      destruct m; cbn; [split; intros; easy | ]. 
      split. 
      + intros H. inv H. now rewrite firstn_all.
      + intros (H2 & H3). inv H2. f_equal. apply Nat.succ_inj in H0. now apply firstn_all_inv. 
  Qed. 

  (*encoding of windows *)
  (*startA is the position at which the premise is placed, startB the position at which the conclusion is placed *)
  Definition encodeWindowAt (startA startB : nat) (win : PRWin bool) := encodeListAt startA (prem win) ∧ encodeListAt startB (conc win). 

  Lemma encodeWindowAt_encodesPredicate start len win : 
    win el windows -> encodesPredicateAt start (len + width) (encodeWindowAt start (start + len) win) (fun m => projVars 0 width m = prem win /\ projVars len width m = conc win). 
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

  (*encoding of the disjunction of all windows of the BinaryPR instance  *)
  Definition encodeWindowsAt (startA startB : nat) := listOr (map (encodeWindowAt startA startB) windows). 

  Lemma encodeWindowsAt_encodesPredicate len start : len >= width -> encodesPredicateAt start (len + width) (encodeWindowsAt start (start + len)) (fun m => exists win, win el windows /\ projVars 0 width m = prem win /\ projVars len width m = conc win). 
  Proof. 
    intros F0.
    specialize (encodeWindowAt_encodesPredicate) as H1. 
    unfold encodeWindowsAt. 
    induction windows. 
    - cbn. split. 
      + unfold satisfies. cbn. congruence. 
      + intros (win & [] & _). 
    - cbn. match type of IHl with ?a -> _ => assert a as H by (intros; apply H1; eauto); apply IHl in H; clear IHl end. 
      specialize (H1 start len a (or_introl eq_refl)). 
      specialize (encodesPredicate_or H1 H) as H2. clear H1 H. 
      cbn in H2. 
      destruct A as (_ & _ & (k & A1 & A2) & _).
      encodesPredicateAt_comp_simp H2. 
      replace (start + (len + width) - start) with (len + width) in H2 by lia.
      eapply encodesPredicateAt_extensional; [ | apply H2]. 
      intros; cbn. 
      rewrite !projVars_comp. cbn. rewrite !Nat.min_l by lia. rewrite Nat.add_0_r. 
      split; intros. 
      + destruct H0 as (win & [<- | H0] & F1 & F2); [now left | right; eauto].
      + destruct H0 as [(F1 & F2) | (win & H0 & F1 & F2)]; eauto 7. 
  Qed. 

  (*encoding of all windows of one line of the tableau *)
  (*we only need to place a window every offset fields, but subtracting offset isn't structurally recursive *)
  (*therefore we use a stepindex (initalise to the same value as l) *)
  Fixpoint encodeWindowsInLine' (stepindex l : nat) (startA startB : nat) := 
    if l <? width then Ftrue 
                  else match stepindex with 
                    | 0 => Ftrue
                    | S stepindex => encodeWindowsAt startA startB ∧ encodeWindowsInLine' stepindex (l - offset) (startA + offset) (startB + offset)
                    end.

  Lemma encodeWindowsInLine'_stepindex_monotone' index startA startB : forall n, n <= index -> encodeWindowsInLine' index n startA startB = encodeWindowsInLine' (S index) n startA startB. 
  Proof. 
    destruct A as (A1 & A2 & _).
    revert startA startB.
    induction index; intros. 
    - unfold encodeWindowsInLine'. assert (n = 0) as -> by lia. cbn; destruct width; [ lia | easy ].
    - unfold encodeWindowsInLine'. destruct (Nat.ltb n width); [ easy | ]. fold encodeWindowsInLine'. 
      erewrite IHindex by lia. easy. 
  Qed. 

  Lemma encodeWindowsInLine'_stepindex_monotone index index' startA startB : index' >= index -> encodeWindowsInLine' index index startA startB = encodeWindowsInLine' index' index startA startB. 
  Proof. 
    intros. revert index H.
    induction index'; intros. 
    - assert (index = 0) as -> by lia. easy.
    - destruct (nat_eq_dec (S index') index). 
      + now rewrite e.
      + assert (index' >= index) as H1 by lia. rewrite <- encodeWindowsInLine'_stepindex_monotone' by lia. now apply IHindex'.
  Qed.

  Lemma encodeWindowsInLine'_encodesPredicate start l : l <= llength -> (exists k, l = k * offset) -> encodesPredicateAt start (l + llength) (encodeWindowsInLine' l l start (start + llength)) (fun m => valid offset width windows (projVars 0 l m) (projVars llength l m)). 
  Proof. 
    intros A0.
    (*need strong induction *)
    destruct A as (A1 & A4 & A2 & A5 & A7 & A3). 
    revert start A0.  
    apply complete_induction with (x := l). clear l. intros l IH. intros. 

    (*case analysis on the stepindex *)
    destruct l.
    - (*we use that width > 0 *)
      unfold encodeWindowsInLine'. rewrite (proj2 (Nat.ltb_lt _ _) A1). 
      intros a. split; [ intros; constructor | intros _; unfold satisfies; eauto].  
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
        replace (start + S offset + (S l - S offset + llength) - start) with (S (l + llength)) in H2. 
        2: { destruct A2 as (? & A2 & A6). nia. }
        
        rewrite encodeWindowsInLine'_stepindex_monotone with (index' := l) in H2; [ | lia].
        eapply encodesPredicateAt_extensional; [ | apply H2].

        clear H2 H3. 
        intros. 
        destruct A2 as (k & A2 & A2').
        assert (S l = S offset + (S l - S offset)) as H0 by nia.  
        (*we now show the two directions of the equivalence, which is a bit technical*)
        split; intros. 
        * rewrite H0 in H1. clear H0. 
          rewrite !projVars_add in H1. inv H1.
          (*the first two cases are contradictory *)
          2 : { exfalso. apply list_eq_length in H0. rewrite !app_length in H0. rewrite !projVars_length in H0; [ | easy | easy]. nia. }
          1: { exfalso. apply list_eq_length in H3. rewrite !app_length in H3. rewrite projVars_length in H3; [ | cbn; nia]. cbn in H3. lia. } 

          apply app_eq_length in H2 as (-> & ->); [ | rewrite projVars_length; [easy | nia] ].
          apply app_eq_length in H0 as (-> & ->); [ | rewrite projVars_length; [easy | nia]]. 
          split.
          -- exists win. rewrite !projVars_comp; cbn. rewrite !Nat.min_l by lia. 
             rewrite !Nat.add_0_r.
             clear H3 H4 H5. rewrite <- !projVars_add in H7. 
             replace (S offset + (l - offset)) with (width + (S l - width)) in H7 by nia. 
             rewrite !projVars_add in H7.
             split; [ easy | split ]; apply A7 in H6 as (H6 & H6'). 
             ++ destruct H7 as ((b & H7) & _). eapply app_eq_length in H7; [ easy| rewrite projVars_length; easy ]. 
             ++ destruct H7 as (_ & (b & H7)). eapply app_eq_length in H7; [ easy | rewrite projVars_length; easy].
          -- clear H7 H6. 
             rewrite !projVars_comp. replace (start + S offset - start) with (S offset) by lia. rewrite !Nat.min_l by lia. 
             apply H3. 
        * (*other direction of the equivalence *)
          destruct H1 as (H1 & H2).  
          rewrite H0, !projVars_add. 
          destruct H1 as (win & H1 & F1 & F2). 
          econstructor 3. 
          -- rewrite !projVars_comp in H2. rewrite !Nat.min_l in H2 by lia.
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
      intros a; split; [intros _ | ]. 
      * destruct H as (k & H). eapply valid_vacuous. 
        -- rewrite !projVars_length; [easy | rewrite explicitAssignment_length; lia | rewrite explicitAssignment_length; lia]. 
        -- rewrite projVars_length; [ easy | rewrite explicitAssignment_length; lia]. 
        -- rewrite projVars_length; [ | rewrite explicitAssignment_length; lia]. 
           (*here we need the assumption that l is a multiple of offset *)
           apply H. 
      * intros _; easy. 
  Qed.

  (*the above construction specialized to the setting we need: the conclusion starts exactly one line after the premise *)
  Definition encodeWindowsInLine start := encodeWindowsInLine' llength llength start (start + llength). 
  Lemma encodeWindowsInLine_encodesPredicate start : encodesPredicateAt start (llength + llength) (encodeWindowsInLine start) (fun m => valid offset width windows (projVars 0 llength m) (projVars llength llength m)). 
  Proof. 
    unfold encodeWindowsInLine.
    apply (@encodeWindowsInLine'_encodesPredicate start llength); [easy | apply A].
  Qed. 

  (*encoding of windows in all lines of the tableau *)
  Fixpoint encodeWindowsInAllLines' (start : nat) (t : nat)  := 
    match t with 
    | 0 => Ftrue
    | S t => encodeWindowsInLine start ∧ encodeWindowsInAllLines' (start + llength) t
    end. 

  Definition encodeWindowsInAllLines := encodeWindowsInAllLines' 0 steps. 

  Lemma encodeWindowsInAllLines'_encodesPredicate start : encodesPredicateAt start ((S steps) * llength) (encodeWindowsInAllLines' start steps) 
    (fun m => (forall i, 0 <= i < steps -> valid offset width windows (projVars (i * llength) llength m) (projVars (S i * llength) llength m))). 
  Proof. 
    revert start. induction steps; cbn; intros. 
    - rewrite !Nat.add_0_r. 
      intros a; unfold satisfies; cbn; split; [ intros _; intros; lia | easy]. 
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
      + intros H1. split.
        * specialize (H1 0). cbn in H1. rewrite Nat.add_0_r in H1. apply H1; lia.
        * intros i H2. 
          specialize (H1 (S i)). cbn in H1. rewrite Nat.add_comm. rewrite <- Nat.add_assoc. 
          rewrite !Nat.min_l by nia.  setoid_rewrite Nat.add_comm at 3.
          apply H1. lia.
      + intros (H1 & H2). intros i H3. destruct i. 
        * cbn. rewrite Nat.add_0_r. apply H1.
        * specialize (H2 i). 
          rewrite !Nat.min_l in H2 by nia.
          cbn. rewrite Nat.add_comm. rewrite Nat.add_assoc. now apply H2. 
  Qed.

  (*again a version specialised to our needs *)
  Corollary encodeWindowsInAllLines_encodesPredicate : encodesPredicateAt 0 ((S steps) * llength) encodeWindowsInAllLines 
    (fun m => (forall i, 0 <= i < steps -> valid offset width windows (projVars (i * llength) llength m) (projVars (S i * llength) llength m))). 
  Proof. 
    unfold encodeWindowsInAllLines. apply encodeWindowsInAllLines'_encodesPredicate. 
  Qed. 

  (*encode the substring constraint for a single string s *)
  (*should only be called for s satisfying |s| > 0; for s = nil, the breaking condition does not work as intended*)
  (*in principle, this is not a problem as the resulting formula is still equivalent to the desired formula, but this breaks monotonicity*)
  Fixpoint encodeSubstringInLine' (s : list bool) (stepindex l : nat) (start : nat) := 
    if l <? |s| then Ffalse
                  else match stepindex with 
                    | 0 => (match s with [] => Ftrue | _ => Ffalse end)
                    | S stepindex => encodeListAt start s ∨ encodeSubstringInLine' s stepindex (l - offset) (start + offset) 
                    end.

  (*the requirement |s| > 0 is needed for monotonicity *)
  Lemma encodeSubstringInLine'_stepindex_monotone' s index start : forall n, |s| > 0 -> n <= index -> encodeSubstringInLine' s index n start = encodeSubstringInLine' s (S index) n start. 
  Proof. 
    destruct A as (A1 & A2 & _).
    revert start.
    induction index; intros. 
    - unfold encodeSubstringInLine'. assert (n = 0) as -> by lia. cbn; destruct s; [ cbn in *; lia | easy ]. 
    - unfold encodeSubstringInLine'. destruct (Nat.ltb n (|s|)); [ easy | ]. fold encodeSubstringInLine'. 
      erewrite IHindex by lia. easy. 
  Qed. 

  Lemma encodeSubstringInLine'_stepindex_monotone s index1 index2 start : 
    |s| > 0 -> index2 >= index1 -> encodeSubstringInLine' s index1 index1 start = encodeSubstringInLine' s index2 index1 start.
  Proof. 
    intros. revert index1 H0. 
    induction index2; intros.
    - assert (index1 = 0) as -> by lia. easy.
    - destruct (nat_eq_dec (S index2) index1). 
      + now rewrite e.
      + assert (index2 >= index1) as H1 by lia. rewrite <- encodeSubstringInLine'_stepindex_monotone' by lia. now apply IHindex2.
  Qed. 

  Lemma encodeSubstringInLine'_encodesPredicate s start l : |s| > 0 -> l <= llength 
    -> (exists k, l = k * offset) -> encodesPredicateAt start l (encodeSubstringInLine' s l l start) (fun m => (exists k, k * offset <= l /\ projVars (k * offset) (|s|) m = s)). 
  Proof. 
    intros F.
    (*need strong induction *)
    destruct A as (A1 & A4 & A2 & A5 & A7 & A3). 
    revert start.  
    apply complete_induction with (x := l). clear l. intros l IH. intros. 

    destruct l.
    - cbn -[projVars]. destruct s; cbn -[projVars]. 
      + (*trivially true because of our requirement that |s| > 0*) cbn in F; easy. 
      + (*trivially false *)
        intros a; split.
        * unfold satisfies; cbn; congruence. 
        * intros (k & H1 & H2). destruct k; [clear H1 | nia]. cbn in H2. congruence. 
    - destruct (le_lt_dec (|s|) (S l)). 
      + (*in this case, we can apply the IH*)
        assert (~ (S l) < (|s|)) as H3%Nat.ltb_nlt by lia. cbn -[projVars]; setoid_rewrite H3. 
        destruct offset as [ | offset]; [ lia | ].
        (* we use the IH for l - offset *)
 
        assert (S l - S offset < S l) as H1 by lia. apply IH with (start := start + S offset) in H1; [ | nia | ]. 
        2: { destruct H0 as (k & H0). destruct k; [ lia | ]. exists k. lia. }
        clear H IH. 
        specialize (encodeListAt_encodesPredicate start s) as H2.
        specialize (encodesPredicate_or H2 H1) as H. clear H1 H2 H3.

        encodesPredicateAt_comp_simp H.
        destruct H0 as (k & H0).
        assert (k > 0) by nia. (*a hint for nia - without it, the following replace will not work *)
        replace (start + S offset + (S l - S offset) - start) with (S l) in H by nia.
        replace (start + S offset - start) with (S offset) in H by lia.

        rewrite encodeSubstringInLine'_stepindex_monotone with (index2 := l) in H; [ | apply F| lia].
        eapply encodesPredicateAt_extensional; [ | apply H]. clear H.
        intros. split.
        * intros (k0 & H2 & H3). 
          destruct k0; [ now left | right]. 
          exists k0. split; [ easy | ]. 
          rewrite projVars_comp. 
          cbn [Nat.mul] in H3.  
          enough (|s| <= l - offset - k0 * S offset).
          { rewrite Nat.min_l by lia. rewrite Nat.add_comm. apply H3. }
          apply projVars_in_ge in H3; nia.
        * intros H3. 
          destruct H3 as [H3 | (k0 & H3 & H4)]; [ exists 0; cbn; easy | ]. 
          exists (S k0). split; [ nia | ].
          rewrite projVars_comp in H4. 

          enough (|s| <= l - offset - k0 * S offset).
          { rewrite Nat.min_l in H4 by lia. cbn [Nat.mul]. rewrite <- Nat.add_comm. apply H4. }
          apply list_eq_length in H4. 
          match type of H4 with (|projVars ?a ?b ?c| = _) => specialize (projVars_length_le2 a b c) as H2 end.
          lia. 
    + (*the case where the remaining string is too short in order to place the substring constraint *)
      clear IH. assert ( (S l) < (|s|)) as H3%Nat.ltb_lt by lia. cbn -[projVars]; setoid_rewrite H3.
      intros a. unfold satisfies; cbn [negb evalFormula].
      split; [congruence | ]. 
      intros (k & H1 & H2). apply list_eq_length in H2. specialize (projVars_length_le (k * offset) (|s|) (explicitAssignment a start (S l))) as H4.
      rewrite explicitAssignment_length in H4. lia. 
  Qed.

  (*we now have to do a case analysis: if the substring which has to be checked is non-empty, we use the function defined above *)
  (*otherwise, the empty string is trivially a substring *)
  Definition encodeSubstringInLine s start l := match s with [] => Ftrue | _ => encodeSubstringInLine' s l l start end.

  Lemma encodeSubstringInLine_encodesPredicate s start l : l <= llength -> (exists k, l = k * offset) -> encodesPredicateAt start l (encodeSubstringInLine s start l) (fun m => (exists k, k * offset <= l /\ projVars (k * offset) (|s|) m = s)). 
  Proof. 
    intros. unfold encodeSubstringInLine. destruct s eqn:H1. 
    - unfold satisfies. cbn. intros; split.
      + intros _. exists 0; cbn; firstorder.
      + intros _. reflexivity. 
    - apply encodeSubstringInLine'_encodesPredicate; cbn; easy.
  Qed. 

  (*the final constraint now is a disjunction over all given substrings *)
  Definition encodeFinalConstraint (start : nat) := listOr (map (fun s => encodeSubstringInLine s start llength) final). 

  Lemma encodesPredicate_listOr (X : Type) (l : list X) (encode : X -> nat -> nat -> formula) (p : X -> list bool -> Prop) start len : 
    (forall x, x el l -> encodesPredicateAt start len (encode x start len) (p x)) 
   -> encodesPredicateAt start len (listOr (map (fun x => encode x start len) l)) (fun m => (exists x, x el l /\ p x m)). 
  Proof. 
    intros H. induction l. 
    - cbn. intros a. unfold satisfies; cbn. split; [ congruence | intros (_ & [] & _)].
    - specialize (IHl (fun x Hel => H x (or_intror Hel))). cbn. 
      specialize (H a (or_introl eq_refl)). 
      specialize (encodesPredicate_or H IHl) as H1. clear IHl H. 
      encodesPredicateAt_comp_simp H1. 
      replace (start + len - start) with len in H1 by lia. 

      eapply encodesPredicateAt_extensional; [ clear H1| apply H1].
      intros m H2; split.
      + intros (x & [-> | H] & H1). 
        * left; now rewrite projVars_all.
        * right. rewrite projVars_all; easy. 
      + intros [H | (x & H & H')].
        * exists a. now rewrite projVars_all in H.
        * exists x. rewrite projVars_all in H'; easy.
  Qed. 

  Lemma encodeFinalConstraint_encodesPredicate start : encodesPredicateAt start llength (encodeFinalConstraint start) (fun m => satFinal offset llength final m).
  Proof. 
    unfold encodeFinalConstraint. 
    eapply encodesPredicateAt_extensional; [ | apply encodesPredicate_listOr]. 
    2: { intros. apply encodeSubstringInLine_encodesPredicate; [easy | apply A]. }
    intros m H4. split. 
    - intros (subs & k & H1 & H2 & H3).
      exists subs. split; [ apply H1 | ]. 
      exists k. split; [ easy | ]. 
      destruct H3 as (b & H3). unfold projVars. rewrite H3. 
      rewrite firstn_app, firstn_all, Nat.sub_diag; cbn. now rewrite app_nil_r. 
    - intros (subs & H1 & (k & H2 & H3)).
      exists subs, k. split; [apply H1 | split; [ apply H2 | ]].
      unfold prefix. unfold projVars in H3. 
      setoid_rewrite <- firstn_skipn with (l := skipn (k * offset) m) (n:= |subs|).
      setoid_rewrite H3. eauto.
  Qed. 

  Definition encodeFinalConstraint' := encodeFinalConstraint (steps *llength).
  Lemma encodeFinalConstraint_encodesPredicate' : encodesPredicateAt (steps * llength) llength encodeFinalConstraint' (fun m => satFinal offset llength final m). 
  Proof. 
    apply encodeFinalConstraint_encodesPredicate. 
  Qed.

  (*encoding of the whole tableau: the initial constraint, window constraints and the final constraint are combined conjunctively *)
  Definition encodeTableau := encodeListAt 0 init ∧ encodeWindowsInAllLines ∧ encodeFinalConstraint'.
  Lemma encodeTableau_encodesPredicate : 
    encodesPredicateAt 0 (S steps * llength) encodeTableau 
    (fun m => projVars 0 llength m = init 
      /\ (forall i, 0 <= i < steps -> valid offset width windows (projVars (i * llength) llength m) (projVars (S i * llength) llength m)) 
      /\ satFinal offset llength final (projVars (steps * llength) llength m)). 
  Proof. 
    specialize (encodesPredicate_and (encodeListAt_encodesPredicate 0 init) encodeWindowsInAllLines_encodesPredicate) as H. 
    encodesPredicateAt_comp_simp H.  
    specialize (encodesPredicate_and H encodeFinalConstraint_encodesPredicate') as H1.
    clear H. 
    encodesPredicateAt_comp_simp H1. 
    unfold encodeTableau. 
    rewrite !Nat.sub_0_r in H1. cbn [Nat.add] in H1. 

    eapply encodesPredicateAt_extensional; [ clear H1| apply H1].
    intros m H4. 
    setoid_rewrite projVars_comp. rewrite !Nat.min_l by nia. 
    setoid_rewrite Nat.add_0_r.  
    split. 
    - intros (H1 & H2 & H3). 
      repeat split; [easy | | easy].
      intros. rewrite !Nat.min_l by nia. rewrite !projVars_comp. rewrite !Nat.min_l by nia. 
      rewrite !Nat.add_0_r. now apply H2.
    - rewrite !and_assoc. intros (H1 & H2 & H3). split; [easy |split;[ | easy]]. 
      intros. specialize (H2 i H). rewrite !Nat.min_l in H2 by nia. 
      rewrite !projVars_comp in H2. rewrite !Nat.min_l in H2 by nia.
      rewrite !Nat.add_0_r in H2. apply H2.
  Qed. 
 
  (*from a proof that a sequence of rewrites is valid, we can restore a satisfying assignment for the encoded windows of the tableau (by concatenating the strings encountered during the sequence of rewrites)*)
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
  
  (*the reduction equivalence for the wellformed BinaryPR instance *)
  Lemma reduction_wf : FSAT encodeTableau <-> exists sf, relpower (valid offset width windows) steps init sf /\ satFinal offset llength final sf. 
  Proof with (try (solve [rewrite explicitAssignment_length; cbn; nia | cbn; lia])). 
    specialize (encodeTableau_encodesPredicate) as H1. split; intros. 
    - destruct H as (a & H). apply H1 in H as (H3 & H4 & H5). 
      exists (projVars (steps * llength) llength (explicitAssignment a 0 (S steps * llength))). 
      split; [ | apply H5]. rewrite <- H3. clear H1 H3 H5. 

      cbn. rewrite projVars_length... rewrite explicitAssignment_app at 1... rewrite projVars_app1...
      rewrite Nat.add_comm. rewrite explicitAssignment_app, projVars_app2, projVars_all... 

      (*as the assignment is constructed by appending new lines, we use the reversed version of relpower *)
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
      exists a. apply H1. clear H1. 
      apply expAssgn_to_assgn_inv in H9. rewrite H5 in H9. rewrite H9. easy.
  Qed. 
End fixInstance.

(*now the whole reduction including non-wellformed instances *)
Definition BinaryPR_wf_dec (bpr : BinaryPR) := 
  leb 1 (width bpr) 
  && leb 1 (offset bpr)
  && Nat.eqb (Nat.modulo (width bpr) (offset bpr)) 0
  && leb (width bpr) (|init bpr|)
  && forallb (PRWin_of_size_dec (width bpr)) (windows bpr)
  && Nat.eqb (Nat.modulo (|init bpr|) (offset bpr)) 0. 

Lemma BinaryPR_wf_dec_correct (bpr : BinaryPR) : BinaryPR_wf_dec bpr = true <-> BinaryPR_wellformed bpr. 
Proof. 
  unfold BinaryPR_wf_dec, BinaryPR_wellformed. rewrite !andb_true_iff, !and_assoc.
  rewrite !leb_iff. rewrite <- !(reflect_iff _ _ (Nat.eqb_spec _ _ )).  
  rewrite !forallb_forall. 
  setoid_rewrite PRWin_of_size_dec_correct. 
  split; intros; repeat match goal with [H : _ /\ _ |- _] => destruct H end; 
  repeat match goal with [ |- _ /\ _ ] => split end; try easy. 
  - apply Nat.mod_divide in H1 as (k & H1); [ | lia]. 
    exists k; split; [ | apply H1 ]. destruct k; cbn in *; lia.
  - apply Nat.mod_divide in H4 as (k & H4); [ | lia].  exists k; apply H4.  
  - apply Nat.mod_divide; [ lia | ]. destruct H1 as (k & _ & H1). exists k; apply H1.
  - apply Nat.mod_divide; [ lia | ]. apply H4. 
Qed. 

(*non-wellformed instances are mapped to a trivial no-instance *)
Definition trivialNoInstance := 0 ∧ ¬0. 
Lemma trivialNoInstance_isNoInstance : not (FSAT trivialNoInstance). 
Proof. 
  intros (a & H). unfold satisfies in H. cbn in H.  
  destruct (evalVar a 0); cbn in H; congruence. 
Qed. 

Definition reduction (bpr : BinaryPR) := if BinaryPR_wf_dec bpr then encodeTableau bpr else trivialNoInstance. 

Lemma BinaryPR_to_FSAT (bpr : BinaryPR) : BinaryPRLang bpr <-> FSAT (reduction bpr). 
Proof. 
  split. 
  - intros (H1 & H2). unfold reduction. rewrite (proj2 (BinaryPR_wf_dec_correct _) H1).
    now apply reduction_wf.
  - intros H. unfold reduction in H. destruct (BinaryPR_wf_dec) eqn:H1. 
    + apply BinaryPR_wf_dec_correct in H1. apply reduction_wf in H; easy. 
    + now apply trivialNoInstance_isNoInstance in H. 
Qed. 
