From Complexity.L.Complexity Require Import Tactics MorePrelim. 
From Undecidability.L.Datatypes Require Import Lists LNat LBool LProd LOptions. 
From Complexity.L.Complexity.Problems Require Import FSAT.

(** * Some generic tools for encoding things as Boolean formulas *)

Section encodings. 
  Implicit Types (a : assgn) (v : var). 

  (** convenience functions for creating formulas *)
  Notation Ffalse := (¬Ftrue). 
  Fixpoint listOr (l : list formula) := match l with
    | [] => Ffalse 
    | a :: l => a ∨ listOr l 
    end. 

  Fixpoint listAnd (l : list formula) := match l with 
    | [] => Ftrue
    | a :: l => a ∧ listAnd l
    end.  

  Lemma listOr_sat_iff l a : satisfies a (listOr l) <-> exists f, f el l /\ satisfies a f. 
  Proof. 
    induction l; cbn. 
    - unfold satisfies. cbn. split; [congruence | intros (f & [] & _)]. 
    - unfold satisfies. rewrite evalFormula_or_iff, IHl. split.
      + intros [ H | (f & H1 & H2)]; [exists a0; eauto | exists f; eauto].  
      + intros (f & [-> | H1] & H2); [now left | right; exists f; eauto]. 
  Qed.

  Lemma listAnd_sat_iff l a : satisfies a (listAnd l) <-> forall f, f el l -> satisfies a f. 
  Proof. 
    induction l; cbn. 
    - unfold satisfies. cbn. split; [intros _ f [] | intros _; easy]. 
    - unfold satisfies. rewrite evalFormula_and_iff, IHl. split.
      + intros (H1 & H2) f [-> | H3%H2]; eauto.
      + intros H; split; [ apply H | intros f H1; apply H]; eauto.
  Qed.

  (** generate the list of values assigned to the variables by a in range [lower, lower + len) *)
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

  Lemma explicitAssignment_app a l1 len1 len2: 
    explicitAssignment a l1 (len1 + len2) = explicitAssignment a l1 len1 ++ explicitAssignment a (l1 + len1) len2. 
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

  (** from the combined assignment for the combination of two formulas, we can restore an assignment for the first formula *)
  Lemma projVars_combined1 s1 s2 l1 l2 a: explicitAssignment a s1 l1 = 
    projVars (s1 - combinedStart s1 s2) l1 (explicitAssignment a (combinedStart s1 s2) (combinedLength s1 s2 l1 l2)).
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
  Lemma projVars_combined2 s1 s2 l1 l2 a: explicitAssignment a s2 l2 = 
    projVars (s2 - combinedStart s1 s2) l2 (explicitAssignment a (combinedStart s1 s2) (combinedLength s1 s2 l1 l2)). 
  Proof. 
    unfold combinedStart, combinedLength. rewrite Nat.min_comm. rewrite Nat.max_comm. apply projVars_combined1. 
  Qed. 

  (*two formulae can be combined via ∧ *)
  Lemma encodesPredicate_and start1 start2 l1 l2 f1 f2 p1 p2 : 
    encodesPredicateAt start1 l1 f1 p1 -> encodesPredicateAt start2 l2 f2 p2 
    -> encodesPredicateAt (combinedStart start1 start2) (combinedLength start1 start2 l1 l2) (f1 ∧ f2) 
        (fun m => (p1 (projVars (start1 - combinedStart start1 start2) l1 m) 
            /\ p2 (projVars (start2 - combinedStart start1 start2) l2 m))). 
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
    -> encodesPredicateAt (combinedStart start1 start2) (combinedLength start1 start2 l1 l2) (f1 ∨ f2) 
        (fun m => (p1 (projVars (start1 - combinedStart start1 start2) l1 m) 
            \/ p2 (projVars (start2 - combinedStart start1 start2) l2 m))).
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

  (** next, we do the same for lists of formulas where the individual formulas are placed in a regular pattern starting at an index s with an offset step *)
  Fixpoint tabulate_step (step s n : nat) := 
    match n with 
      | 0 => [] 
      | S n => s :: tabulate_step step (step + s) n
    end. 
  Definition tabulate_formula s step n (t : nat -> formula) := map t (tabulate_step step s n). 

  Lemma in_tabulate_step_iff step s n x : x el tabulate_step step s n <-> exists i, i < n /\ x = s + step * i. 
  Proof. 
    revert s. induction n; cbn; intros.
    - split; [easy | intros (i & H & _); lia ].
    - split. 
      + intros [-> | H%IHn]; [exists 0; lia | ].
        destruct H as (i & H1 & ->). exists (S i). lia. 
      + intros (i & H1 & H2). 
        destruct i. 
        * now left. 
        * right. apply IHn. exists i. lia. 
  Qed.

  Lemma in_tabulate_formula_iff s step n t f: 
    f el tabulate_formula s step n t <-> exists i, i < n /\ f = t (s + step * i). 
  Proof. 
    unfold tabulate_formula. rewrite in_map_iff. setoid_rewrite in_tabulate_step_iff. 
    split. 
    - intros (x & <- & (i & H1 & ->)). exists i. eauto.
    - intros (i & H1 & ->). exists (s + step * i). eauto.
  Qed.

  Fact projVars_mul_offset a s step i l n: i < n -> explicitAssignment a (s + step * i) l = projVars (step * i) l (explicitAssignment a s (step * n + (l - step))). 
  Proof. 
    intros H. apply list_eq_nth_error. 
    split. 
    - rewrite projVars_length; rewrite !explicitAssignment_length; [lia | ]. nia.
    - rewrite explicitAssignment_length. intros k H1. 
      unfold projVars. rewrite nth_error_firstn by apply H1. 
      rewrite nth_error_skipn. rewrite !explicitAssignment_nth. 
      + easy.
      + nia. 
      + apply H1. 
  Qed.

  Lemma encodesPredicate_listOr_tabulate l (t : nat -> formula) p : 
    (forall s, encodesPredicateAt s l (t s) p)
    -> forall s step n, encodesPredicateAt s (step * n + (l - step)) (listOr (tabulate_formula s step n t)) 
        (fun m => exists i, i < n /\ p (projVars (step * i) l m)). 
  Proof. 
    (* we have to add l - step for the case that l > step; this is the case when creating the rewrite windows, for instance *)
    intros H s step n. unfold encodesPredicateAt. intros a. 
    rewrite listOr_sat_iff. setoid_rewrite in_tabulate_formula_iff. 
    split.
    - intros (f & (i & H1 & ->) & H2). exists i. split; [easy | ]. 
      specialize (H (s + step * i)). apply H in H2. 
      rewrite <- projVars_mul_offset by apply H1. apply H2. 
    - intros (i & H1 & H2). exists (t (s + step * i)). split. 
      + exists i. eauto.
      + apply H. erewrite projVars_mul_offset by apply H1. apply H2. 
  Qed.

  Lemma encodesPredicate_listAnd_tabulate l (t : nat -> formula) p : 
    (forall s, encodesPredicateAt s l (t s) p)
    -> forall s step n, encodesPredicateAt s (step * n + (l - step)) (listAnd (tabulate_formula s step n t)) 
        (fun m => forall i, i < n -> p (projVars (step * i) l m)). 
  Proof. 
    intros H s step n. unfold encodesPredicateAt. intros a. 
    rewrite listAnd_sat_iff. setoid_rewrite in_tabulate_formula_iff. 
    split.
    - intros H1 i H2. rewrite <- projVars_mul_offset by apply H2. 
      apply H, H1. exists i; eauto. 
    - intros H1 f (i & H2 & ->). apply H. 
      erewrite projVars_mul_offset by apply H2. now apply H1. 
  Qed.

  (** similarly, we can combine multiple formulas at the same position *)
  Lemma encodesPredicate_listOr_map (X : Type) s l (es : list X) (p : X -> predicate) (f : X -> formula) : 
    (forall e, e el es -> encodesPredicateAt s l (f e) (p e))
    -> encodesPredicateAt s l (listOr (map f es)) (fun m => exists e, e el es /\ p e m). 
  Proof. 
    intros H. unfold encodesPredicateAt. intros a. 
    rewrite listOr_sat_iff. setoid_rewrite in_map_iff. 
    split. 
    - intros (fo & (x & <- & Hel) & H1). apply (H _ Hel) in H1. eauto.
    - intros (x & Hel & H1). apply (H _ Hel) in H1. exists (f x). 
      split; eauto.
  Qed.

  Lemma encodesPredicate_listAnd_map (X : Type) s l (es : list X) (p : X -> predicate) (f : X -> formula) : 
    (forall e, e el es -> encodesPredicateAt s l (f e) (p e))
    -> encodesPredicateAt s l (listAnd (map f es)) (fun m => forall e, e el es -> p e m). 
  Proof. 
    intros H. unfold encodesPredicateAt. intros a. 
    rewrite listAnd_sat_iff. setoid_rewrite in_map_iff. 
    split. 
    - intros H1 e Hel. apply (H _ Hel). apply H1. eauto. 
    - intros H1 fo (x & <- & Hel). apply (H _ Hel). now apply H1. 
  Qed.

  (*encoding of single literals *)
  Definition encodeLiteral (v : var) (sign : bool) : formula := if sign then v else ¬ v. 

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
  Lemma encodesPredicateAt_extensional s l f p1 p2 : (forall m, |m| = l -> p1 m <-> p2 m) 
      -> encodesPredicateAt s l f p1 <-> encodesPredicateAt s l f p2. 
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
End encodings. 
Ltac encodesPredicateAt_comp_simp H := 
  unfold combinedStart, combinedLength in H;
  try (rewrite Nat.min_l in H by nia); try (rewrite Nat.min_r in H by nia);
  try (rewrite Nat.max_l in H by nia); try (rewrite Nat.max_r in H by nia);
  try rewrite !Nat.sub_diag in H.

(** *** extraction *)
From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Complexity.L.Complexity Require Import PolyBounds. 
From Undecidability.L.Datatypes Require Import LProd LOptions LBool LSum. 
From Undecidability.L.Functions Require Import EqBool.

Implicit Type (p : nat -> Prop).

(** listAnd *)
Definition c__listAnd := 12. 
Definition listAnd_time (l : list formula) := (|l| + 1) * c__listAnd.
Instance term_listAnd : computableTime' listAnd (fun l _ => (listAnd_time l, tt)). 
Proof. 
  extract. solverec. all: unfold listAnd_time, c__listAnd; solverec. 
Qed.

Lemma listAnd_varsIn (p : nat ->Prop) l: (forall f, f el l -> formula_varsIn p f) -> formula_varsIn p (listAnd l). 
Proof. 
  unfold formula_varsIn. intros H; induction l; cbn.
  - intros v H1. inv H1.  
  - intros v H1. inv H1; [eapply H; eauto | eapply IHl; eauto]. 
Qed. 

Lemma listAnd_size l : formula_size (listAnd l) <= sumn (map formula_size l) + |l| + 1. 
Proof. 
  induction l; cbn; [lia | rewrite IHl; lia].
Qed. 

(** listOr *)
Definition c__listOr := 12.
Definition listOr_time (l : list formula) := (|l| + 1) * c__listOr.
Instance term_listOr : computableTime' listOr (fun l _ => (listOr_time l, tt)). 
Proof. 
  extract. solverec. all: unfold listOr_time, c__listOr; solverec. 
Qed.

Lemma listOr_varsIn p l: (forall f, f el l -> formula_varsIn p f) -> formula_varsIn p (listOr l). 
Proof. 
  unfold formula_varsIn. intros H; induction l; cbn.
  - intros v H1. inv H1. inv H2.  
  - intros v H1. inv H1; [eapply H; eauto | eapply IHl; eauto]. 
Qed. 

Lemma listOr_size l : formula_size (listOr l) <= sumn (map formula_size l) + |l| + 2. 
Proof. 
  induction l; cbn; [lia | rewrite IHl; lia].
Qed. 

(** tabulate_step *)
Definition c__tabulateStep := 13 + c__add1.
Definition tabulate_step_time (step n : nat) := n * (add_time step + c__tabulateStep) + c__tabulateStep.
Instance term_tabulate_step : computableTime' tabulate_step (fun step _ => (5, fun s _ => (1, fun n _ => (tabulate_step_time step n, tt)))). 
Proof. 
  extract. solverec. 
  all: unfold tabulate_step_time, c__tabulateStep; solverec. 
Qed.

Definition poly__tabulateStep n := n * ((n + 1) * c__add + c__tabulateStep) + c__tabulateStep.
Lemma tabulate_step_time_bound step n : tabulate_step_time step n <= poly__tabulateStep (size (enc step) + size (enc n)). 
Proof. 
  unfold tabulate_step_time. rewrite size_nat_enc_r with (n := n) at 1. 
  unfold add_time. rewrite size_nat_enc_r with (n := step) at 1. 
  unfold poly__tabulateStep; solverec.  
Qed.
Lemma tabulate_step_poly : monotonic poly__tabulateStep /\ inOPoly poly__tabulateStep.
Proof. 
  unfold poly__tabulateStep; split; smpl_inO. 
Qed.

Lemma tabulate_step_length step s n: |tabulate_step step s n| = n.
Proof. 
  revert step s. induction n; cbn; intros; [lia | rewrite IHn; lia]. 
Qed. 

(** tabulate_formula *)
Definition c__tabulateFormula := 8. 
Definition tabulate_formula_time (s step n : nat) (tf : nat -> nat) := tabulate_step_time step n + map_time tf (tabulate_step step s n) + c__tabulateFormula.
Instance term_tabulate_formula : computableTime' tabulate_formula (fun s _ => (1, fun step _ => (1, fun n _ => (1, fun t tf => (tabulate_formula_time s step n (callTime tf), tt))))). 
Proof. 
  extract. solverec. 
  unfold tabulate_formula_time, c__tabulateFormula; solverec. 
Qed.  

Lemma formula_varsIn_monotonic (p1 p2 : nat -> Prop) : (forall n, p1 n -> p2 n) -> forall f, formula_varsIn p1 f -> formula_varsIn p2 f. 
Proof. 
  intros H f. unfold formula_varsIn. eauto.
Qed. 

Lemma tabulate_formula_varsIn s step n t (g : nat -> nat): 
  (forall start, formula_varsIn (fun n => n < g start) (t start))
  -> monotonic g
  -> forall f, f el tabulate_formula s step n t -> formula_varsIn (fun v => v < g (s + step * (n -1))) f. 
Proof. 
  intros H H0 f Hel. unfold tabulate_formula in Hel. apply in_map_iff in Hel as (i & <- & Hel). 
  apply in_tabulate_step_iff in Hel as (i' & H1 & ->). 
  eapply formula_varsIn_monotonic. 
  2: apply H. 
  cbn. intros n' Hn'. unfold monotonic in H0. specialize (H0 (s + step * i') (s + step * (n -1)) ltac:(nia)). nia. 
Qed. 

Lemma tabulate_formula_length s step n t : |tabulate_formula s step n t| = n. 
Proof. 
  revert s step. induction n; cbn; intros; [lia | ]. 
  unfold tabulate_formula in IHn. now rewrite IHn. 
Qed. 

(** encodeLiteral *)
Definition c__encodeLiteral := 6. 
Instance term_encodeLiteral : computableTime' encodeLiteral (fun n _ => (1, fun b _ => (c__encodeLiteral, tt))). 
Proof. 
  extract. solverec. all: unfold c__encodeLiteral; solverec. 
Qed.

Lemma encodeLiteral_size v b : formula_size (encodeLiteral v b) <= 2. 
Proof. 
  unfold encodeLiteral. destruct b; cbn; lia. 
Qed. 

Ltac varsIn_inv := 
  repeat match goal with 
    | [ H: formula_varsIn ?f |- _] => inv H
    | [ H: varInFormula ?v ?f|- _]=> inv H
  end. 

Lemma encodeLiteral_varsIn v b : formula_varsIn (fun n => n = v) (encodeLiteral v b).  
Proof. 
  unfold encodeLiteral. destruct b; cbn; intros v' H; varsIn_inv; lia. 
Qed. 

(** encodeListAt *)
Definition c__encodeListAt := c__encodeLiteral + c__add1 + add_time 1 + 15.
Definition encodeListAt_time (l : list bool) := (|l| + 1) * c__encodeListAt. 
Instance term_encodeListAt : computableTime' encodeListAt (fun s _ => (5, fun l _ => (encodeListAt_time l, tt))). 
Proof. 
  extract. solverec. 
  all: unfold encodeListAt_time, c__encodeListAt; solverec.  
Qed.

Definition poly__encodeListAt n := (n + 1) * c__encodeListAt.
Lemma encodeListAt_time_bound l : encodeListAt_time l <= poly__encodeListAt (size (enc l)). 
Proof. 
  unfold encodeListAt_time. rewrite list_size_length. 
  unfold poly__encodeListAt; solverec. 
Qed. 
Lemma encodeListAt_poly : monotonic poly__encodeListAt /\ inOPoly poly__encodeListAt. 
Proof. 
  unfold poly__encodeListAt; split; smpl_inO. 
Qed.

Lemma encodeListAt_varsIn start l: formula_varsIn (fun n => n >= start /\ n < start + |l|) (encodeListAt start l). 
Proof. 
  revert start; induction l; cbn; intros. 
  - intros v H; varsIn_inv.  
  - intros v H. inv H. 
    + apply encodeLiteral_varsIn in H1. lia. 
    + apply IHl in H1. lia. 
Qed. 

Lemma encodeListAt_size start l : formula_size (encodeListAt start l) <= 3 * (|l|) + 1. 
Proof. 
  revert start; induction l; cbn -[Nat.mul]; intros; [lia | rewrite IHl]. rewrite encodeLiteral_size. lia. 
Qed. 
 
