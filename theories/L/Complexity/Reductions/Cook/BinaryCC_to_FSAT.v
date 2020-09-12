From PslBase Require Import Base. 
From Undecidability.L.Complexity Require Import Tactics MorePrelim. 
From Undecidability.L.Datatypes Require Import Lists LNat LBool LProd LOptions. 
From Undecidability.L.Complexity.Problems Require Import FSAT Cook.BinaryCC.
From Undecidability.L.Complexity.Reductions.Cook Require Import FormulaEncoding.
Require Import Lia. 

(** * Reduction of BinaryCC to FSAT *)
(** High-level overview:
We lay out the BinaryCC computation in a tableau which has (steps + 1) lines, where steps is the number of steps of the BCC instance, 
and each line has a length which is equal to the length of the BCC strings.
Each cell of the tableau corresponds to one symbol of a BCC string and is encoded using a single Boolean variable in the FSAT instance.

The FSAT formula consists of three gadgets, encoding:
- the constraint on the initial string
- the validity of CC-steps 
- the final constraints.

The constraint on the initial string is straightforward to encode: We just have a big AND over the positions of the string.

For the validity of coverings, we have a AND consisting of a subformula for each of the steps.
Each step in turn forces that the successor string evolves validly from the current string - we have an AND over the offsets of the string
at which covering cards have to hold. 
For each of the offsets, we then have a disjunction over all covering cards. 
That a card is covering at a position is encoded similarly to the initial string.

For the final constraint, we have a disjunction over the final strings and a nested disjunction over all positions at which a string can be a substring.
*)

Section fixInstance. 
  Variable (bpr : BinaryCC). 
  
  Notation offset := (offset bpr). 
  Notation width := (width bpr). 
  Notation init := (init bpr). 
  Notation cards := (cards bpr).
  Notation final := (final bpr).
  Notation steps := (steps bpr). 

  Context (A : BinaryCC_wellformed bpr). 
  Notation llength := (length init). 
  Implicit Types (a : assgn) (v : var). 
  Notation Ffalse := (¬ Ftrue). 


  (** encoding of cards *)
  (** startA is the position at which the premise is placed, startB the position at which the conclusion is placed *)
  Definition encodeCardAt (startA startB : nat) (card : CCCard bool) := encodeListAt startA (prem card) ∧ encodeListAt startB (conc card). 

  Lemma encodeCardAt_encodesPredicate start len card : 
    card el cards -> encodesPredicateAt start (len + width) (encodeCardAt start (start + len) card) (fun m => projVars 0 width m = prem card /\ projVars len width m = conc card). 
  Proof. 
    intros H0. 
    specialize (encodesPredicate_and (encodeListAt_encodesPredicate start (prem card)) (encodeListAt_encodesPredicate (start + len) (conc card))) as H. 
    destruct A as (_ & _ & _ & A0 & A1 & _). apply A1 in H0 as (H0 & H0').
    encodesPredicateAt_comp_simp H. 
    rewrite !H0 in H. rewrite !H0' in H.
    replace (start + len + width - start) with (len + width) in H by lia. 
    replace (start + len - start) with len in H by lia.
    unfold encodeCardAt. eapply encodesPredicateAt_extensional; [ | apply H].
    tauto.
  Qed.

  (** encoding of the disjunction of all cards of the BinaryCC instance  *)
  Definition encodeCardsAt (startA startB : nat) := listOr (map (encodeCardAt startA startB) cards). 

  Lemma encodeCardsAt_encodesPredicate len start : len >= width -> encodesPredicateAt start (len + width) (encodeCardsAt start (start + len)) (fun m => exists card, card el cards /\ projVars 0 width m = prem card /\ projVars len width m = conc card). 
  Proof. 
    intros F0. apply encodesPredicate_listOr_map. 
    intros card Hel. apply encodeCardAt_encodesPredicate, Hel. 
  Qed.

  (*encoding of all cards of one line of the tableau *)
  (*we only need to place a card every offset fields, but subtracting offset isn't structurally recursive *)
  (*therefore we use a stepindex (initalise to the same value as l) *)
  Fixpoint encodeCardsInLine' (stepindex l : nat) (startA startB : nat) := 
    if l <? width then Ftrue 
                  else match stepindex with 
                    | 0 => Ftrue
                    | S stepindex => encodeCardsAt startA startB ∧ encodeCardsInLine' stepindex (l - offset) (startA + offset) (startB + offset)
                    end.

  Lemma encodeCardsInLineP_stepindex_monotone' index startA startB : forall n, n <= index -> encodeCardsInLine' index n startA startB = encodeCardsInLine' (S index) n startA startB. 
  Proof. 
    destruct A as (A1 & A2 & _).
    revert startA startB.
    induction index as [ | index IH]; intros. 
    - unfold encodeCardsInLine'. assert (n = 0) as -> by lia. cbn; destruct width; [ lia | easy ].
    - unfold encodeCardsInLine'. destruct (Nat.ltb n width); [ easy | ]. fold encodeCardsInLine'. 
      erewrite IH by lia. easy. 
  Qed. 

  Lemma encodeCardsInLineP_stepindex_monotone index index' startA startB : index' >= index -> encodeCardsInLine' index index startA startB = encodeCardsInLine' index' index startA startB. 
  Proof. 
    intros. revert index H.
    induction index' as [ | index' IH]; intros. 
    - assert (index = 0) as -> by lia. easy.
    - destruct (nat_eq_dec (S index') index). 
      + now rewrite e.
      + assert (index' >= index) as H1 by lia. rewrite <- encodeCardsInLineP_stepindex_monotone' by lia. now apply IH.
  Qed.

  Lemma encodeCardsInLineP_encodesPredicate start l : l <= llength -> (exists k, l = k * offset) -> encodesPredicateAt start (l + llength) (encodeCardsInLine' l l start (start + llength)) (fun m => valid offset width cards (projVars 0 l m) (projVars llength l m)). 
  Proof. 
    intros A0.
    (*need strong induction *)
    destruct A as (A1 & A4 & A2 & A5 & A7 & A3). 
    revert start A0.  
    apply complete_induction with (x := l). clear l. intros l IH. intros. 

    (*case analysis on the stepindex *)
    destruct l.
    - (*we use that width > 0 *)
      unfold encodeCardsInLine'. rewrite (proj2 (Nat.ltb_lt _ _) A1). 
      intros a. split; [ intros; constructor | intros _; unfold satisfies; eauto].  
    - destruct (le_lt_dec width (S l)). 
      + assert (~ (S l) < width) as H3%Nat.ltb_nlt by lia. cbn -[projVars]; setoid_rewrite H3. 
        destruct offset as [ | offset]; [ lia | ].
        (* we use the IH for l - offset *)
 
        assert (S l - S offset < S l) as H1 by lia. apply IH with (start := start + S offset) in H1. 2: lia. 
        2: { destruct H as (k & H). destruct k; [ lia | ]. exists k. lia. }
        clear H IH. 
        assert (llength >= width) as H0 by lia.
        apply (encodeCardsAt_encodesPredicate start) in H0. 

        specialize (encodesPredicate_and H0 H1) as H2. clear H1 H0.
        encodesPredicateAt_comp_simp H2. 

        replace (start + S offset + llength) with (start + llength + S offset) in H2 by lia. 
        replace (start + S offset + (S l - S offset + llength) - start) with (S (l + llength)) in H2. 
        2: { destruct A2 as (? & A2 & A6). nia. }
        
        rewrite encodeCardsInLineP_stepindex_monotone with (index' := l) in H2; [ | lia].
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
          2 : { exfalso. apply list_eq_length in H0. rewrite !app_length in H0. rewrite !projVars_length in H0; [ | easy | easy]. lia. }
          1: { exfalso. apply list_eq_length in H3. rewrite !app_length in H3. rewrite projVars_length in H3; [ | cbn; nia]. cbn in H3. lia. } 

          apply app_eq_length in H2 as (-> & ->); [ | rewrite projVars_length; [easy | nia] ].
          apply app_eq_length in H0 as (-> & ->); [ | rewrite projVars_length; [easy | nia]]. 
          split.
          -- exists card. rewrite !projVars_comp; cbn. rewrite !Nat.min_l by lia. 
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
          destruct H1 as (card & H1 & F1 & F2). 
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
    + (*the case where the remaining string is too short for a rewrite card to hold - validity holds vacuously *)
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

  (** the above construction specialised to the setting we need: the conclusion starts exactly one line after the premise *)
  Definition encodeCardsInLine start := encodeCardsInLine' llength llength start (start + llength). 
  Lemma encodeCardsInLine_encodesPredicate start : encodesPredicateAt start (llength + llength) (encodeCardsInLine start) (fun m => valid offset width cards (projVars 0 llength m) (projVars llength llength m)). 
  Proof. 
    unfold encodeCardsInLine.
    apply (@encodeCardsInLineP_encodesPredicate start llength); [easy | apply A].
  Qed. 

  (** encoding of cards in all lines of the tableau *)
  Definition encodeCardsInAllLines := listAnd (tabulate_formula 0 llength steps encodeCardsInLine). 
  Lemma encodeCardsInAllLines_encodesPredicate : encodesPredicateAt 0 ((S steps) * llength) encodeCardsInAllLines 
    (fun m => (forall i, 0 <= i < steps -> valid offset width cards (projVars (i * llength) llength m) (projVars (S i * llength) llength m))). 
  Proof. 
    eapply encodesPredicateAt_extensional. 
    2: { unfold encodeCardsInAllLines. 
         replace (S steps * llength) with (llength * steps + ((llength + llength) -llength)) by lia. 
         apply encodesPredicate_listAnd_tabulate. intros s. apply encodeCardsInLine_encodesPredicate. 
    } 
    intros m Hlen. split. 
    - intros H i H1. specialize (H i ltac:(lia)). 
      rewrite !projVars_comp. rewrite !Nat.min_l by lia. cbn. rewrite Nat.mul_comm at 1. 
      replace (llength + llength * i) with (S i * llength) by lia. apply H. 
    - intros H i (_ & H1). specialize (H i H1). rewrite !projVars_comp in H. rewrite !Nat.min_l in H by lia. 
      cbn in H. cbn. rewrite Nat.mul_comm. apply H. 
  Qed.

  (** encode the substring constraint for a single string s *)
  (** should only be called for s satisfying |s| > 0; for s = nil, the breaking condition does not work as intended*)
  (** in principle, this is not a problem as the resulting formula is still equivalent to the desired formula, but this breaks monotonicity*)
  Fixpoint encodeSubstringInLine' (s : list bool) (stepindex l : nat) (start : nat) := 
    if l <? |s| then Ffalse
                  else match stepindex with 
                    | 0 => (match s with [] => Ftrue | _ => Ffalse end)
                    | S stepindex => encodeListAt start s ∨ encodeSubstringInLine' s stepindex (l - offset) (start + offset) 
                    end.

  (** the requirement |s| > 0 is needed for monotonicity *)
  Lemma encodeSubstringInLineP_stepindex_monotone' s index start : forall n, |s| > 0 -> n <= index -> encodeSubstringInLine' s index n start = encodeSubstringInLine' s (S index) n start. 
  Proof. 
    destruct A as (A1 & A2 & _).
    revert start.
    induction index as [ | index IH]; intros. 
    - unfold encodeSubstringInLine'. assert (n = 0) as -> by lia. cbn; destruct s; [ cbn in *; lia | easy ]. 
    - unfold encodeSubstringInLine'. destruct (Nat.ltb n (|s|)); [ easy | ]. fold encodeSubstringInLine'. 
      erewrite IH by lia. easy. 
  Qed. 

  Lemma encodeSubstringInLineP_stepindex_monotone s index1 index2 start : 
    |s| > 0 -> index2 >= index1 -> encodeSubstringInLine' s index1 index1 start = encodeSubstringInLine' s index2 index1 start.
  Proof. 
    intros. revert index1 H0. 
    induction index2 as [ | index2 IH]; intros.
    - assert (index1 = 0) as -> by lia. easy.
    - destruct (nat_eq_dec (S index2) index1). 
      + now rewrite e.
      + assert (index2 >= index1) as H1 by lia. rewrite <- encodeSubstringInLineP_stepindex_monotone' by lia. now apply IH.
  Qed. 

  Lemma encodeSubstringInLineP_encodesPredicate s start l : |s| > 0 -> l <= llength 
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
        assert (k > 0) by nia. (*a hint for nia - without it, the follocardg replace will not work *)
        replace (start + S offset + (S l - S offset) - start) with (S l) in H by nia.
        replace (start + S offset - start) with (S offset) in H by lia.

        rewrite encodeSubstringInLineP_stepindex_monotone with (index2 := l) in H; [ | apply F| lia].
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

  (** we now have to do a case analysis: if the substring which has to be checked is non-empty, we use the function defined above *)
  (** otherwise, the empty string is trivially a substring *)
  Definition encodeSubstringInLine s start l := match s with [] => Ftrue | _ => encodeSubstringInLine' s l l start end.

  Lemma encodeSubstringInLine_encodesPredicate s start l : l <= llength -> (exists k, l = k * offset) -> encodesPredicateAt start l (encodeSubstringInLine s start l) (fun m => (exists k, k * offset <= l /\ projVars (k * offset) (|s|) m = s)). 
  Proof. 
    intros. unfold encodeSubstringInLine. destruct s eqn:H1. 
    - unfold satisfies. cbn. intros; split.
      + intros _. exists 0; cbn; firstorder.
      + intros _. reflexivity. 
    - apply encodeSubstringInLineP_encodesPredicate; cbn; easy.
  Qed. 

  (** the final constraint now is a disjunction over all given substrings *)
  Definition encodeFinalConstraint (start : nat) := listOr (map (fun s => encodeSubstringInLine s start llength) final). 

  Lemma encodeFinalConstraint_encodesPredicate start : encodesPredicateAt start llength (encodeFinalConstraint start) (fun m => satFinal offset llength final m).
  Proof. 
    unfold encodeFinalConstraint. 
    eapply encodesPredicateAt_extensional; [ | apply encodesPredicate_listOr_map].
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

  (** encoding of the whole tableau: the initial constraint, card constraints and the final constraint are combined conjunctively *)
  Definition encodeTableau := encodeListAt 0 init ∧ encodeCardsInAllLines ∧ encodeFinalConstraint'.
  Lemma encodeTableau_encodesPredicate : 
    encodesPredicateAt 0 (S steps * llength) encodeTableau 
    (fun m => projVars 0 llength m = init 
      /\ (forall i, 0 <= i < steps -> valid offset width cards (projVars (i * llength) llength m) (projVars (S i * llength) llength m)) 
      /\ satFinal offset llength final (projVars (steps * llength) llength m)). 
  Proof. 
    specialize (encodesPredicate_and (encodeListAt_encodesPredicate 0 init) encodeCardsInAllLines_encodesPredicate) as H. 
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
 
  (** from a proof that a sequence of rewrites is valid, we can restore a satisfying assignment for the encoded cards of the tableau (by concatenating the strings encountered during the sequence of rewrites)*)
  Lemma relpower_valid_to_assignment n x y: 
    relpower (valid offset width cards) n x y -> |x| = llength 
    -> exists m, |m| = (S n * llength) /\ projVars 0 llength m = x /\ projVars (n * llength) llength m = y 
      /\ (forall i, 0 <= i < n -> valid offset width cards (projVars (i * llength) llength m) (projVars (S i * llength) llength m)). 
  Proof. 
    induction 1 as [ ? | ? ? ? ? H H0 IH]. 
    - cbn. exists a. rewrite projVars_all; [ | lia]. easy.
    - intros. specialize (valid_length_inv H) as H2. rewrite H1 in H2; symmetry in H2. 
      apply IH in H2 as (m & H2 & H3 & H4 & H5). clear IH. 
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
  
  (*the reduction equivalence for the wellformed BinaryCC instance *)
  Lemma reduction_wf : FSAT encodeTableau <-> exists sf, relpower (valid offset width cards) steps init sf /\ satFinal offset llength final sf. 
  Proof with (try (solve [rewrite explicitAssignment_length; cbn; nia | cbn; lia])). 
    specialize (encodeTableau_encodesPredicate) as H1. split; intros. 
    - destruct H as (a & H). apply H1 in H as (H3 & H4 & H5). 
      exists (projVars (steps * llength) llength (explicitAssignment a 0 (S steps * llength))). 
      split; [ | apply H5]. rewrite <- H3. clear H1 H3 H5. 

      cbn. rewrite projVars_length... rewrite explicitAssignment_app at 1... rewrite projVars_app1...
      rewrite Nat.add_comm. rewrite explicitAssignment_app, projVars_app2, projVars_all... 

      (*as the assignment is constructed by appending new lines, we use the reversed version of relpower *)
      apply relpower_relpowerRev. induction steps as [ | n IH]. 
      + cbn. constructor. 
      + econstructor. 
        * apply IH. intros. specialize (H4 i). clear IH. 
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
        * specialize (H4 n). clear IH. 
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

(** now the whole reduction including non-wellformed instances *)
Definition BinaryCC_wf_dec (bpr : BinaryCC) := 
  leb 1 (width bpr) 
  && leb 1 (offset bpr)
  && Nat.eqb (Nat.modulo (width bpr) (offset bpr)) 0
  && leb (width bpr) (|init bpr|)
  && forallb (CCCard_of_size_dec (width bpr)) (cards bpr)
  && Nat.eqb (Nat.modulo (|init bpr|) (offset bpr)) 0. 

Lemma BinaryCC_wf_dec_correct (bpr : BinaryCC) : BinaryCC_wf_dec bpr = true <-> BinaryCC_wellformed bpr. 
Proof. 
  unfold BinaryCC_wf_dec, BinaryCC_wellformed. rewrite !andb_true_iff, !and_assoc.
  rewrite !leb_iff. rewrite <- !(reflect_iff _ _ (Nat.eqb_spec _ _ )).  
  rewrite !forallb_forall. 
  setoid_rewrite CCCard_of_size_dec_correct. 
  split; intros; repeat match goal with [H : _ /\ _ |- _] => destruct H end; 
  repeat match goal with [ |- _ /\ _ ] => split end; try easy. 
  - apply Nat.mod_divide in H1 as (k & H1); [ | lia]. 
    exists k; split; [ | apply H1 ]. destruct k; cbn in *; lia.
  - apply Nat.mod_divide in H4 as (k & H4); [ | lia].  exists k; apply H4.  
  - apply Nat.mod_divide; [ lia | ]. destruct H1 as (k & _ & H1). exists k; apply H1.
  - apply Nat.mod_divide; [ lia | ]. apply H4. 
Qed. 

(** non-wellformed instances are mapped to a trivial no-instance *)
Definition trivialNoInstance := 0 ∧ ¬0. 
Lemma trivialNoInstance_isNoInstance : not (FSAT trivialNoInstance). 
Proof. 
  intros (a & H). unfold satisfies in H. cbn in H.  
  destruct (evalVar a 0); cbn in H; congruence. 
Qed. 

Definition reduction (bpr : BinaryCC) := if BinaryCC_wf_dec bpr then encodeTableau bpr else trivialNoInstance. 

Lemma BinaryCC_to_FSAT (bpr : BinaryCC) : BinaryCCLang bpr <-> FSAT (reduction bpr). 
Proof. 
  split. 
  - intros (H1 & H2). unfold reduction. rewrite (proj2 (BinaryCC_wf_dec_correct _) H1).
    now apply reduction_wf.
  - intros H. unfold reduction in H. destruct (BinaryCC_wf_dec) eqn:H1. 
    + apply BinaryCC_wf_dec_correct in H1. apply reduction_wf in H; easy. 
    + now apply trivialNoInstance_isNoInstance in H. 
Qed. 

(** ** extraction *)
From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Complexity Require Import PolyBounds. 
From Undecidability.L.Datatypes Require Import LProd LOptions LBool LSum. 
From Undecidability.L.Functions Require Import EqBool.

 
(** encodeCardAt *)
Definition c__encodeCardAt := FlatCC.cnst_prem + FlatCC.cnst_conc + 13.
Definition encodeCardAt_time (card : CCCard bool) := encodeListAt_time (prem card) + encodeListAt_time (conc card) + c__encodeCardAt.
Instance term_encodeCardAt : computableTime' encodeCardAt (fun s1 _ => (1, fun s2 _ => (1, fun card _ => (encodeCardAt_time card, tt)))). 
Proof. 
  extract. solverec. 
  unfold encodeCardAt_time, c__encodeCardAt; solverec. 
Qed.

Definition poly__encodeCardAt k := (k + 1) * c__encodeListAt * 2 + c__encodeCardAt.
Lemma encodeCardAt_time_bound card k: CCCard_of_size card k -> encodeCardAt_time card <= poly__encodeCardAt k. 
Proof. 
  unfold CCCard_of_size. intros [H1 H2]. 
  unfold encodeCardAt_time. unfold encodeListAt_time. rewrite H1, H2. 
  unfold poly__encodeCardAt; solverec.
Qed. 
Lemma encodeCardAt_poly : monotonic poly__encodeCardAt /\ inOPoly poly__encodeCardAt. 
Proof. 
  unfold poly__encodeCardAt; split; smpl_inO. 
Qed. 

Lemma encodeCardAt_varsIn s1 s2 k card : CCCard_of_size card k -> formula_varsIn (fun n => (n >= s1 /\ n < s1 + k) \/ (n >= s2 /\ n < s2 + k)) (encodeCardAt s1 s2 card). 
Proof. 
  intros [H1 H2]. unfold encodeCardAt. intros v H. inv H.  
  - apply encodeListAt_varsIn in H3. lia. 
  - apply encodeListAt_varsIn in H3. lia. 
Qed. 

Lemma encodeCardAt_size s1 s2 k card : CCCard_of_size card k -> formula_size (encodeCardAt s1 s2 card) <= 6 * k + 3. 
Proof. 
  intros [H1 H2]. unfold encodeCardAt. cbn -[Nat.mul]. rewrite !encodeListAt_size. rewrite H1, H2. nia. 
Qed. 

(** encodeCardsAt *)
Definition c__encodeCardsAt := 4 + c__cards.
Definition encodeCardsAt_time (bpr : BinaryCC) (s1 s2 : nat) := map_time encodeCardAt_time (cards bpr) + listOr_time (map (encodeCardAt s1 s2) (cards bpr)) + c__encodeCardsAt.
Instance term_encodeCardsAt : computableTime' encodeCardsAt (fun bpr _ => (1, fun s1 _ => (1, fun s2 _ => (encodeCardsAt_time bpr s1 s2, tt)))). 
Proof. 
  extract. solverec. 
  unfold encodeCardsAt_time, c__encodeCardsAt; simp_comp_arith; solverec. 
Qed.
  
Definition poly__encodeCardsAt n := n * (poly__encodeCardAt n + c__map) + c__map + (n + 1) * c__listOr + c__encodeCardsAt.
Lemma encodeCardsAt_time_bound bpr s1 s2: 
  BinaryCC_wellformed bpr 
  -> encodeCardsAt_time bpr s1 s2 <= poly__encodeCardsAt (size (enc bpr)). 
Proof. 
  intros H. unfold encodeCardsAt_time. 
  rewrite map_time_mono. 2: { intros card H1. apply H in H1. instantiate (1 := fun _ => _). cbn. 
    rewrite encodeCardAt_time_bound by apply H1. reflexivity. 
  } 
  rewrite map_time_const.
  unfold listOr_time. rewrite map_length. 
  poly_mono encodeCardAt_poly. 2: { rewrite size_nat_enc_r. instantiate (1 := size (enc bpr)). rewrite BinaryCC_enc_size. lia. }
  rewrite list_size_length. replace_le (size (enc (cards bpr))) with (size (enc bpr)) by (rewrite BinaryCC_enc_size; lia). 
  unfold poly__encodeCardsAt. solverec.   
Qed.
Lemma encodeCardsAt_poly : monotonic poly__encodeCardsAt /\ inOPoly poly__encodeCardsAt. 
Proof. 
  unfold poly__encodeCardsAt; split; smpl_inO; apply encodeCardAt_poly. 
Qed.

Lemma encodeCardsAt_varsIn s1 s2 bpr : 
  BinaryCC_wellformed bpr
  -> formula_varsIn (fun n => (n >= s1 /\ n < s1 + width bpr) \/ (n >= s2 /\ n < s2 + width bpr)) (encodeCardsAt bpr s1 s2). 
Proof. 
  intros (_ & _ & _ & _ & H1 & _). 
  unfold encodeCardsAt. apply listOr_varsIn. 
  intros f (card & <- & Hel)%in_map_iff. apply encodeCardAt_varsIn, H1, Hel. 
Qed. 

Lemma encodeCardsAt_size s1 s2 bpr : 
  BinaryCC_wellformed bpr
  -> formula_size (encodeCardsAt bpr s1 s2) <= |cards bpr| * (6 * width bpr + 4) + 2. 
Proof. 
  intros (_ &_  & _ & _ & H1 & _). 
  unfold encodeCardsAt. rewrite listOr_size. 
  rewrite sumn_map_mono. 2: { intros f (card & <- & Hel)%in_map_iff. instantiate (1 := fun _ => _); cbn -[formula_size].
    rewrite encodeCardAt_size by apply H1, Hel. reflexivity. 
  } 
  rewrite sumn_map_const, !map_length. nia. 
Qed. 

(** encodeCardsInLine' *)
Definition c__encodeCardsInLineP := c__width + c__sub1 + 3 * c__offset + 2 * c__add1 + 24.
Fixpoint encodeCardsInLineP_time (bpr : BinaryCC) (stepindex l startA startB : nat) := 
  match stepindex with 
  | 0 => 0 
  | S stepi => encodeCardsAt_time bpr startA startB + sub_time l (offset bpr) + add_time startA + add_time startB + encodeCardsInLineP_time bpr stepi (l - offset bpr) (startA + offset bpr) (startB + offset bpr)
  end + ltb_time l (width bpr) + c__encodeCardsInLineP.
Instance term_encodeCardsInLine': computableTime' encodeCardsInLine' (fun bpr _ => (1, fun stepi _ => (5, fun l _ => (1, fun s1 _ => (5, fun s2 _ => (encodeCardsInLineP_time bpr stepi l s1 s2, tt)))))). 
Proof. 
  extract. 
  solverec. all: unfold c__encodeCardsInLineP; solverec. 
Qed.

(** we first bound the components that can be accounted for by the pr instance and bound the start indices inductively; 
    we have the invariant that start' <= start + stepindex * offset for every start' obtained by recursion*)
Definition poly__encodeCardsInLineP1 n := poly__encodeCardsAt n + (n + 1) * c__sub + (c__leb * (1 + n) + c__ltb) + c__encodeCardsInLineP.
Lemma encodeCardsInLineP_time_bound1 bpr stepindex l startA startB : 
  BinaryCC_wellformed bpr 
  -> encodeCardsInLineP_time bpr stepindex l startA startB <= (stepindex + 1) * poly__encodeCardsInLineP1 (size (enc bpr)) 
    + stepindex * (stepindex * (offset bpr) + startA + stepindex * (offset bpr) + startB + 2) * c__add. 
Proof. 
  intros H.
  revert l startA startB. unfold encodeCardsInLineP_time. induction stepindex; intros.
  - unfold ltb_time, leb_time. rewrite Nat.le_min_r. 
    rewrite size_nat_enc_r with (n := width bpr) at 1. 
    replace_le (size (enc (width bpr))) with (size (enc bpr)) by (rewrite BinaryCC_enc_size; cbn; lia). 
    unfold poly__encodeCardsInLineP1. leq_crossout. 
  - rewrite IHstepindex. clear IHstepindex. 
    rewrite encodeCardsAt_time_bound by apply H. 
    unfold sub_time. rewrite Nat.le_min_r. 
    unfold ltb_time, leb_time. rewrite Nat.le_min_r. 
    rewrite size_nat_enc_r with (n := offset bpr) at 1. 
    replace_le (size (enc (offset bpr))) with (size (enc bpr)) by (rewrite BinaryCC_enc_size; cbn; lia). 
    rewrite size_nat_enc_r with (n := width bpr) at 1. 
    replace_le (size (enc (width bpr))) with (size (enc bpr)) by (rewrite BinaryCC_enc_size; cbn; lia). 
    unfold poly__encodeCardsInLineP1. unfold add_time. nia.  
Qed.
Lemma encodeCardsInLineP1_poly : monotonic poly__encodeCardsInLineP1 /\ inOPoly poly__encodeCardsInLineP1. 
Proof. 
  unfold poly__encodeCardsInLineP1; split; smpl_inO; apply encodeCardsAt_poly. 
Qed.

(** in a second step, we also bound the numbers by their encoding size *)
Definition poly__encodeCardsInLine' n := (n + 1) * poly__encodeCardsInLineP1 n + n * (n * n + n + 1) * c__add * 2.
Lemma encodeCardsInLineP_time_bound bpr stepindex l startA startB : 
  BinaryCC_wellformed bpr -> encodeCardsInLineP_time bpr stepindex l startA startB <= poly__encodeCardsInLine' (size (enc bpr) + size (enc stepindex) + size (enc startA) + size (enc startB)). 
Proof. 
  intros H. rewrite encodeCardsInLineP_time_bound1 by easy.
  rewrite size_nat_enc_r with (n := stepindex) at 1 2 3 4. 
  rewrite size_nat_enc_r with (n := offset bpr) at 1 2. 
  replace_le (size (enc (offset bpr))) with (size (enc bpr)) by (rewrite BinaryCC_enc_size; lia). 
  rewrite size_nat_enc_r with (n := startA) at 1. 
  rewrite size_nat_enc_r with (n := startB) at 1. 
  pose (g := size (enc bpr) + size (enc stepindex) + size (enc startA) + size (enc startB)). 
  poly_mono encodeCardsInLineP1_poly. 2: { instantiate (1 := g). subst g; lia. }
  replace_le (size (enc stepindex)) with g by (subst g; lia) at 1 2 3 4. 
  replace_le (size (enc bpr)) with g by (subst g; lia) at 1 2. 
  replace_le (size (enc startA)) with g by (subst g; lia) at 1. replace_le (size (enc startB)) with g by (subst g; lia) at 1. 
  fold g. 
  unfold poly__encodeCardsInLine'. nia. 
Qed.
Lemma encodeCardsInLineP_poly : monotonic poly__encodeCardsInLine' /\ inOPoly poly__encodeCardsInLine'. 
Proof. 
  unfold poly__encodeCardsInLine'; split; smpl_inO; apply encodeCardsInLineP1_poly. 
Qed. 

Lemma encodeCardsInLineP_varsIn bpr stepi l startA startB : 
  BinaryCC_wellformed bpr
  -> formula_varsIn (fun n => (n >= startA /\ n < startA + l) \/ (n >= startB /\ n < startB + l)) (encodeCardsInLine' bpr stepi l startA startB). 
Proof. 
  intros H0. revert startA startB l. induction stepi; cbn; intros. 
  - destruct width; [ | destruct Nat.ltb]; cbn; intros a H1; inv H1. 
  - destruct width eqn:H1; [destruct H0; lia | ]. 
    destruct Nat.ltb eqn:H2. 
    + apply Nat.leb_le in H2. intros a H. inv H. 
    + apply leb_complete_conv in H2. intros a H. inv H. 
      * apply encodeCardsAt_varsIn in H4; [ | apply H0]. rewrite !H1 in H4. nia. 
      * apply IHstepi in H4. nia.  
Qed. 

(** a more precise bound could be obtained by replacing stepi with div l (offset bpr) *)
Lemma encodeCardsInLineP_size bpr stepi l startA startB : 
  BinaryCC_wellformed bpr -> formula_size (encodeCardsInLine' bpr stepi l startA startB) <= stepi * (|cards bpr| * (6 * width bpr + 4) + 3) + 1.
Proof. 
  intros H0. revert l startA startB. induction stepi; cbn -[Nat.mul Nat.add]; intros. 
  - destruct width; [ | destruct Nat.ltb]; cbn; lia. 
  - destruct width eqn:H1; [ destruct H0; lia | ]. 
    destruct Nat.ltb eqn:H2. 
    + cbn. lia. 
    + apply leb_complete_conv in H2. cbn [formula_size]. rewrite IHstepi. clear IHstepi. 
      rewrite encodeCardsAt_size by apply H0. lia. 
Qed. 

(** encodeCardsInLine *)
Definition c__encodeCardsInLine := 3 * c__init + 3 * c__length + c__add1 + 13.
Definition encodeCardsInLine_time (bpr : BinaryCC) (s : nat) := 
  3 * c__length * (| init bpr |) + add_time s +
  encodeCardsInLineP_time bpr (| init bpr |) (| init bpr |) s (s + (| init bpr |)) + c__encodeCardsInLine.
Instance term_encodeCardsInLine :computableTime' encodeCardsInLine (fun bpr _ => (1, fun s _ => (encodeCardsInLine_time bpr s, tt))). 
Proof. 
  extract. solverec. 
  unfold encodeCardsInLine_time, c__encodeCardsInLine. solverec. 
Qed.

Definition poly__encodeCardsInLine n := 3 * c__length * n + (n + 1) * c__add + poly__encodeCardsInLine' (n * (c__natsizeS + 2) + c__natsizeO) + c__encodeCardsInLine. 
Lemma encodeCardsInLine_time_bound bpr s : 
  BinaryCC_wellformed bpr
  -> encodeCardsInLine_time bpr s <= poly__encodeCardsInLine (size (enc bpr) + size (enc s)). 
Proof. 
  intros H. unfold encodeCardsInLine_time. 
  rewrite encodeCardsInLineP_time_bound by easy.
  poly_mono encodeCardsInLineP_poly. 
  2: { setoid_rewrite size_nat_enc at 3. rewrite list_size_enc_length, list_size_length. 
       rewrite size_nat_enc_r with (n := s) at 2. 
       replace_le (size (enc (init bpr))) with (size (enc bpr)) by (rewrite BinaryCC_enc_size; lia). 
       instantiate (1 := (size (enc bpr) + size (enc s)) * ( c__natsizeS + 2) + c__natsizeO). lia. 
  } 
  rewrite list_size_length. replace_le (size (enc (init bpr))) with (size (enc bpr)) by (rewrite BinaryCC_enc_size; lia). 
  unfold add_time. rewrite size_nat_enc_r with (n := s) at 1. 
  unfold poly__encodeCardsInLine; solverec.  
Qed.
Lemma encodeCardsInLine_poly : monotonic poly__encodeCardsInLine /\ inOPoly poly__encodeCardsInLine. 
Proof. 
  unfold poly__encodeCardsInLine; split; smpl_inO.
  - apply encodeCardsInLineP_poly.
  - apply inOPoly_comp; smpl_inO; apply encodeCardsInLineP_poly. 
Qed. 

Lemma encodeCardsInLine_varsIn bpr s : 
  BinaryCC_wellformed bpr
  -> formula_varsIn (fun n => (n >= s /\ n < s + 2 * (|init bpr|))) (encodeCardsInLine bpr s). 
Proof. 
  intros H. eapply formula_varsIn_monotonic. 
  2: { unfold encodeCardsInLine. apply encodeCardsInLineP_varsIn, H. }
  cbn. intros n. lia. 
Qed. 

Lemma encodeCardsInLine_size bpr s: 
  BinaryCC_wellformed bpr
  -> formula_size (encodeCardsInLine bpr s) <= (|init bpr|) * (|cards bpr| * (6 * width bpr + 4) + 3) +1. 
Proof.  apply encodeCardsInLineP_size.  Qed. 
  
(** encodeCardsInAllLines *)
Definition c__encodeCardsInAllLines := c__init + c__length + c__steps + 5.
Definition encodeCardsInAllLines_time (bpr : BinaryCC) := c__length * (|init bpr|) + tabulate_formula_time 0 (|init bpr|) (steps bpr) (encodeCardsInLine_time bpr) + listAnd_time (tabulate_formula 0 (|init bpr|) (steps bpr) (encodeCardsInLine bpr)) + c__encodeCardsInAllLines.
Instance term_encodeCardsInAllLines : computableTime' encodeCardsInAllLines (fun bpr _ => (encodeCardsInAllLines_time bpr, tt)). 
Proof. 
  extract. solverec. 
  unfold encodeCardsInAllLines_time, c__encodeCardsInAllLines. simp_comp_arith; lia.  
Qed.

Fact nat_size_mul a b: size (enc (a * b)) <= size (enc a) * size (enc b). 
Proof. 
  rewrite !size_nat_enc. unfold c__natsizeS. nia. 
Qed.

Definition poly__encodeCardsInAllLines n := 
  c__length * n + (poly__tabulateStep n + (n * (poly__encodeCardsInLine (n + n * n) + c__map) + c__map)) + c__tabulateFormula + (n + 1) * c__listAnd + c__encodeCardsInAllLines. 
Lemma encodeCardsInAllLines_time_bound bpr : BinaryCC_wellformed bpr -> encodeCardsInAllLines_time bpr <= poly__encodeCardsInAllLines (size (enc bpr)). 
Proof. 
  intros H. unfold encodeCardsInAllLines_time. 
  rewrite list_size_length at 1. replace_le (size (enc (init bpr))) with (size (enc bpr)) by (rewrite BinaryCC_enc_size; lia). 
  unfold tabulate_formula_time. rewrite tabulate_step_time_bound. 
  poly_mono tabulate_step_poly. 2: { rewrite list_size_enc_length. instantiate (1 := size (enc bpr)). rewrite BinaryCC_enc_size; lia. }
  rewrite map_time_mono. 
  2: { intros start Hel. instantiate (1 := fun _ => _). cbn -[Nat.add Nat.mul]. 
       rewrite encodeCardsInLine_time_bound by apply H. 
       apply in_tabulate_step_iff in Hel as (i & H1 & ->). 
       poly_mono encodeCardsInLine_poly. 
       2: { rewrite nat_size_le with (a := 0 + (|init bpr|) * i). 2: { instantiate (1 := (|init bpr|) * steps bpr). nia. }
            rewrite nat_size_mul. rewrite list_size_enc_length. 
            replace_le (size (enc (init bpr))) with (size (enc bpr)) by (rewrite BinaryCC_enc_size; lia). 
            replace_le (size (enc (steps bpr))) with (size (enc bpr)) by (rewrite BinaryCC_enc_size; lia). 
            reflexivity. 
       } 
       reflexivity. 
  } 
  rewrite map_time_const. 
  rewrite tabulate_step_length. 
  unfold listAnd_time, tabulate_formula. rewrite map_length, tabulate_step_length. 
  rewrite size_nat_enc_r with (n := steps bpr) at 1 2. replace_le (size (enc (steps bpr))) with (size (enc bpr)) by (rewrite BinaryCC_enc_size; lia).
  unfold poly__encodeCardsInAllLines. nia.
Qed. 
Lemma encodeCardsInAllLines_poly : monotonic poly__encodeCardsInAllLines /\ inOPoly poly__encodeCardsInAllLines. 
Proof. 
  unfold poly__encodeCardsInAllLines; split; smpl_inO; try apply inOPoly_comp; smpl_inO; first [apply tabulate_step_poly | apply encodeCardsInLine_poly]. 
Qed. 

Lemma encodeCardsInAllLines_varsIn bpr :
  BinaryCC_wellformed bpr 
  -> formula_varsIn (fun n => n < (1 + steps bpr) * (|init bpr|)) (encodeCardsInAllLines bpr). 
Proof. 
  intros H. unfold encodeCardsInAllLines. apply listAnd_varsIn. 
  intros f H1. destruct steps; [now cbn in H1 | ]. 
  eapply tabulate_formula_varsIn in H1. 
  2: { intros s. eapply formula_varsIn_monotonic. 2: apply encodeCardsInLine_varsIn, H. 
       intros n'. cbn. intros [_ H2]. apply H2.
  } 
  2: smpl_inO. 
  cbn in H1. eapply formula_varsIn_monotonic. 2 : apply H1. intros n'. cbn. 
  nia. 
Qed. 

Lemma encodeCardsInAllLines_size bpr : 
  BinaryCC_wellformed bpr
  -> formula_size (encodeCardsInAllLines bpr) <= ((steps bpr) * ((|init bpr|) * (|cards bpr| * (6 * width bpr + 4) + 3) +2)) + 1.
Proof. 
  intros H. unfold encodeCardsInAllLines. rewrite listAnd_size. 
  rewrite tabulate_formula_length. 
  rewrite sumn_map_mono. 2: { intros f H1. unfold tabulate_formula in H1. apply in_map_iff in H1 as (i & <- & H1). 
    instantiate (1 := fun _ => _). cbn. rewrite encodeCardsInLine_size by apply H. reflexivity. 
  } 
  rewrite sumn_map_const, tabulate_formula_length. nia. 
Qed. 

(** encodeSubstringInLine' *)
Definition c__encodeSubstringInLine' := c__length +  23 + c__sub1 + 2 * c__offset.
Fixpoint encodeSubstringInLineP_time (bpr : BinaryCC) (s : list bool) (stepindex l start : nat) := 
 match stepindex with 
  | 0 => 0 
  | S stepi => encodeListAt_time s +  sub_time l (offset bpr) + c__add1 + add_time start + encodeSubstringInLineP_time bpr s stepi (l - offset bpr) (start + offset bpr)
 end + c__length * (|s|) + ltb_time l (|s|) + c__encodeSubstringInLine'. 
Instance term_encodeSubstringInLine' : computableTime' encodeSubstringInLine' (fun bpr _ => (1, fun s _ => (5, fun stepi _ => (1, fun l _ => (1, fun start _ => (encodeSubstringInLineP_time bpr s stepi l start, tt)))))). 
Proof. 
  extract. solverec. 
  all: unfold encodeSubstringInLineP_time, c__encodeSubstringInLine'. all: solverec. 
Qed.

Definition poly__encodeSubstringInLineP1 n := poly__encodeListAt n + (n + 1) * c__sub + c__add1 + c__length * n + (c__leb * (1 + n) + c__ltb) + c__encodeSubstringInLine'.
Lemma encodeSubstringInLineP_time_bound1 bpr s stepindex l start : 
  BinaryCC_wellformed bpr 
  -> encodeSubstringInLineP_time bpr s stepindex l start <= (stepindex + 1) * poly__encodeSubstringInLineP1 (size (enc bpr) + size (enc s)) + stepindex * (stepindex * (offset bpr) + start + 1) * c__add.
Proof. 
  intros H.
  revert l start. unfold encodeSubstringInLineP_time. induction stepindex; intros.
  - unfold ltb_time, leb_time. rewrite Nat.le_min_r. 
    rewrite list_size_length. 
    unfold poly__encodeSubstringInLineP1. nia. 
  - rewrite IHstepindex. clear IHstepindex. 
    rewrite encodeListAt_time_bound. 
    unfold sub_time. rewrite Nat.le_min_r. 
    unfold ltb_time, leb_time. rewrite Nat.le_min_r. 
    rewrite list_size_length. 
    rewrite size_nat_enc_r with (n := offset bpr) at 1. 
    replace_le (size (enc (offset bpr))) with (size (enc bpr)) by (rewrite BinaryCC_enc_size; cbn; lia). 
    poly_mono encodeListAt_poly. 2: { instantiate (1 := size (enc bpr) + size (enc s)). lia. }
    unfold poly__encodeSubstringInLineP1. unfold add_time. nia.  
Qed.
Lemma encodeSubstringInLineP_poly1 : monotonic poly__encodeSubstringInLineP1 /\ inOPoly poly__encodeSubstringInLineP1. 
Proof. 
  unfold poly__encodeSubstringInLineP1; split; smpl_inO; apply encodeListAt_poly. 
Qed.

Definition poly__encodeSubstringInLine' n := (n + 1) * poly__encodeSubstringInLineP1 n + n * (n * n + n + 1) * c__add. 
Lemma encodeSubstringInLineP_time_bound bpr s stepindex l start : 
  BinaryCC_wellformed bpr -> encodeSubstringInLineP_time bpr s stepindex l start <= poly__encodeSubstringInLine' (size (enc bpr) + size (enc s) + size (enc stepindex) + size (enc start)). 
Proof. 
  intros H. rewrite encodeSubstringInLineP_time_bound1 by apply H. 
  pose (g := size (enc bpr) + size (enc s) + size (enc stepindex) + size (enc start)).
  poly_mono encodeSubstringInLineP_poly1. 2 : { instantiate (1 := g). subst g; lia. }
  rewrite size_nat_enc_r with (n := stepindex) at 1 2 3. 
  rewrite size_nat_enc_r with (n := offset bpr). replace_le (size (enc (offset bpr))) with (size (enc bpr)) by (rewrite BinaryCC_enc_size; lia). 
  rewrite size_nat_enc_r with (n := start) at 1. 
  replace_le (size (enc stepindex)) with g by (unfold g; lia) at 1 2 3.  
  replace_le (size (enc bpr)) with g by (unfold g; lia) at 1. 
  replace_le (size (enc start)) with g by (unfold g; lia) at 1. 
  fold g.  unfold poly__encodeSubstringInLine'.  nia.  
Qed.
Lemma encodeSubstringInLineP_poly : monotonic poly__encodeSubstringInLine' /\ inOPoly poly__encodeSubstringInLine'. 
Proof. 
  unfold poly__encodeSubstringInLine'; split; smpl_inO; apply encodeSubstringInLineP_poly1. 
Qed.

Lemma encodeSubstringInLineP_varsIn bpr s stepindex l start: formula_varsIn (fun n => n >= start /\ n < start + l) (encodeSubstringInLine' bpr s stepindex l start). 
Proof. 
  revert l start. induction stepindex; cbn; intros. 
  - destruct s; cbn.
    + intros a H. inv H. 
    + destruct leb; intros a H; varsIn_inv. 
  - destruct s; cbn. 
    + intros a H1. inv H1; [varsIn_inv | ]. 
      apply IHstepindex in H0. lia. 
    + destruct leb eqn:H2; [intros a H; varsIn_inv | ]. 
      apply leb_complete_conv in H2. 
      intros a H. inv H. 
      * apply (@encodeListAt_varsIn start (b :: s)) in H1. cbn in H1. nia. 
      * apply IHstepindex in H1. nia. 
Qed. 

Lemma encodeSubstringInLineP_size bpr s stepindex l start : formula_size (encodeSubstringInLine' bpr s stepindex l start) <= stepindex * (3 * |s| + 1) + 2. 
Proof. 
  revert l start. induction stepindex; cbn; intros. 
  - destruct s; cbn; [lia | ]. destruct leb; cbn; lia. 
  - destruct s; cbn. 
    + rewrite IHstepindex. cbn. nia. 
    + destruct leb eqn:H1; cbn -[Nat.add Nat.mul]; [lia | ]. rewrite IHstepindex. 
      rewrite encodeListAt_size, encodeLiteral_size. cbn. nia. 
Qed. 

(** encodeSubstringInLine *)
Definition c__encodeSubstringInLine := 14. 
Definition encodeSubstringInLine_time (bpr : BinaryCC) (s : list bool) (start l : nat) := encodeSubstringInLineP_time bpr s l l start + c__encodeSubstringInLine. 
Instance term_encodeSubstringInLine : computableTime' encodeSubstringInLine (fun bpr _ => (1, fun s _ => (1, fun start _ => (1, fun l _ => (encodeSubstringInLine_time bpr s start l, tt))))). 
Proof. 
  extract. solverec. all: unfold encodeSubstringInLine_time, c__encodeSubstringInLine; solverec. 
Qed.

Lemma encodeSubstringInLine_varsIn bpr s start l: formula_varsIn (fun n => n >= start /\ n < start + l) (encodeSubstringInLine bpr s start l).
Proof. 
  unfold encodeSubstringInLine. destruct s. 
  - intros a H. inv H. 
  - apply encodeSubstringInLineP_varsIn. 
Qed. 

Lemma encodeSubstringInLine_size bpr s start l : formula_size (encodeSubstringInLine bpr s start l) <= l * (3 * |s| + 1) + 2.
Proof. 
  unfold encodeSubstringInLine. destruct s. 
  - cbn. lia. 
  - apply encodeSubstringInLineP_size. 
Qed. 

(** encodeFinalConstraint *)
Definition encodeFinalConstraint_step (bpr : BinaryCC) (start : nat) (s : list bool) := encodeSubstringInLine bpr s start (|init bpr|). 

Definition c__encodeFinalConstraintStep := c__init + c__length + 4.
Definition encodeFinalConstraint_step_time (bpr : BinaryCC) (start : nat) (s : list bool) := c__length * (|init bpr|) + encodeSubstringInLine_time bpr s start (|init bpr|) + c__encodeFinalConstraintStep.
Instance term_encodeFinalConstraint_step : computableTime' encodeFinalConstraint_step (fun bpr _ => (1, fun start _ => (1, fun s _ => (encodeFinalConstraint_step_time bpr start s, tt)))). 
Proof. 
  extract. solverec. 
  unfold encodeFinalConstraint_step_time, c__encodeFinalConstraintStep; solverec.   
Qed. 

Definition c__encodeFinalConstraint := c__final + 4. 
Definition encodeFinalConstraint_time (bpr : BinaryCC) (start : nat) :=  map_time (encodeFinalConstraint_step_time bpr start) (final bpr) + listOr_time (map (encodeFinalConstraint_step bpr start) (final bpr)) + c__encodeFinalConstraint.
Instance term_encodeFinalConstraint : computableTime' encodeFinalConstraint (fun bpr _ => (1, fun start _ => (encodeFinalConstraint_time bpr start, tt))). 
Proof. 
  apply computableTimeExt with (x := fun bpr start => listOr (map (encodeFinalConstraint_step bpr start) (final bpr))). 
  1: easy.
  extract. solverec. 
  unfold encodeFinalConstraint_time, c__encodeFinalConstraint; simp_comp_arith; solverec. 
Qed.

Definition poly__encodeFinalConstraint n := n * (c__length * n + poly__encodeSubstringInLine' (2 * n) + c__encodeSubstringInLine + c__encodeFinalConstraintStep + c__map) + c__map + (n + 1) * c__listOr + c__encodeFinalConstraint. 
Lemma encodeFinalConstraint_time_bound bpr start : 
  BinaryCC_wellformed bpr 
  -> encodeFinalConstraint_time bpr start <= poly__encodeFinalConstraint (size (enc bpr) + size (enc start)). 
Proof. 
  intros H. unfold encodeFinalConstraint_time. 
  rewrite map_time_mono. 
  2: { intros l Hel. unfold encodeFinalConstraint_step_time, encodeSubstringInLine_time.  
       instantiate (1 := fun _ => _). cbn -[Nat.mul Nat.add]. 
       rewrite encodeSubstringInLineP_time_bound by apply H.
       rewrite list_size_length at 1. replace_le (size (enc (init bpr))) with (size (enc bpr)) by (rewrite BinaryCC_enc_size; lia). 
       poly_mono encodeSubstringInLineP_poly. 
       2: { instantiate (1 := 2 * (size (enc bpr) + size (enc start))). 
            rewrite (list_el_size_bound Hel), list_size_enc_length. 
            cbn. rewrite BinaryCC_enc_size at 2. lia. 
       } 
       reflexivity. 
  }
  rewrite map_time_const, list_size_length. unfold listOr_time. rewrite map_length, list_size_length. 
  replace_le (size (enc (final bpr))) with (size (enc bpr)) by (rewrite BinaryCC_enc_size; lia).
  unfold poly__encodeFinalConstraint; nia.  
Qed. 
Lemma encodeFinalConstraint_poly : monotonic poly__encodeFinalConstraint /\ inOPoly poly__encodeFinalConstraint. 
Proof. 
  unfold poly__encodeFinalConstraint; split; smpl_inO. 
  - apply encodeSubstringInLineP_poly. 
  - apply inOPoly_comp; smpl_inO; apply encodeSubstringInLineP_poly. 
Qed. 

Lemma encodeFinalConstraint_varsIn bpr start : formula_varsIn (fun n => n >= start /\ n < start + (|init bpr|)) (encodeFinalConstraint bpr start).
Proof. 
  unfold encodeFinalConstraint. apply listOr_varsIn. 
  intros f (s & <- & Hel)%in_map_iff. apply encodeSubstringInLine_varsIn. 
Qed. 

Lemma encodeFinalConstraint_size bpr start : 
  formula_size (encodeFinalConstraint bpr start)<= sumn (map (fun s => ((|init bpr|) * (3 * |s| + 1) + 2)) (final bpr)) + (|final bpr|) + 2.
Proof. 
  unfold encodeFinalConstraint. rewrite listOr_size. 
  rewrite map_map, sumn_map_mono. 
  2: { intros x _. instantiate (1 := fun x => _ ). cbn. rewrite encodeSubstringInLine_size. reflexivity. }
  rewrite map_length. lia. 
Qed. 

(**encodeTableau *)
Definition c__encodeTableau := 2 * c__init + c__steps + c__mult1 + c__length + 11.
Definition encodeTableau_time (bpr : BinaryCC) := encodeListAt_time (init bpr) + encodeCardsInAllLines_time bpr + c__length * (|init bpr|) + mult_time (steps bpr) (|init bpr|) + encodeFinalConstraint_time bpr (steps bpr * (|init bpr|)) + c__encodeTableau. 
Instance term_encodeTableau : computableTime' encodeTableau (fun bpr _ => (encodeTableau_time bpr, tt)). 
Proof. 
  unfold encodeTableau, encodeFinalConstraint'. extract. solverec. 
  unfold encodeTableau_time, c__encodeTableau. solverec. 
Qed. 

Definition poly__encodeTableau n := poly__encodeListAt n + poly__encodeCardsInAllLines n + c__length * n + (n * n * c__mult + c__mult * (n + 1)) + poly__encodeFinalConstraint (n + n * n) + c__encodeTableau.
Lemma encodeTableau_time_bound bpr : BinaryCC_wellformed bpr -> encodeTableau_time bpr <= poly__encodeTableau (size (enc bpr)). 
Proof. 
  intros H. unfold encodeTableau_time. 
  rewrite encodeListAt_time_bound. poly_mono encodeListAt_poly. 2: { instantiate (1:= size (enc bpr)). rewrite BinaryCC_enc_size; lia. }
  rewrite encodeCardsInAllLines_time_bound by apply H.     
  rewrite encodeFinalConstraint_time_bound by apply H. 
  poly_mono encodeFinalConstraint_poly. 
  2: { rewrite nat_size_mul. rewrite list_size_enc_length. 
       replace_le (size (enc (steps bpr))) with (size (enc bpr)) by (rewrite BinaryCC_enc_size; lia). 
       replace_le (size (enc (init bpr))) with (size (enc bpr)) by (rewrite BinaryCC_enc_size; lia). 
       reflexivity. 
  } 
  unfold mult_time. rewrite list_size_length at 1 2. rewrite size_nat_enc_r with (n := steps bpr). 
  replace_le (size (enc (init bpr))) with (size (enc bpr)) by (rewrite BinaryCC_enc_size; lia) at 1 2. 
  replace_le (size (enc (steps bpr))) with (size (enc bpr)) by (rewrite BinaryCC_enc_size; lia) at 1 2.
  unfold poly__encodeTableau; nia. 
Qed.
Lemma encodeTableau_poly : monotonic poly__encodeTableau /\ inOPoly poly__encodeTableau. 
Proof. 
  unfold poly__encodeTableau; split; smpl_inO; try apply inOPoly_comp; smpl_inO; first [apply encodeListAt_poly | apply encodeCardsInAllLines_poly | apply encodeFinalConstraint_poly]. 
Qed. 

Lemma encodeTableau_varsIn bpr: BinaryCC_wellformed bpr -> formula_varsIn (fun n => n < (1 + steps bpr) * (|init bpr|)) (encodeTableau bpr). 
Proof. 
  intros H. 
  unfold encodeCardsInAllLines. intros a H1. inv H1. 
  - inv H2. 
    + apply encodeListAt_varsIn in H1. nia. 
    + apply encodeCardsInAllLines_varsIn in H1; [ | apply H]. nia. 
  - unfold encodeFinalConstraint' in H2. apply encodeFinalConstraint_varsIn in H2. nia. 
Qed. 

Lemma encodeTableau_size : {f : nat -> nat & (forall bpr, BinaryCC_wellformed bpr -> formula_size (encodeTableau bpr) <= f (size (enc bpr))) /\ monotonic f /\ inOPoly f}. 
Proof. 
  eexists. split; [ | split]. 
  - intros bpr H. unfold encodeTableau. cbn. 
    rewrite encodeListAt_size. rewrite encodeCardsInAllLines_size by apply H. 
    unfold encodeFinalConstraint'. rewrite encodeFinalConstraint_size. 
    rewrite !list_size_length. rewrite sumn_map_mono. 
    2: { intros s Hel. instantiate (1 := fun _ => _). cbn -[Nat.mul Nat.add]. 
         rewrite list_size_length with (l := s). rewrite list_size_length. 
         replace_le (size (enc (init bpr))) with (size (enc bpr)) by (rewrite BinaryCC_enc_size; lia). 
         erewrite list_el_size_bound with (a := s) by apply Hel.
         replace_le (size (enc (final bpr))) with (size (enc bpr)) by (rewrite BinaryCC_enc_size; lia). 
         reflexivity. 
    } 
    rewrite sumn_map_const. rewrite list_size_length. 
    replace_le (size (enc (init bpr))) with (size (enc bpr)) by (rewrite BinaryCC_enc_size; lia). 
    replace_le (size (enc (final bpr))) with (size (enc bpr)) by (rewrite BinaryCC_enc_size; lia).
    replace_le (size (enc (cards bpr))) with (size (enc bpr)) by (rewrite BinaryCC_enc_size; lia).
    rewrite size_nat_enc_r with (n := width bpr). 
    replace_le (size (enc (width bpr))) with (size (enc bpr)) by (rewrite BinaryCC_enc_size; lia).
    rewrite size_nat_enc_r with (n := steps bpr). 
    replace_le (size (enc (steps bpr))) with (size (enc bpr)) by (rewrite BinaryCC_enc_size; lia).
    instantiate (1 := fun n => _). cbn -[Nat.add Nat.mul]. generalize (size (enc bpr)). reflexivity. 
  - smpl_inO. 
  - smpl_inO. 
Defined. 

Lemma encodeTableau_enc_size : {f : nat -> nat & (forall bpr, BinaryCC_wellformed bpr -> size (enc (encodeTableau bpr)) <= f (size (enc bpr))) /\ inOPoly f /\ monotonic f}.
Proof. 
  destruct encodeTableau_size as (f' & H1 & H2 & H3). 
  eexists. split; [ | split]. 
  - intros bpr H. rewrite formula_enc_size_bound. 
        rewrite H1 by apply H. erewrite formula_varsIn_bound. 
    2: { eapply formula_varsIn_monotonic. 2: apply encodeTableau_varsIn, H. intros n. cbn. apply Nat.lt_le_incl. }
    instantiate (1 := fun n => _). cbn -[Nat.add Nat.mul]. 
    rewrite list_size_length. replace_le (size (enc (init bpr))) with (size (enc bpr)) by (rewrite BinaryCC_enc_size; lia). 
    rewrite size_nat_enc_r with (n := steps bpr). replace_le (size (enc (steps bpr))) with (size (enc bpr)) by (rewrite BinaryCC_enc_size; lia).
    generalize (size (enc bpr)). reflexivity. 
  - smpl_inO. 
  - smpl_inO. 
Qed. 

(** BinaryCC_wf_dec *)

Definition c__BinaryCCWfDec := 3 * c__leb2 + 4 * c__width + 3 * c__offset + 2 * 5 + 2 * c__init + 2 * c__length + c__cards + 32 + 4 * c__leb + 2 * c__eqbComp nat * size (enc 0).
Definition BinaryCC_wf_dec_time x := 2 * c__length * (|init x|) + leb_time (width x) (|init x|) + forallb_time (@FlatCC.CCCard_of_size_dec_time bool (width x)) (cards x) + modulo_time (|init x|) (offset x) + modulo_time (width x) (offset x) + c__BinaryCCWfDec.  
Instance term_BinaryCC_wf_dec : computableTime' BinaryCC_wf_dec (fun bpr _ => (BinaryCC_wf_dec_time bpr, tt)). 
Proof. 
  extract. solverec. 
  unfold BinaryCC_wf_dec_time, c__BinaryCCWfDec, leb_time. rewrite !eqbTime_le_r. 
  do 2 rewrite Nat.le_min_l. simp_comp_arith. leq_crossout. 
Qed. 

Definition c__BinaryCCWfDecBound := 2*(2 * c__length + c__leb + FlatCC.c__prcardOfSizeDecBound + c__forallb + 2 * c__moduloBound + c__BinaryCCWfDec).
Definition poly__BinaryCCWfDec n := (n*n + 2* n + 1) * c__BinaryCCWfDecBound.
Lemma BinaryCC_wf_dec_time_bound fpr : 
  BinaryCC_wf_dec_time fpr <= poly__BinaryCCWfDec (size (enc fpr)). 
Proof. 
  unfold BinaryCC_wf_dec_time. rewrite leb_time_bound_l. 
  rewrite !modulo_time_bound. rewrite list_size_enc_length.
  rewrite list_size_length.
  erewrite forallb_time_bound_env.
  2: {
    split; [intros | ].
    - specialize (FlatCC.CCCard_of_size_dec_time_bound (X := bool) y a) as H1.
      instantiate (2:= fun n => (n + 1) * FlatCC.c__prcardOfSizeDecBound). simp_comp_arith; nia. 
    - smpl_inO. 
  }
  rewrite list_size_length. 
  replace_le (size(enc (cards fpr))) with (size (enc fpr)) by (rewrite BinaryCC_enc_size; lia). 
  replace_le (size(enc (init fpr))) with (size (enc fpr)) by (rewrite BinaryCC_enc_size; lia). 
  replace_le (size(enc (width fpr))) with (size (enc fpr)) by (rewrite BinaryCC_enc_size; lia). 
  replace_le (size(enc(offset fpr))) with (size (enc fpr)) by (rewrite BinaryCC_enc_size; lia). 
  unfold poly__BinaryCCWfDec, c__BinaryCCWfDecBound. nia.
Qed. 
Lemma BinaryCC_wf_dec_poly : monotonic poly__BinaryCCWfDec /\ inOPoly poly__BinaryCCWfDec.
Proof. 
  unfold poly__BinaryCCWfDec; split; smpl_inO. 
Qed. 

(** reduction *)
Definition c__reduction := 4. 
Definition reduction_time (bpr : BinaryCC) := (if BinaryCC_wf_dec bpr then  encodeTableau_time bpr else 0) +BinaryCC_wf_dec_time bpr + c__reduction. 
Instance term_reduction : computableTime' reduction (fun bpr _ => (reduction_time bpr, tt)). 
Proof. 
  extract. unfold reduction_time, c__reduction; solverec. 
Qed. 

(** full reduction statement *)
Theorem BinaryCC_to_FSAT_poly : (unrestrictedP BinaryCCLang) ⪯p (unrestrictedP FSAT). 
Proof. 
  eapply reducesPolyMO_intro_unrestricted with (f := reduction). 
  - exists (fun n => poly__encodeTableau n + poly__BinaryCCWfDec n + c__reduction). 
    + eexists. 
      eapply computesTime_timeLeq. 2: { apply term_reduction. }
      intros bpr _. cbn -[Nat.add Nat.mul]. split; [ | easy]. 
      unfold reduction_time. destruct BinaryCC_wf_dec eqn:H1. 
      * apply BinaryCC_wf_dec_correct in H1. rewrite encodeTableau_time_bound, BinaryCC_wf_dec_time_bound by easy. 
        generalize (size (enc bpr)). reflexivity. 
      * rewrite BinaryCC_wf_dec_time_bound. lia. 
    + smpl_inO; first [apply encodeTableau_poly | apply BinaryCC_wf_dec_poly]. 
    + smpl_inO; first [apply encodeTableau_poly | apply BinaryCC_wf_dec_poly]. 
    + destruct encodeTableau_enc_size as (f & H1 & H2 & H3). 
      exists (fun n => f n + size (enc trivialNoInstance)). 
      * intros bpr. unfold reduction. destruct BinaryCC_wf_dec eqn:H4. 
        -- apply BinaryCC_wf_dec_correct in H4. rewrite H1 by apply H4. lia. 
        -- lia. 
      * smpl_inO. 
      * smpl_inO. 
  - apply BinaryCC_to_FSAT. 
Qed. 
