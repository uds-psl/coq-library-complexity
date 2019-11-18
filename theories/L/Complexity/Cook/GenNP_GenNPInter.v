(* -*- company-coq-local-symbols: (("|_|" .?␣)); -*- *)
From Undecidability.L.Complexity Require Import Cook.GenNP Cook.TCSR Cook.Prelim.
From PslBase Require Import FiniteTypes. 
From Undecidability.TM Require Import TM.
Require Import Lia. 


(*TODO: too many dependent pairs because of alphabet and states.. *)
(* Definition GenNP_Intermediate : {Sigma : finType & {Gamma' : finType & nat * list (TCSRWin Sigma) * list (list (Sigma + Gamma')) *  *)


Definition makeExhaustive (t : finType) (X : Type) (f : t -> list X) := concat (map (fun e => f e) (@FinTypes.enum t _)).  

Lemma makeExhaustive_correct (t : finType) (X : Type) (f : t -> list X) :
  forall e, e el (makeExhaustive f) <-> (exists (a : t), e el f a). 
Proof.
  intros.
  unfold makeExhaustive. rewrite in_concat_iff. 
  split.
  - intros (l' & H1 & H2). rewrite in_map_iff in H2. destruct H2 as (a & H3 & H4). exists a. now rewrite <- H3 in *. 
  - intros (a & H1). exists (f a). split; [assumption | ]. rewrite in_map_iff. exists a. split; [reflexivity | ]. 
    eapply countIn. rewrite enum_ok. lia. 
Qed. 

Section fixTM.
  Variable (states : finType).
  Variable (Sigma : finType).
  Variable (trans : (states * option Sigma) -> (states * (option Sigma * move))). 
  Variable (halt : states -> bool). 

  Definition sconfig := (states * tape Sigma)%type. (* single-tape configuration*)
  Implicit Type (c : sconfig). 

  Variables (t k : nat).
  Definition z' := t + k. (*effectively available space on each tape side *)
  Definition z := z' + 3. (*length of each tape side *)
  Definition l := 2 * z + 1. (*length of the whole string: two tape sides and the state symbol*)

  Hint Unfold z z' l. 

  Inductive polarity := positive | negative | neutral. 

  Instance polarity_eqTypeC : eq_dec polarity. 
  Proof. 
    unfold dec. decide equality. 
  Qed. 

  Lemma polarity_Enum_Ok x : BasicDefinitions.count [positive; negative; neutral] x = 1. 
  Proof. 
    simpl; dec; destruct x; congruence. 
  Qed. 

  Instance polarity_finTypeC : finTypeC (EqType polarity). 
  Proof. 
    econstructor. apply polarity_Enum_Ok. 
  Defined. 

  Implicit Type σ : Sigma. 

  Notation "'↓' σ" := ((negative, σ)) (at level 30). 
  Notation "'↑' σ" := ((positive, σ)) (at level 30).
  Notation "'∘' σ" := ((neutral, σ)) (at level 30). 

  Definition polSigma := FinType (EqType (polarity * Sigma)%type). 
  Definition tapeSigma := FinType (EqType (option polSigma)). 

  Definition stateSigma := FinType (EqType (option Sigma)). 

  Definition States := FinType (EqType ((states * stateSigma)%type)). 

  Definition Gamma := FinType (EqType ((States + tapeSigma)%type)). 

  Implicit Type (q : states).
  Implicit Type (m : tapeSigma).
  Implicit Type (p : polarity).

  (* Definition inra := @inr States tapeSigma.  *)
  (* Coercion inra : tapeSigma >-> Gamma.  *)

  Notation "'|_|'" := (None) (only parsing). 

  (*move tape element from state to tape cell, adding a polarity*)
  Definition withPolaritySigma p σ : tapeSigma := Some (p, σ). 
  Definition withPolarity p (σ: stateSigma) : tapeSigma := match σ with |_| => |_| | Some σ => withPolaritySigma p σ end. 

  (*move from tape cell to state cell *)
  Definition removePolarity (σ : tapeSigma) : stateSigma := match σ with |_| => |_| | Some (p, σ) => Some σ end.

  Notation "p ! a" := (withPolarity p a) (at level 40). 

  (* Definition makeRulesPol (a b c : stateSigma) (d e f : Gamma) := *)
  (*   [  { inr (negative ! a), inr (negative ! a), inr (negative ! c)} *)
  (*    / { }] *)

  (*flip the polarity of a symbol *)
  Definition polarityFlipSigma (x : polSigma) := match x with ↓ σ => ↑ σ
                                                    | ↑ σ => ↓ σ
                                                    | ∘ σ => ∘ σ
                                             end.
  Definition polarityFlipTapeSigma (x : tapeSigma) : tapeSigma := match x with |_| => |_| | Some σ => Some (polarityFlipSigma σ) end. 
  Definition polarityFlipGamma (x : Gamma) : Gamma := match x with inl s => inl s | inr x => inr (polarityFlipTapeSigma x) end.

  (*reverse a string + flip its polarities *)
  Fixpoint polarityRev (x : list Gamma) : list Gamma := match x with [] => []
                                                                | (x :: xr) => polarityRev xr ++ [polarityFlipGamma x]
                                                         end. 

  (*the same for rewrite windows *)
  Definition polarityRevTCSRWinP (x : TCSRWinP Gamma) : TCSRWinP Gamma :=
    match x with winp σ1 σ2 σ3 => winp (polarityFlipGamma σ3) (polarityFlipGamma σ2) (polarityFlipGamma σ1) end. 
  Definition polarityRevWin (x : TCSRWin Gamma) : TCSRWin Gamma := {| prem := polarityRevTCSRWinP (prem x); conc := polarityRevTCSRWinP (conc x)|}. 

  (*a rule template which instantiates the symbols with the three possible consistent polarities*)
  Definition makeRulesPol (a b c : stateSigma ) (d e f : Gamma): list (TCSRWin Gamma) :=
    [  {     inr (negative ! a) , inr(negative ! b), inr (negative ! c) }
         / { d,  e, f };
       {     inr (neutral ! a), inr (neutral ! b), inr (neutral ! c) }
         / { d, e, f};
       {     inr (positive ! a), inr (positive ! b), inr (positive ! c) }
         / { d, e, f}
    ].

  (** *Identity rules*)
  Definition makeIdentityRulesTemplate (x : stateSigma * stateSigma * stateSigma) : list (TCSRWin Gamma) :=
    match x with (a, b, c) => makeRulesPol a b c (inr (neutral ! a)) (inr (neutral ! b)) (inr (neutral ! c)) end. 

  (*rules that apply to both halves of the tape *)
  Definition makeIdentityRulesBlankBlankBlank := makeIdentityRulesTemplate (|_| , |_| , |_| ). 
  Definition makeIdentityRulesSigSigSig (x : Sigma * Sigma * Sigma) :=
    match x with (σ1, σ2, σ3) => makeIdentityRulesTemplate (Some σ1, Some σ2, Some σ3) end.

  (*templates for rules that apply to right half of tape *)
  Definition makeIdentityRulesSigBlankBlank σ := makeIdentityRulesTemplate (Some σ , |_| , |_|). 
  Definition makeIdentityRulesSigSigBlank (x : Sigma * Sigma) :=
    match x with (σ1, σ2) => makeIdentityRulesTemplate (Some σ1, Some σ2, |_|) end.

  Definition makeIdentityBoth := makeIdentityRulesBlankBlankBlank ++ makeExhaustive makeIdentityRulesSigSigSig.
  Definition makeIdentityRight := makeExhaustive makeIdentityRulesSigBlankBlank++ makeExhaustive makeIdentityRulesSigSigBlank. 
  Definition makeIdentityLeft := map polarityRevWin makeIdentityRight.  (*the left rules are symmetric to the right rules *)

  Definition makeIdentity := makeIdentityLeft ++ makeIdentityBoth ++ makeIdentityRight. 
  (* Lemma makeIdentityRules_correct : forall a, a el makeIdentityRules <-> (exists (x y z : stateSigma), a el makeIdentityRules' (x, y, z)).  *)
  (* Proof.  *)
  (*   unfold makeIdentityRules. intros. rewrite makeExhaustive_correct. split. *)
  (*   - intros ([[x y] z] & H). eauto.   *)
  (*   - intros (x & y & z & H). eauto.  *)
  (* Qed.  *)


  (** *shift right rules*)
  (*of the form {a, b, c} / {↑ d, ↑ a, ↑ b} *)
  Definition makeShiftRightRulesTemplate (x : stateSigma * stateSigma * stateSigma * stateSigma) :=
    match x with (((a, b), c), d) => makeRulesPol a b c (inr (positive ! d)) (inr (positive ! a)) (inr (positive ! b)) end. 

  (* both halves*)
  Definition makeShiftRightRulesSigSigSig1 (x : Sigma * Sigma * Sigma * Sigma) :=
    match x with (σ1, σ2, σ3, σ4) => makeShiftRightRulesTemplate (Some σ1, Some σ2, Some σ3, Some σ4) end. 


  (* right half*)
  Definition makeShiftRightRulesBlankBlankBlank (σ : Sigma) := makeShiftRightRulesTemplate (|_| , |_| , |_| , Some σ).
  Definition makeShiftRightRulesSigBlankBlank (x : Sigma * Sigma) :=
    match x with (σ1, σ2) => makeShiftRightRulesTemplate (Some σ1, |_| , |_| , Some σ2) end.
  Definition makeShiftRightRulesSigSigBlank (x : Sigma * Sigma * Sigma) :=
    match x with (σ1, σ2, σ3) => makeShiftRightRulesTemplate (Some σ1, Some σ2, |_| , Some σ3) end. 

  (*left half*)
  Definition makeShiftRightRulesBlankBlankSig (σ : Sigma) := makeShiftRightRulesTemplate (|_| , |_| , Some σ , |_| ).
  Definition makeShiftRightRulesBlankSigSig (x : Sigma * Sigma) :=
    match x with (σ1, σ2) => makeShiftRightRulesTemplate (|_| , Some σ1, Some σ2, |_|) end.
  Definition makeShiftRightRulesSigSigSig2 (x : Sigma * Sigma * Sigma) :=
    match x with (σ1, σ2, σ3) => makeShiftRightRulesTemplate (Some σ1, Some σ2, Some σ3, |_|) end. 

  Definition makeShiftRightBoth := makeExhaustive makeShiftRightRulesSigSigSig1. 
  Definition makeShiftRightRight := makeExhaustive makeShiftRightRulesBlankBlankBlank ++ makeExhaustive makeShiftRightRulesSigBlankBlank ++ makeExhaustive makeShiftRightRulesSigSigBlank. 
  Definition makeShiftRightLeft := makeExhaustive makeShiftRightRulesBlankBlankSig ++ makeExhaustive makeShiftRightRulesBlankSigSig ++ makeExhaustive makeShiftRightRulesSigSigSig2. 

  Definition makeShiftRight := makeShiftRightBoth ++ makeShiftRightRight ++ makeShiftRightLeft. 
                
  (** *shift left rules *) 
  (*these can be derived from the rules for shifting right due to symmetry *)
  Definition makeShiftLeft := map polarityRevWin makeShiftRight. 

  Definition makeTapeRules := makeIdentity ++ makeShiftRight ++ makeShiftLeft. 

  Lemma polarityRevWinP_involutive a : a = polarityRevTCSRWinP (polarityRevTCSRWinP a). 
  Proof. 
    unfold polarityRevTCSRWinP. destruct a. cbn.
    repeat (try destruct e; try destruct e0; try destruct e1; try destruct p; try destruct p0; try destruct p1); cbn; try reflexivity.
  Qed. 

  Lemma polarityRevWin_involutive rule : rule = polarityRevWin (polarityRevWin rule). 
  Proof. unfold polarityRevWin. cbn. destruct rule. cbn. now repeat rewrite <- polarityRevWinP_involutive. Qed. 
  
  Lemma tape_rules_identity_revp rule : rule el makeIdentity -> polarityRevWin rule el makeIdentity. 
  Proof.
    unfold makeIdentity. repeat rewrite in_app_iff. intros [H | [H | H]]. 
    - right; right. unfold makeIdentityLeft in H. apply in_map_iff in H as (x & H1 & H2).
      now rewrite <- H1, <- polarityRevWin_involutive.
    - right; left. unfold makeIdentityBoth in *. rewrite in_app_iff in *. destruct H as [H | H].
      * left. unfold makeIdentityRulesBlankBlankBlank, makeIdentityRulesTemplate, makeRulesPol in *. 
        cbn in H. destruct H as [H | [H | [H | H]]]; try rewrite <- H; cbn; now left. 
      * right. unfold makeIdentityRulesSigSigSig, makeIdentityRulesTemplate, makeRulesPol in *. 
        cbn in H. 
  Admitted. 

  Lemma tape_rules_revp' rule : rule el makeTapeRules -> polarityRevWin rule el makeTapeRules.
  Proof. 
    unfold makeTapeRules. repeat rewrite in_app_iff. intros [H | [H | H]]. 
    - left. now apply tape_rules_identity_revp. 
    - right; right. unfold makeShiftLeft. rewrite in_map_iff. now exists rule. 
    - right; left. unfold makeShiftLeft in H. apply in_map_iff in H as (rule' & <- & H2). now rewrite <- polarityRevWin_involutive. 
  Qed.

  Corollary tape_rules_revp rule : rule el makeTapeRules <-> polarityRevWin rule el makeTapeRules. 
  Proof. 
    split.
    - now apply tape_rules_revp'. 
    - intros. specialize (tape_rules_revp' H). now rewrite <- polarityRevWin_involutive. 
  Qed. 

 
  (** *automation *)
  (** *TODO*)
  (* Hint Unfold makeIdentity. *)
  (* Hint Unfold makeIdentityBoth makeIdentityRulesBlankBlankBlank makeIdentityRulesTemplate makeExhaustive.  *)
  Lemma blank : {inr |_| , inr |_| , inr |_|} / {inr |_| , inr |_| , inr |_| } el makeIdentity. 
  Proof. 
    (* eauto.  *)
    unfold makeIdentity. repeat rewrite in_app_iff. 
    right; left. unfold makeIdentityBoth. rewrite in_app_iff. left. unfold makeIdentityRulesBlankBlankBlank. cbn. now left. 
  Qed.  


  (** *representation of tapes *)
  Definition stape := list Sigma. 
  Implicit Type (u v : stape). 

  Definition halftape := list Gamma.
  Implicit Type (h : halftape). 


  (*a string consisting of k blanks*)
  Fixpoint E k : halftape := match k with 0 => [] | S k => inr |_| :: E k end. 

  Lemma E_length (v  : nat) : |(E v)| = v. 
  Proof. 
    induction v; cbn.
    - reflexivity.  
    - rewrite <- IHv at 2. reflexivity.  (*slightly hacky because of typeclass inference *)
  Qed. 


  Definition wo := 3.

  Lemma E_w_step w : E (w + wo) = (inr |_|) :: E (w + wo -1).
  Proof.
    remember (w + wo). destruct n. 
    + unfold wo in Heqn; lia. 
    + now cbn. 
  Qed. 

  Definition mapPolarity p u : list Gamma := map (fun e => inr (withPolaritySigma p e)) u.
  Definition reprTape' w u h p:= length h = w+wo /\ length u <= w /\ h = (mapPolarity p u) ++ E ( w + wo - (|u|)). 

  Definition reprTape := reprTape' z'. 

  Notation "u '≃t' h" := (exists p, reprTape u h p) (at level 80).
  Notation "u '≃t(' p ')' h" := (reprTape u h p) (at level 80). 

  Notation "u '≃t(' p ',' w ')' h" := (reprTape' w u h p) (at level 80). 

  Lemma niltape_repr' : forall w p, [] ≃t(p, w) (E (w + wo)) /\ forall a, [] ≃t(p, w) a -> a = E (w + wo). 
  Proof.
    intros. repeat split.
    - now apply E_length. 
    - now cbn.
    - cbn. now rewrite Nat.sub_0_r. 
    - intros. destruct H as (H1 & H2 & H3). rewrite H3. cbn. now rewrite Nat.sub_0_r. 
  Qed. 

  Lemma niltape_repr : forall p, [] ≃t(p) E z /\ forall a, [] ≃t(p) a -> a = E z. 
  Proof. apply niltape_repr'. Qed. 
    
  Lemma reprTape_length' w u h p : u ≃t(p, w) h -> (|h|) >= w + wo. 
  Proof. intros (H1 & H2 & H3). lia. Qed. 

  Lemma reprTape_length u h p : u ≃t(p) h -> (|h|) >= z.
  Proof. apply reprTape_length'. Qed. 
 

  (** *representation of configurations *)
  Definition strconfig := list Gamma.
  Implicit Type (s x : strconfig).

  Definition embedState (q : states) (m : stateSigma) : Gamma := inl (q, m). 
  Definition reprConfig c (s : list Gamma) := match c with (q, tape) => match tape with
                                                | niltape _ => s = E z ++ [embedState q |_|] ++ E z
                                                | leftof r rs => exists h, (r :: rs) ≃t h /\ s = E z ++ [embedState q |_|] ++ h
                                                | rightof r rs => exists h, (r :: rs) ≃t h /\ s = rev h ++ [embedState q |_|] ++ E z
                                                | midtape ls m rs => exists p h1 h2, ls ≃t(p) h1 /\ rs ≃t(p) h2 /\ s = rev h1 ++ [embedState q (Some m)] ++ h2
                                               end end. 

  Notation "c '≃c' s" := (reprConfig c s) (at level 80). 

  Definition getState s : option States := match nth_error s z with None => None | Some q => match q with inl q => Some q | inr _ => None end end.  
  (*tape positions are one-based *)
  Definition getLeft s n : option tapeSigma := match nth_error s (z - n) with None => None |  Some q => match q with inr q => Some q | inl _ => None end end.
  Definition getRight s n : option tapeSigma := match nth_error s (z + n) with None => None | Some q => match q with inr q => Some q | inl _ => None end end. 

  Definition tape_getCurrent (tape : tape Sigma) : stateSigma := match tape with midtape _ m _ => Some m | _ => |_| end. 

  Lemma getState_Some q tape s : (q, tape) ≃c s -> getState s = Some (q, tape_getCurrent tape). 
  Proof. 
    intros. destruct tape; cbn [reprConfig] in H. 
    2: destruct H as (h & H1 & H). 1-2: rewrite H; unfold getState; rewrite nth_error_app2; [ rewrite E_length; now rewrite Nat.sub_diag | rewrite E_length; lia]. 
    1: destruct H as (h1 & [p (H1 & H3 & H4)] & H2).
    2: destruct H as (p & h1 & h2 & ((H1 & H4 & H5) & (H3 & H6 & H7)& H2 )). 
    all: rewrite H2; unfold getState; rewrite nth_error_app2; [ | unfold wo, z, z' in *; rewrite rev_length; rewrite H1; lia].
    all: rewrite rev_length, H1; now rewrite Nat.sub_diag. 
  Qed. 

  (* Lemma getLeft_Some q tape s n : (q, tape) ≃c s -> n <= z -> getLeft s n = *)

  (* Lemma tape_repr_step u us p σ h : (u :: us) ≃t(p) (inr (Some σ)) :: h ->  *)


  Lemma tape_repr_inv w u p (x : States) a : u ≃t(p, w) (@inl States tapeSigma x) :: a -> False. 
  Proof. 
    intros []. destruct H0. destruct u. 
    + cbn in H1. rewrite Nat.sub_0_r in H1. now rewrite E_w_step in H1. 
    + now cbn in H1. 
  Qed. 

  Lemma tape_repr_inv2 w p (σ : polSigma) a : [] ≃t(p, w) (@inr States tapeSigma (Some σ))::a -> False. 
  Proof. 
    intros (H1 & H2 & H3).
    cbn in H3. rewrite Nat.sub_0_r in H3. now rewrite E_w_step in H3.  
  Qed. 

  Lemma tape_repr_inv3 w p (u : Sigma) (us : list Sigma) h : u :: us ≃t(p, w) (inr |_| :: h) -> False. 
  Proof. intros (H1 & H2 & H3). cbn in H3. unfold withPolaritySigma in H3. congruence. Qed. 


  Ltac discr_tape := match goal with
                     | [ H : ?u ≃t(?p, ?w) (inl ?e) :: ?a |- _] => now apply tape_repr_inv in H
                     | [ H : [] ≃t(?p, ?w) (inr (Some ?e)) :: ?a |- _] => now apply tape_repr_inv2 in H
                     | [ H : ?u :: ?us ≃t(?p, ?w) inr |_| :: ?a |- _] => now apply tape_repr_inv3 in H
                      end. 

  Lemma tape_repr_step u h a b p w : (a :: u) ≃t(p, S w) (b :: h) -> u ≃t(p, w) h. 
  Proof. 
    intros (H1 & H2 & H3). cbn [length] in *; repeat split.
    - lia. 
    - lia. 
    - cbn [mapPolarity map] in H3. replace (S w + wo - S (|u|)) with (w + wo - (|u|)) in H3 by lia. 
      replace (map (fun e => inr (withPolaritySigma p e)) u) with (mapPolarity p u) in H3 by now cbn.  
      cbn [app] in H3. congruence. 
  Qed. 

  (* Lemma rewritesHead_list_length *)




  Lemma rewritesAt_add_at_end i sig rule (a b c d : string sig) : rewritesAt rule i a b -> rewritesAt rule i (a ++ c) (b ++ d). 
  Proof. 
    intros. unfold rewritesAt, rewritesHead in *. 
    unfold Prelim.prefix in *. destruct H as ((b1 & H1) & (b2 & H2)). 
    split.
    - exists (b1 ++ c). rewrite app_assoc. apply skipn_app2 with (c := prem rule ++ b1); [ | assumption]. 
      destruct rule, prem. now cbn.  
    - exists (b2 ++ d). rewrite app_assoc. apply skipn_app2 with (c := conc rule ++ b2); [ | assumption]. 
      destruct rule, conc. now cbn. 
   Qed. 


  (* Notation "a ⇝ b" := (valid a b) (at level 90, left associativity). *)
  Lemma tape_rewrite_symm1 u h p h' : u ≃t(p) h -> valid makeTapeRules h h' -> valid makeTapeRules (polarityRev h) (polarityRev h'). 
  Proof with try discr_tape.
    (* *TODO: need a non-trivial strengthening due to the static length constraint imposed by the ≃t relation*)
    intros.
    unfold reprTape in H. revert u H. generalize z'. 
    induction H0; intros. 
    - cbn; constructor. 
    - apply reprTape_length' in H1. cbn [length] in H1; unfold wo in H1. lia.  
    - destruct x... destruct e...
      + destruct u... destruct n; [ destruct H2; cbn in H3; lia | ]. apply tape_repr_step in H2 as H3. 
        specialize (IHvalid n u H3). clear H3. 
        apply valid_iff. apply valid_iff in IHvalid as (IH1 & IH2). repeat split. 
        * cbn [polarityRev]. repeat rewrite app_length. rewrite IH1. now cbn [length]. 
        * cbn [polarityRev]. rewrite app_length. cbn[length]. intros. 
          destruct (Nat.eq_dec i ((|polarityRev a|) -2)). (*is it the position that we have to cover with a new rule? *)
          -- apply tape_rules_revp in H. exists (polarityRevWin rule). split; [assumption | ].  
             rewrite e1. admit.
          -- assert (0 <= i < (|polarityRev a|) -2) by lia. specialize (IH2 i H4) as (rule' & F1 & F2). clear H3 n0 H4.
             exists rule'; split; [assumption | ]. now apply rewritesAt_add_at_end. 
    + destruct u... (*the unique a which satisfies this condition is E n-1 *)

  Admitted. 

  Lemma tape_rewrite_symm2 u h p h' : u ≃t(p) h -> valid makeTapeRules (polarityRev h) (polarityRev h') -> valid makeTapeRules h h'.
  Proof with simp_tape.
  Admitted. 

  Lemma tape_rewrite_symm3 u h p h' : u ≃t(p) h -> valid makeTapeRules h h' -> valid makeTapeRules (map polarityFlipGamma h) h'. 
  Admitted. 

  


End fixTM. 

Compute (makeTapeRules (FinType(EqType bool)) (FinType (EqType bool))).

