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

Hint Resolve -> makeExhaustive_correct. 

Section fixTM.
  Variable (states : finType).
  Variable (Sigma : finType).
  Variable (trans : (states * option Sigma) -> (states * (option Sigma * move))). 
  Variable (halt : states -> bool). 

  Definition sconfig := (states * tape Sigma)%type. (* single-tape configuration*)
  Implicit Type (c : sconfig). 

  Variables (t k : nat).
  Definition z' := t + k. (*effectively available space on each tape side *)
  Definition wo := 2.     (*additional space for each side in order to make proofs more convenient *)
  Definition z := z' + wo. (*length of each tape side *)
  Definition l := 2 * (z + 1) + 1. (*length of the whole string: two tape sides and the state symbol*)

  Hint Unfold z z' l. 

  Inductive polarity := positive | negative | neutral. 

  Hint Constructors polarity. 

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

  Inductive delim := delimC. 
  Hint Constructors delim.
  Instance delim_eqTypeC : eq_dec delim.
  Proof. unfold dec. decide equality. Qed. 

  Instance delim_finTypeC : finTypeC (EqType delim). 
  Proof. exists [delimC]. intros []. simpl. dec; congruence. Qed. 

  Notation "$" := (inl delimC). 

  Definition polSigma := FinType (EqType (polarity * Sigma)%type). 
  Definition tapeSigma' := FinType (EqType (option polSigma)). 
  Definition tapeSigma := FinType (EqType (sum delim tapeSigma')).

  Definition stateSigma := FinType (EqType (option Sigma)). 

  Definition States := FinType (EqType ((states * stateSigma)%type)). 

  Definition Gamma := FinType (EqType ((States + tapeSigma)%type)). 
 

  Implicit Type (γ : Gamma).
  Implicit Type (q : states).
  Implicit Type (m : tapeSigma).
  Implicit Type (p : polarity).

  (* Definition inra := @inr States tapeSigma. *)
  (* Coercion inra : tapeSigma >-> Gamma. *)

  Notation "'|_|'" := (None). 

  (*move tape element from state to tape cell, adding a polarity*)
  Definition withPolaritySigma p σ : tapeSigma := inr(Some (p, σ)). 
  Definition withPolarity p (σ: stateSigma) : tapeSigma := match σ with |_| => inr |_| | Some σ => (withPolaritySigma p σ)  end.

  (*move from tape cell to state cell *)
  Definition removePolarity (σ : tapeSigma') : stateSigma := match σ with |_| => |_| | Some (p, σ) => Some σ end.

  Notation "p ! a" := (withPolarity p a) (at level 5). 
  Notation "p !! a" := (withPolaritySigma p a) (at level 5). 

  Hint Unfold withPolarity. 

  Definition setPolarity p (σ : polSigma) : polSigma := match σ with (_, σ) => (p, σ) end. 

  (*flip the polarity of a symbol *)
  Definition polarityFlip p := match p with negative => positive | positive => negative | neutral => neutral end. 
  Lemma polarityFlip_involutive p : polarityFlip(polarityFlip p) = p.
  Proof. now destruct p. Qed. 
  Definition polarityFlipSigma (x : polSigma) := match x with (p, σ) => (polarityFlip p, σ) end. 
  Lemma polarityFlipSigma_involutive (x : polSigma) : polarityFlipSigma (polarityFlipSigma x) = x. 
  Proof. destruct x, p; now cbn. Qed.

  Definition polarityFlipTapeSigma' (x : tapeSigma') : tapeSigma' := match x with |_| => |_| | Some σ => Some (polarityFlipSigma σ) end. 
  Definition polarityFlipTapeSigma (x : tapeSigma) : tapeSigma := match x with inr a => inr (polarityFlipTapeSigma' a) | $ => $ end. 
  Definition polarityFlipGamma (x : Gamma) : Gamma := match x with inl s => inl s | inr x => inr (polarityFlipTapeSigma x) end.

  Notation "'~' x" := (polarityFlipGamma x). 
  Notation "'#' x" := (polarityFlipTapeSigma' x) (at level 30). 
  Notation "'%' x" := (polarityFlipTapeSigma x) (at level 30). 

  Lemma polarityFlipTapeSigma'_involutive (x: tapeSigma') : (##x) = x. 
  Proof. destruct x; [ | now cbn]. cbn. now rewrite polarityFlipSigma_involutive. Qed. 

  Lemma polarityFlipTapeSigma_involutive (x :tapeSigma) : (polarityFlipTapeSigma (polarityFlipTapeSigma x)) = x. 
  Proof.
    destruct x; [ destruct d; now cbn | ]. cbn; now rewrite polarityFlipTapeSigma'_involutive.
  Qed. 
  Lemma polarityFlipGamma_involutive (x : Gamma) : (~~x) = x. 
  Proof. 
    destruct x; [now cbn | ]. cbn. now rewrite polarityFlipTapeSigma_involutive.  
  Qed. 

  Lemma polarityFlipSigmaInv1 e p σ : polarityFlipSigma e = (p, σ) -> e = (polarityFlip p, σ). 
  Proof. 
    unfold polarityFlipSigma. destruct e. intros. inv H. now rewrite polarityFlip_involutive.
  Qed. 

  Lemma polarityFlipTapeSigmaInv1 e p σ : polarityFlipTapeSigma e = inr (Some (p, σ)) -> e = inr (Some (polarityFlip p, σ)). 
  Proof.
    unfold polarityFlipTapeSigma. destruct e.
    + destruct d. congruence. 
    + destruct e.  
      - intros. inv H. destruct e. cbn in H1. inv H1. now rewrite polarityFlip_involutive.
      - cbn; congruence. 
  Qed. 

  (*reverse a string + flip its polarities *)
  Definition polarityRev (x : list Gamma) : list Gamma := rev (map polarityFlipGamma x).

  Lemma polarityRev_involutive (x : list Gamma) : polarityRev(polarityRev x) = x. 
  Proof. 
    unfold polarityRev. rewrite map_rev, rev_involutive, map_map. setoid_rewrite polarityFlipGamma_involutive. 
    induction x; [eauto | cbn [map]; now rewrite IHx]. 
  Qed. 



  (** *inductive rewriteHead predicates *)


  Inductive shiftRightWindow : tapeSigma' -> tapeSigma' -> tapeSigma' -> tapeSigma' -> tapeSigma' -> tapeSigma' -> Prop :=
  | shiftRightSSSS σ1 σ2 σ3 σ4 p : shiftRightWindow (Some (p, σ1)) (Some (p, σ2)) (Some (p, σ3)) (Some (↑ σ4)) (Some (↑σ1)) (Some (↑ σ2))
  | shiftRightBBB σ1 : shiftRightWindow |_| |_| |_| (Some (↑ σ1)) |_| |_|
  | shiftRightSBB σ1 σ2 p : shiftRightWindow (Some (p, σ1)) |_| |_| (Some (↑ σ2)) (Some (↑ σ1)) |_|
  | shiftRightSSB σ1 σ2 σ3 p : shiftRightWindow (Some (p, σ1)) (Some (p, σ2)) |_| (Some (↑ σ3)) (Some (↑ σ1)) (Some (↑ σ2))
  | shiftRightBBS σ1 p : shiftRightWindow |_| |_| (Some (p, σ1)) |_| |_| |_|
  | shiftRightBSS σ1 σ2 p : shiftRightWindow |_| (Some (p, σ1)) (Some (p, σ2)) |_| |_| (Some (↑ σ1))
  | shiftRightSSSB σ1 σ2 σ3 p : shiftRightWindow (Some (p, σ1)) (Some (p, σ2)) (Some (p, σ3)) |_| (Some (↑ σ1)) (Some (↑ σ2)). 

  Hint Constructors shiftRightWindow. 

  Inductive identityWindow : tapeSigma -> tapeSigma -> tapeSigma -> tapeSigma -> tapeSigma -> tapeSigma -> Prop :=
  | identityBBB : identityWindow (inr |_|) (inr |_|) (inr |_|) (inr |_|) (inr |_|) (inr |_|)
  | identitySSS σ1 σ2 σ3 p: identityWindow (inr (Some (p, σ1))) (inr (Some (p, σ2))) (inr(Some (p, σ3))) (inr (Some (∘ σ1))) (inr (Some (∘ σ2))) (inr (Some (∘ σ3)))
  | identitySBB σ1 p : identityWindow (inr (Some (p, σ1))) (inr |_|) (inr |_|) (inr (Some (∘ σ1))) (inr |_|) (inr |_|)
  | identitySSB σ1 σ2 p : identityWindow (inr (Some (p, σ1))) (inr (Some (p, σ2))) (inr |_|) (inr (Some (∘ σ1))) (inr (Some (∘ σ2))) (inr |_|)
  | identityBBS σ1 p : identityWindow (inr |_|) (inr |_|) (inr (Some (p, σ1))) (inr |_|) (inr |_|) (inr (Some(∘ σ1)))
  | identityBSS σ1 σ2 p : identityWindow (inr |_|) (inr (Some (p, σ1))) (inr (Some (p, σ2))) (inr |_|) (inr(Some (∘ σ1))) (inr (Some (∘ σ2)))
  | identityDBB : identityWindow $ (inr |_|) (inr |_|) $ (inr |_|) (inr |_|)
  | identityBBD : identityWindow (inr |_|) (inr |_|) $ (inr |_|) (inr |_|) $. 

  Hint Constructors identityWindow.

  Inductive rewHeadTape : string Gamma -> string Gamma -> Prop :=
  | rewShiftLeftTapeC (σ1 σ2 σ3 σ4 σ5 σ6 : tapeSigma') u v: shiftRightWindow (#σ3) (#σ2) (#σ1) (#σ6) (#σ5) (#σ4) -> rewHeadTape ((inr (inr σ1)) :: (inr (inr σ2)) :: (inr (inr σ3)) :: u) ((inr (inr σ4)) :: (inr (inr σ5)) :: (inr (inr σ6)) :: v)
  | rewShiftRightTapeC  (σ1 σ2 σ3 σ4 σ5 σ6 : tapeSigma') u v : shiftRightWindow σ1 σ2 σ3 σ4 σ5 σ6 -> rewHeadTape ((inr (inr σ1)) :: (inr (inr σ2)) :: (inr (inr σ3)) :: u) ((inr (inr σ4)) :: (inr (inr σ5)) :: (inr (inr σ6)) :: v)
  | rewIdentityTapeC (σ1 σ2 σ3 σ4 σ5 σ6 : tapeSigma) u v : identityWindow σ1 σ2 σ3 σ4 σ5 σ6 -> rewHeadTape ((inr σ1) :: (inr σ2) :: (inr σ3) :: u) ((inr σ4) :: (inr σ5) :: (inr σ6) :: v).

  Hint Constructors rewHeadTape. 

  Lemma rewHeadTape_tail_invariant γ1 γ2 γ3 γ4 γ5 γ6 u v u' v' :
    rewHeadTape (γ1 :: γ2 :: γ3 :: u) (γ4 :: γ5 :: γ6 :: v) <-> rewHeadTape (γ1 :: γ2 :: γ3 :: u') (γ4 :: γ5 :: γ6 :: v').
  Proof. split; intros; inv H; eauto. Qed. 

  Lemma rewHeadTape_append_invariant γ1 γ2 γ3 γ4 γ5 γ6 u v u' v' :
    rewHeadTape (γ1 :: γ2 :: γ3 :: u) (γ4 :: γ5 :: γ6 :: v) <-> rewHeadTape (γ1 :: γ2 :: γ3 :: u ++ u') (γ4 :: γ5 :: γ6 :: v ++ v').
  Proof. now apply rewHeadTape_tail_invariant. Qed. 



  Lemma identityWindow_revp (σ1 σ2 σ3 σ4 σ5 σ6 : tapeSigma) : identityWindow σ1 σ2 σ3 σ4 σ5 σ6 <-> identityWindow (%σ3) (%σ2) (%σ1) (%σ6) (%σ5) (%σ4). 
  Proof.
    split; intros; inv H; cbn.
    all: repeat match goal with
           | [H : delim |- _] => destruct H
           | [H : inr _ = % _ |- _] => symmetry in H
           | [H : % ?a = inr |_| |- _] => is_var a; destruct a; cbn in H; try congruence 
           | [H : inr (# ?a) = inr |_| |- _] => is_var a; destruct a; cbn in H; try congruence
           | [H : $ = $ |- _] => clear H
           | [H : |_| = |_| |- _] => clear H
           | [H : inr _ = inr _ |- _] => inv H
           | [H : inl _ = inl _ |- _] => inv H
           | [H : $ = % ?a |- _] => is_var a; destruct a; cbn in H; try congruence
           | [H : % _ = inr(Some (_, _)) |- _] => apply polarityFlipTapeSigmaInv1 in H as ->
                end.
    all: eauto. 
  Qed. 

  Lemma rewHeadTape_revp' γ1 γ2 γ3 γ4 γ5 γ6 : rewHeadTape [γ1; γ2; γ3] [γ4; γ5; γ6] -> rewHeadTape [~γ3; ~γ2; ~γ1] [~γ6; ~γ5; ~γ4]. 
  Proof. 
    intros. inv H. 
    - apply rewShiftRightTapeC. apply H1.
    - apply rewShiftLeftTapeC. now repeat rewrite polarityFlipTapeSigma'_involutive.
    - apply identityWindow_revp in H1. now apply rewIdentityTapeC. 
  Qed. 

  Lemma rewHeadTape_revp γ1 γ2 γ3 γ4 γ5 γ6 : rewHeadTape [γ1; γ2; γ3] [γ4; γ5; γ6] <-> rewHeadTape [~γ3; ~γ2; ~γ1] [~γ6; ~γ5; ~γ4].
  Proof. 
    split. apply rewHeadTape_revp'. intros H%rewHeadTape_revp'. now repeat rewrite polarityFlipGamma_involutive in H. 
  Qed.

  Lemma rewritesAt_rewHeadTape_add_at_end i a b u v : rewritesAt rewHeadTape i a b -> rewritesAt rewHeadTape i (a ++ u) (b ++ v).  
  Proof. 
    intros. unfold rewritesAt in *. inv H; symmetry in H0; symmetry in H1; repeat erewrite skipn_app2; eauto; try congruence; cbn; eauto. 
  Qed. 

  (** *automation *)
  (** *TODO*)


  (** *representation of tapes *)
  Definition stape := list Sigma. 
  Implicit Type (u v : stape). 

  Definition halftape := list Gamma.
  Implicit Type (h : halftape). 


  (*a string consisting of k blanks*)
  Fixpoint E k : halftape := match k with 0 => [inr $] | S k => inr (inr |_|) :: E k end. 

  Lemma E_length (v  : nat) : |(E v)| = S v. 
  Proof. 
    induction v; cbn.
    - reflexivity.  
    - rewrite <- IHv at 1. reflexivity.  (*slightly hacky because of typeclass inference *)
  Qed. 

  Lemma E_w_step w : E (w + wo) = (inr (inr |_|)) :: E (w + wo -1).
  Proof.
    remember (w + wo). destruct n. 
    + unfold wo in Heqn; lia. 
    + now cbn. 
  Qed. 

  Lemma E_w_head w : E (w + wo) = (inr (inr |_|)) :: (inr(inr |_|)) :: E w. 
  Proof. 
    remember (w + wo); unfold wo in Heqn. destruct n; [ lia | destruct n; [lia | ]]. now cbn. 
  Qed. 

  Definition mapPolarity p u : list Gamma := map (fun e => inr (withPolaritySigma p e)) u.
  Definition reprTape' w u h p:= length h = S w+wo /\ length u <= w /\ h = (mapPolarity p u) ++ E ( w + wo - (|u|)). 

  Definition reprTape := reprTape' z'. 

  Notation "u '≃t' h" := (exists p, reprTape u h p) (at level 80).
  Notation "u '≃t(' p ')' h" := (reprTape u h p) (at level 80). 

  Notation "u '≃t(' p ',' w ')' h" := (reprTape' w u h p) (at level 80). 

  Lemma niltape_repr : forall w p, [] ≃t(p, w) (E (w + wo)) /\ forall a, [] ≃t(p, w) a -> a = E (w + wo). 
  Proof.
    intros. repeat split.
    - apply E_length. 
    - now cbn.
    - cbn. now rewrite Nat.sub_0_r. 
    - intros. destruct H as (H1 & H2 & H3). rewrite H3. cbn. now rewrite Nat.sub_0_r. 
  Qed. 

  Lemma reprTape_length w u h p : u ≃t(p, w) h -> (|h|) >= S w + wo. 
  Proof. intros (H1 & H2 & H3). lia. Qed. 

  (** *representation of configurations *)
  Definition strconfig := list Gamma.
  Implicit Type (s x : strconfig).

  Definition embedState (q : states) (m : stateSigma) : Gamma := inl (q, m). 
  Definition reprConfig c (s : list Gamma) := match c with (q, tape) => match tape with
                                                | niltape _ => s = rev (E z) ++ [embedState q |_|] ++ E z
                                                | leftof r rs => exists h, (r :: rs) ≃t h /\ s = rev (E z) ++ [embedState q |_|] ++ h
                                                | rightof r rs => exists h, (r :: rs) ≃t h /\ s = rev h ++ [embedState q |_|] ++ E z
                                                | midtape ls m rs => exists p h1 h2, ls ≃t(p) h1 /\ rs ≃t(p) h2 /\ s = rev h1 ++ [embedState q (Some m)] ++ h2
                                               end end. 

  Notation "c '≃c' s" := (reprConfig c s) (at level 80). 

  Definition getState s : option States := match nth_error s (S z) with None => None | Some q => match q with inl q => Some q | inr _ => None end end.  
  (*tape positions are one-based *)
  Definition getLeft s n : option tapeSigma := match nth_error s (S z - n) with None => None |  Some q => match q with inr q => Some q | inl _ => None end end.
  Definition getRight s n : option tapeSigma := match nth_error s (S z + n) with None => None | Some q => match q with inr q => Some q | inl _ => None end end. 

  Definition tape_getCurrent (tape : tape Sigma) : stateSigma := match tape with midtape _ m _ => Some m | _ => |_| end. 

  Lemma getState_Some q tape s : (q, tape) ≃c s -> getState s = Some (q, tape_getCurrent tape). 
  Proof. 
    intros. destruct tape; cbn [reprConfig] in H. 
    2: destruct H as (h & H1 & H). 1-2: rewrite H; unfold getState; rewrite nth_error_app2; rewrite rev_length, E_length;  [ now rewrite Nat.sub_diag | lia]. 
    1: destruct H as (h1 & [p (H1 & H3 & H4)] & H2).
    2: destruct H as (p & h1 & h2 & ((H1 & H4 & H5) & (H3 & H6 & H7)& H2 )). 
    all: rewrite H2; unfold getState; rewrite nth_error_app2; [ | unfold z, z', wo in *; rewrite rev_length; rewrite H1; lia ].
    all: rewrite rev_length, H1; now rewrite Nat.sub_diag. 
  Qed. 


  (** *basic facts about tape rewriting *)
  Lemma tape_repr_step u h a b p w : (a :: u) ≃t(p, S w) (b :: h) -> u ≃t(p, w) h. 
  Proof. 
    intros (H1 & H2 & H3). cbn [length] in *; repeat split.
    - lia. 
    - lia. 
    - cbn [mapPolarity map] in H3. replace (S w + wo - S (|u|)) with (w + wo - (|u|)) in H3 by lia. 
      replace (map (fun e => inr (withPolaritySigma p e)) u) with (mapPolarity p u) in H3 by now cbn.  
      cbn [app] in H3. congruence. 
  Qed. 


  Lemma tape_repr_inv w u p (x : States) a : u ≃t(p, w) (@inl States tapeSigma x) :: a -> False. 
  Proof. 
    intros []. destruct H0. destruct u. 
    + cbn in H1. rewrite Nat.sub_0_r in H1. now rewrite E_w_step in H1. 
    + now cbn in H1. 
  Qed. 

  Lemma tape_repr_inv2 w p (σ : polSigma) a : [] ≃t(p, w) (@inr States tapeSigma (inr (Some σ)))::a -> False. 
  Proof. 
    intros (H1 & H2 & H3).
    cbn in H3. rewrite Nat.sub_0_r in H3. now rewrite E_w_step in H3.  
  Qed. 

  Lemma tape_repr_inv3 w p (u : Sigma) (us : list Sigma) h : u :: us ≃t(p, w) (inr (inr |_|) :: h) -> False. 
  Proof. intros (H1 & H2 & H3). cbn in H3. unfold withPolaritySigma in H3. congruence. Qed. 

  Lemma tape_repr_inv4 w p (u : Sigma) (us : list Sigma) h : u :: us ≃t(p, w) (inr $) :: h -> False. 
  Proof. intros (H1 & H2 & H3). cbn in H3. unfold withPolaritySigma in H3; congruence. Qed. 

  Lemma tape_repr_inv5 w p u h e : u ≃t(p, w) (inr $) :: e:: h -> False. 
  Proof.
    intros (H1 & H2 & H3). destruct u; cbn in H3.
    + rewrite Nat.sub_0_r, E_w_step in H3. congruence. 
    + unfold withPolaritySigma in H3; congruence. 
  Qed. 

  Ltac discr_tape := match goal with
                     | [ H : ?u ≃t(?p, ?w) (inl ?e) :: ?a |- _] => now apply tape_repr_inv in H
                     | [ H : [] ≃t(?p, ?w) (inr (inr (Some ?e))) :: ?a |- _] => now apply tape_repr_inv2 in H
                     | [ H : ?u :: ?us ≃t(?p, ?w) inr (inr |_|):: ?a |- _] => now apply tape_repr_inv3 in H
                     | [ H : ?u :: ?us ≃t(?p, ?w) inr $ :: ?a |- _] => now apply tape_repr_inv4 in H
                     | [H : _ ≃t(?p, ?w) inr $ :: ?e :: ?a |- _] => now apply tape_repr_inv5 in H
                      end. 

  Ltac destruct_tape := repeat match goal with
                        | [H : _ ≃t(?p, ?w) ?x :: ?h |- _] => is_var x; destruct x; try discr_tape
                        | [H : _ ≃t(?p, ?w) (inr ?e) :: ?h |- _] => is_var e; destruct e; try discr_tape
                        | [H : ?u ≃t(?p, ?w) inr _ :: ?h |- _] => is_var u; destruct u; try discr_tape
                        | [H : delim |- _] => destruct H; try discr_tape
                          end. 

  Ltac rewHeadTape_inv := repeat match goal with 
                                   | [H : rewHeadTape  ?a _ |- _] => is_var a; destruct a; try (inv H; fail)
                                   | [H : rewHeadTape  (_ :: ?a) _ |- _] => is_var a; destruct a; try (inv H; fail)
                                   | [H : rewHeadTape  (_ :: _ :: ?a) _ |- _] => is_var a; destruct a; try (inv H; fail)
                                   | [H : rewHeadTape  _ ?a |- _ ] => is_var a; destruct a; try (inv H; fail)
                                   | [H : rewHeadTape  _ (_ :: ?a) |-_ ] => is_var a; destruct a; try (inv H; fail)
                                   | [H : rewHeadTape  _ (_ :: _ :: ?a) |- _] => is_var a; destruct a; try (inv H; fail)
                               end.

  Ltac rewHeadTape_inv2 := repeat match goal with
                                  | [H : rewHeadTape _ _ |- _] => inv H
                                  | [H : shiftRightWindow _ _ _ _ _ _ |- _ ] => inv H
                                  | [H : identityWindow _ _ _ _ _ _ |- _] => inv H
                                  | [H : |_| = # ?σ |- _] => is_var σ; destruct σ; cbn in H; try congruence
                                  | [H : # ?σ = |_| |- _] => is_var σ; destruct σ; cbn in H; try congruence
                                  | [H : Some (_, _) = # ?e |- _] => symmetry in H; apply polarityFlipTapeSigmaInv1 in H; rewrite H in *; clear H
                                  | [H : # ?e = Some (_, _) |- _] => apply polarityFlipTapeSigmaInv1 in H; rewrite H in *; clear H
                                  | [H : |_| = |_| |- _] => clear H
                           end. 
 
  Lemma tape_rewrite_symm1 u h p h' : u ≃t(p) h -> valid rewHeadTape h h' -> valid rewHeadTape (polarityRev h) (polarityRev h'). 
  Proof.
    intros.
    unfold reprTape in H. revert u H. generalize z'. 
    induction H0; intros. 
    - cbn; constructor. 
    - apply reprTape_length in H1. cbn [length] in H1; unfold wo in H1. lia.  
    - rewHeadTape_inv. 
      rewrite valid_iff. unfold validExplicit. cbn [polarityRev map rev]. repeat rewrite app_length.
      repeat rewrite rev_length, map_length. cbn [length]. split.
      1: apply valid_length_inv in H0; now cbn [length] in H0. 
      replace ((|a|) + 1 + 1 + 1 - 2) with (S (|a|)) by lia. intros. destruct (nat_eq_dec i (|a|)). 
      * (*rewrite at the new position, cannot apply IH *)
        rewrite e3 in *; clear e3. unfold rewritesAt. 
        apply rewHeadTape_tail_invariant with (u' := []) (v' := []) in H.
        apply rewHeadTape_revp' in H. 
        cbn [rev map].
        repeat rewrite <- app_assoc.
        rewrite skipn_app with (xs := rev (map polarityFlipGamma a)).
        rewrite skipn_app with (xs := rev (map polarityFlipGamma b)).
        2, 3: rewrite rev_length, map_length. 3: reflexivity. 
        2: { apply valid_length_inv in H0; cbn [length] in H0. lia. }
        cbn. apply H. 
      * (*this follows by IH *)
        destruct_tape.
        + destruct n.
          -- cbn in H1. destruct a. 2: { destruct H1 as [F1 [F3 F4]]. now cbn in F1. }
            cbn in H2, n0. lia. 
          -- cbn [Nat.sub] in H2. assert (0 <= i < (|a|)) by lia. clear n0 H2. 
            apply niltape_repr in H1 as H2. cbn [E] in H2. rewrite Nat.add_comm in H2; unfold wo in H2.
            cbn [E Nat.add] in H2. inv H2.
            specialize (niltape_repr n p) as (H4 & _). 
            rewrite Nat.add_comm in H4; unfold wo in H4; cbn [Nat.add E] in H4. 
            specialize (IHvalid n [] H4). apply valid_iff in IHvalid as (IH1 & IH2). 
            cbn [length] in H3. cbn [polarityRev app rev map] in IH2. repeat rewrite app_length in IH2. 
            cbn [length] in IH2. rewrite rev_length, map_length in IH2. replace (|E n| + 1 + 1 -2) with ((|E n|)) in IH2 by lia. 
            specialize (IH2 i H3). cbn [polarityRev app rev map].
            now apply rewritesAt_rewHeadTape_add_at_end. 
        + destruct n. { destruct H1 as [F1 [F3 F4]]. now cbn in F3. }
          apply tape_repr_step in H1. specialize (IHvalid n u H1).
          assert (0 <= i < (|a|)) by lia. clear H2 n0 H. apply valid_iff in IHvalid as [_ IH].
          cbn [length polarityRev rev map app] in IH. repeat rewrite app_length in IH; cbn [length] in IH.
          rewrite rev_length, map_length in IH. replace (|a| + 1 + 1 -2) with (|a|) in IH by lia. 
          specialize (IH i H3) as IH. 
          cbn [rev map polarityFlipGamma].
          now apply rewritesAt_rewHeadTape_add_at_end. 
  Qed. 

  Lemma polarityRev_eqn_move a b : a = polarityRev b -> b = polarityRev a. 
  Proof. intros ->; symmetry; now apply polarityRev_involutive. Qed. 

  Lemma tape_rewrite_symm2 u h p h' : u ≃t(p) h -> valid rewHeadTape (polarityRev h) (polarityRev h') -> valid rewHeadTape h h'.
  Proof.
    (*the proof is structurally very similar to the proof for tape_rewrite_symm1, *)
    (*but not a direct consequence since the tape h is not reversed; *)
    (*the reversion poses an additional challenge for tape inversion*)
    intros. unfold reprTape in H. revert u H. generalize z'. 
    remember (polarityRev h). remember (polarityRev h').
    apply polarityRev_eqn_move in Heql0 as ->. apply polarityRev_eqn_move in Heql1 as ->. 
    induction H0; intros.
    - cbn; constructor. 
    - apply reprTape_length in H1. cbn [length polarityRev map rev] in H1; unfold wo in H1.
      rewrite app_length, rev_length, map_length in H1; cbn [length] in H1; lia.  
    - rewHeadTape_inv. 
      rewrite valid_iff. unfold validExplicit. cbn [polarityRev map rev]. repeat rewrite app_length.
      repeat rewrite rev_length, map_length. cbn [length]. split.
      1: apply valid_length_inv in H0; now cbn [length] in H0. 
      replace ((|a|) + 1 + 1 + 1 - 2) with (S (|a|)) by lia. intros. destruct (nat_eq_dec i (|a|)). 
      * (*rewrite at the new position, cannot apply IH *)
        rewrite e3 in *; clear e3. unfold rewritesAt. 
        apply rewHeadTape_tail_invariant with (u' := []) (v' := []) in H.
        apply rewHeadTape_revp' in H. 
        (* cbn [rev map]. *)
        repeat rewrite <- app_assoc.
        rewrite skipn_app with (xs := rev (map polarityFlipGamma a)).
        rewrite skipn_app with (xs := rev (map polarityFlipGamma b)).
        2, 3: rewrite rev_length, map_length. 3: reflexivity. 
        2: { apply valid_length_inv in H0; cbn [length] in H0. lia. }
        cbn. apply H. 
      * (*this follows by IH *)
        (* destruct_tape. *)
        (* + destruct n. { destruct H1 as [F1 [F3 F4]]. now cbn in F3. } *)
        (*   apply tape_repr_step in H1. specialize (IHvalid n u H1). *)
        (*   assert (0 <= i < (|a|)) by lia. clear H2 n0 H. apply valid_iff in IHvalid as [_ IH]. *)
        (*   cbn [length polarityRev rev map app] in IH. repeat rewrite app_length in IH; cbn [length] in IH. *)
        (*   rewrite rev_length, map_length in IH. replace (|a| + 1 + 1 -2) with (|a|) in IH by lia.  *)
        (*   specialize (IH i H3) as IH.  *)
        (*   cbn [rev map polarityFlipGamma]. *)
        (*   now apply rewritesAt_rewHeadTape_add_at_end.  *)
        (* + destruct n. *)
        (*   -- cbn in H1. destruct a. 2: { destruct H1 as [F1 [F3 F4]]. now cbn in F1. } *)
        (*     cbn in H2, n0. lia.  *)
        (*   -- cbn [Nat.sub] in H2. assert (0 <= i < (|a|)) by lia. clear n0 H2.  *)
        (*     apply niltape_repr in H1 as H2. cbn [E] in H2. rewrite Nat.add_comm in H2; unfold wo in H2. *)
        (*     cbn [E Nat.add] in H2. inv H2. *)
        (*     specialize (niltape_repr n p) as (H4 & _).  *)
        (*     rewrite Nat.add_comm in H4; unfold wo in H4; cbn [Nat.add E] in H4.  *)
        (*     specialize (IHvalid n [] H4). apply valid_iff in IHvalid as (IH1 & IH2).  *)
        (*     cbn [length] in H3. cbn [polarityRev app rev map] in IH2. repeat rewrite app_length in IH2.  *)
        (*     cbn [length] in IH2. rewrite rev_length, map_length in IH2. replace (|E n| + 1 + 1 + 1 -2) with (S (|E n|)) in IH2 by lia.  *)
        (*     specialize (IH2 i H3). cbn [polarityRev app rev map]. *)
        (*     now apply rewritesAt_rewHeadTape_add_at_end.  *)

  Admitted. 

  Lemma tape_rewrite_symm3 u h p h' : u ≃t(p) h -> valid rewHeadTape h h' -> valid rewHeadTape (map polarityFlipGamma h) h'. 
  Proof. 
    intros. induction H0. 
    - cbn; constructor. 
    - 
  Admitted. 

  


End fixTM. 

Compute (makeTapeRules (FinType(EqType bool)) (FinType (EqType bool))).

