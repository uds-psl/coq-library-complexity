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


Definition involution (X : Type) (f : X -> X) := forall (x : X), f (f x) = x. 

Lemma map_involution (X : Type)(f : X -> X) : involution f -> involution (map f). 
Proof. 
  intros. intros l. rewrite map_map. setoid_rewrite H. now rewrite map_id. 
Qed. 

Lemma involution_invert_eqn (X : Type) (f : X -> X) : involution f -> forall a b, f a = f b -> a = b. 
Proof. 
  intros. enough (f (f a) = f(f b)) by (now repeat rewrite H). easy. 
Qed. 

Lemma involution_invert_eqn2 (X : Type) (f : X -> X) : involution f -> forall a b, f a = b -> a = f b. 
Proof. 
  intros. rewrite <- (H a). now apply involution_invert_eqn with (f := f). 
Qed. 

Hint Resolve -> makeExhaustive_correct. 

Module Type TMSig. 
  Parameter (states : finType).
  Parameter (Sigma : finType).
  Parameter (trans : (states * option Sigma) -> (states * (option Sigma * move))). 
  Parameter (halt : states -> bool). 
  Parameter (t k : nat).
End TMSig. 

Module basics (sig : TMSig).
  Export sig. 

  Definition sconfig := (states * tape Sigma)%type. (* single-tape configuration*)
  Implicit Type (c : sconfig). 

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
  Lemma polarityFlip_involution : involution polarityFlip. 
  Proof. intros p. now destruct p. Qed. 
  Definition polarityFlipSigma (x : polSigma) := match x with (p, σ) => (polarityFlip p, σ) end. 
  Lemma polarityFlipSigma_involution : involution polarityFlipSigma.
  Proof. intros x. destruct x, p; now cbn. Qed.

  Definition polarityFlipTapeSigma' (x : tapeSigma') : tapeSigma' := match x with |_| => |_| | Some σ => Some (polarityFlipSigma σ) end. 
  Definition polarityFlipTapeSigma (x : tapeSigma) : tapeSigma := match x with inr a => inr (polarityFlipTapeSigma' a) | $ => $ end. 
  Definition polarityFlipGamma (x : Gamma) : Gamma := match x with inl s => inl s | inr x => inr (polarityFlipTapeSigma x) end.

  Notation "'~' x" := (polarityFlipGamma x). 
  Notation "'#' x" := (polarityFlipTapeSigma' x) (at level 30). 
  Notation "'%' x" := (polarityFlipTapeSigma x) (at level 30). 

  Lemma polarityFlipTapeSigma'_involution : involution polarityFlipTapeSigma'.
  Proof. intros x. destruct x; [ | now cbn]. cbn. now rewrite polarityFlipSigma_involution. Qed. 

  Lemma polarityFlipTapeSigma_involution : involution polarityFlipTapeSigma.
  Proof.
    intros x. destruct x; [ destruct d; now cbn | ]. cbn; now rewrite polarityFlipTapeSigma'_involution.
  Qed. 
  Lemma polarityFlipGamma_involution : involution polarityFlipGamma. 
  Proof. 
    intros x. destruct x; [now cbn | ]. cbn. now rewrite polarityFlipTapeSigma_involution.  
  Qed. 

  Lemma polarityFlipSigmaInv1 e p σ : polarityFlipSigma e = (p, σ) -> e = (polarityFlip p, σ). 
  Proof. 
    unfold polarityFlipSigma. destruct e. intros. inv H. specialize (polarityFlip_involution p0). congruence. 
  Qed. 

  Lemma polarityFlipTapeSigmaInv1 e p σ : polarityFlipTapeSigma e = inr (Some (p, σ)) -> e = inr (Some (polarityFlip p, σ)). 
  Proof.
    unfold polarityFlipTapeSigma. destruct e.
    + destruct d. congruence. 
    + destruct e.  
      - intros. inv H. destruct e. cbn in H1. inv H1. specialize (polarityFlip_involution p0) as ->. reflexivity.
      - cbn; congruence. 
  Qed. 
  Lemma polarityFlipTapeSigma'Inv1 e p σ : polarityFlipTapeSigma' e = (Some (p, σ)) -> e = (Some (polarityFlip p, σ)). 
  Proof.
    unfold polarityFlipTapeSigma'. destruct e.  
    - intros. inv H. destruct e. cbn in H1. inv H1. specialize (polarityFlip_involution p0) as -> ;reflexivity. 
    - cbn; congruence. 
  Qed.

  (*reverse a string + flip its polarities *)
  Definition polarityRev (x : list Gamma) : list Gamma := rev (map polarityFlipGamma x).

  Lemma polarityRev_involution : involution polarityRev.
  Proof. 
    intros x. unfold polarityRev. rewrite map_rev, rev_involutive, map_map. setoid_rewrite polarityFlipGamma_involution. 
    induction x; [eauto | cbn [map]; now rewrite IHx]. 
  Qed. 

  Lemma polarityRev_eqn_move a b : a = polarityRev b -> b = polarityRev a. 
  Proof. intros ->; symmetry; now apply polarityRev_involution. Qed. 


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

  Lemma E_polarityFlip n : map polarityFlipGamma (E n) = E n. 
  Proof. induction n; cbn; now f_equal. Qed. 

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

  Lemma tape_repr_polarityFlip ls p w h : ls ≃t(p, w) h -> ls ≃t(polarityFlip p, w) map polarityFlipGamma h. 
  Proof. 
    intros (H1 & H2 & H3). repeat split. 
    - now rewrite map_length. 
    - apply H2.
    - rewrite H3. unfold mapPolarity, polarityFlipGamma. rewrite map_app. rewrite map_map. 
      rewrite E_polarityFlip. easy. 
  Qed. 

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

End basics. 
