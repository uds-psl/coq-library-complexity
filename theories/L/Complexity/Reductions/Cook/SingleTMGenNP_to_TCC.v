(* -*- company-coq-local-symbols: (("|_|" .?␣)); -*- *)
(** printing  *|_|* %\textvisiblespace% #␣# *)
From Complexity.L.Complexity.Problems Require Import SingleTMGenNP TCC FlatTCC . 
From Complexity.L.Complexity.Reductions.Cook Require Import PTCC_Preludes TM_single.
From Complexity.L.Complexity Require Import FlatFinTypes MorePrelim. 
From Undecidability.Shared.Libs.PSL Require Import FiniteTypes. 
Require Import Lia. 
Require Import Undecidability.Shared.Libs.PSL.FiniteTypes.BasicDefinitions. 
Require Import Undecidability.Shared.Libs.PSL.FiniteTypes.FinTypes.
From Undecidability.TM Require Import TM_facts.


(** * Reduction of single-tape Turing machines to 3-CC *)

Notation "f $ x" := (f x) (at level 60, right associativity, only parsing).

(**We build the tableau construction as a CC instance.
  The translation to the FlatSingleTMGenNP to FlatTCC reduction is directly done in this file
  as Coq's section mechanism does not support multiple files
  (and it would be super tedious to explicitly pass in the fixed variables after leaving the section).*)
Section fixTM. 
  Variable (Sigma : finType).
  Variable (fTM : TM Sigma 1).

  Notation states := (state fTM).  
  Notation trans := (@strans Sigma fTM). 
  Notation start := (start fTM). 
  Notation halt := (@halt Sigma 1 fTM). 

  (** ** Alphabet *)

  (**number of steps to simulate *)
  Variable (t : nat).
  (**maximum length of certificate*)
  Variable (k' : nat). 
  Variable (fixedInput : list Sigma). 

  Notation sconfig := (sconfig fTM). 
  Implicit Type (c : sconfig). 
  Notation sstep := (sstep trans). 

  (*our nice 1-tape definition should not be reduced *)
  Arguments strans : simpl never. 
  
  (**total input length: fixed input + certificate *)
  Definition k := (|fixedInput|) + k'. 
  (**effectively available space on each side of the tape *)
  Definition z := t + k. 
  (**additional space for each side in order to make proofs more convenient *)
  Definition wo := 2.     
  (**length of each tape side *)
  Definition z' := wo + z. 
  (**length of the whole string: two tape sides and the state symbol*)
  Definition l := 2 * (z' + 1) + 1. 

  Hint Unfold z' z l : core. 

  (**for polarities, we just interpret move in a different way in order to save us the translation at some point *)
  Hint Constructors move : core. 
  Notation polarity := move. 
  Notation positive := Rmove. 
  Notation negative := Lmove. 
  Notation neutral := Nmove. 

  Implicit Type σ : Sigma.

  Declare Scope polscope. 
  Notation "'↓' σ" := ((negative, σ)) (at level 50) : polscope. 
  Notation "'↑' σ" := ((positive, σ)) (at level 50) : polscope.
  Notation "'∘' σ" := ((neutral, σ)) (at level 50) : polscope. 
  Local Open Scope polscope.

  (** delimiter symbol *)
  Inductive delim : Set := delimC. 
  Hint Constructors delim : core.
  Global Instance delim_eqTypeC : eq_dec delim.
  Proof. unfold dec. decide equality. Defined. 

  Global Instance delim_finTypeC : finTypeC (EqType delim). 
  Proof. exists [delimC]. intros []. simpl. dec; congruence. Defined. 

  Notation "#" := (inl delimC). 

  Definition stateSigma := (option Sigma). 
  Definition polSigma := ((polarity * stateSigma)%type).
  Definition tapeSigma := (sum delim polSigma).
  Definition States := ((states * stateSigma)%type). 
  Definition Gamma := ((States + tapeSigma)%type). 

  Ltac foldAbbrevs := fold stateSigma polSigma tapeSigma States Gamma in *.

  Implicit Type (γ : Gamma).
  Implicit Type (q : states).
  Implicit Type (m : stateSigma).
  Implicit Type (p : polarity).

  (*a new scope is used because the notation later is not needed anymore *)
  Open Scope cc_scope. 
  Notation "'|_|'" := (None) : cc_scope. 

  (* The following options allow for asynchronous proof processing *)
  Set Default Proof Using "Type".

  (**flip the polarity of a symbol *)
  Definition polarityFlip p := match p with negative => positive | positive => negative | neutral => neutral end. 
  Lemma polarityFlip_involution : involution polarityFlip. 
  Proof. intros p. now destruct p. Qed. 

  Smpl Add (apply polarityFlip_involution) : involution.

  Definition polarityFlipSigma (x : polSigma) := match x with (p, σ) => (polarityFlip p, σ) end. 
  Lemma polarityFlipSigma_involution : involution polarityFlipSigma.
  Proof. intros x. destruct x as [[] σ]; now cbn. Qed.

  Smpl Add (apply polarityFlipSigma_involution) : involution. 

  Definition polarityFlipTapeSigma (x : tapeSigma) : tapeSigma := match x with inr a => inr (polarityFlipSigma a) | # => # end. 
  Definition polarityFlipGamma (x : Gamma) : Gamma := match x with inl s => inl s | inr x => inr (polarityFlipTapeSigma x) end.

  Lemma polarityFlipTapeSigma_involution : involution polarityFlipTapeSigma.
  Proof.
    intros x. idtac. destruct x; [ destruct d; now cbn | ]. destruct p; cbn. do 2 f_equal. apply polarityFlip_involution. 
  Qed. 
  Lemma polarityFlipGamma_involution : involution polarityFlipGamma. 
  Proof. 
    intros x. destruct x; [now cbn | ]. cbn. now rewrite polarityFlipTapeSigma_involution.  
  Qed. 

  Smpl Add (apply polarityFlipTapeSigma_involution) : involution.
  Smpl Add (apply polarityFlipGamma_involution) : involution.

  Notation "'~' x" := (polarityFlipGamma x). 
  Notation "'!' x" := (polarityFlipSigma x) (at level 1). 
  Notation "'%' x" := (polarityFlipTapeSigma x) (at level 30).
  
  Lemma polarityFlipSigmaInv1 e p m : polarityFlipSigma e = (p, m) -> e = (polarityFlip p, m). 
  Proof. 
    unfold polarityFlipSigma. destruct e as [p' e]. intros. inv H. specialize (polarityFlip_involution p'). congruence. 
  Qed. 

  Set Keyed Unification.
  Lemma polarityFlipTapeSigmaInv1 e p m : polarityFlipTapeSigma e = inr (p, m) -> e = inr (polarityFlip p, m). 
  Proof.
    intros. destruct e; cbn in H; [destruct d; congruence | ].
    inv H. eapply polarityFlipSigmaInv1 in H1. foldAbbrevs. congruence. 
  Qed. 

  Lemma polarityFlipGammaInv1 e p m : polarityFlipGamma e = inr (inr (p, m)) -> e = inr (inr (polarityFlip p, m)). 
  Proof. 
    intros. destruct e; cbn in H; [ congruence | ]. 
    inv H. now apply polarityFlipTapeSigmaInv1 in H1;foldAbbrevs.
  Qed.

  (** reverse a string + flip its polarities *)
  Definition polarityRev (x : list Gamma) : list Gamma := rev (map polarityFlipGamma x).

  Lemma polarityRev_involution : involution polarityRev.
  Proof. 
    intros x. unfold polarityRev. rewrite map_rev, rev_involutive, map_map. setoid_rewrite polarityFlipGamma_involution. 
    induction x; [eauto | cbn [map]; now rewrite IHx]. 
  Qed. 

  Smpl Add (apply polarityRev_involution) : involution. 

  (** ** Representation of tapes *)
  Notation stape := (list Sigma). 

  Notation halftape := (list Gamma).

  (** The empty tape is represented by a string consisting of k blanks followed by #*)
  Fixpoint E p k : halftape := match k with 0 => [inr #] | S k => inr (inr (p, |_|)) :: E p k end. 
  Lemma E_length p n: |(E p n)| = S n. 
  Proof. 
    induction n; cbn.
    - reflexivity.  
    - now rewrite IHn. 
  Qed. 

  Lemma E_polarityFlip p n : map polarityFlipGamma (E p n) = E (polarityFlip p) n. 
  Proof. induction n; cbn; now f_equal. Qed. 

  Definition mapPolarity p u : list Gamma := map (fun e => inr (inr (p, Some e))) u.

  Definition reprTape' w u h p:= (|u|) <= w /\ h = (mapPolarity p u) ++ E p ( wo + w - (|u|)). 
  Definition reprTape := reprTape' z. 

  Notation "u '≃t' h" := (exists p, reprTape u h p) (at level 80).
  Notation "u '≃t(' p ')' h" := (reprTape u h p) (at level 80). 

  Notation "u '≃t(' p ',' w ')' h" := (reprTape' w u h p) (at level 80). 

  Lemma niltape_repr : forall w p, [] ≃t(p, w) (E p (wo + w)) /\ forall a, [] ≃t(p, w) a -> a = E p (wo + w). 
  Proof.
    intros. repeat split.
    - now cbn.
    - intros. destruct H as (H1 & H2). now rewrite H2.
  Qed. 

  Lemma string_reprTapeP_length p u s w: u ≃t(p, w) s -> |s| = S wo + w. 
  Proof. 
    intros (H1 & ->). unfold z', wo, mapPolarity. 
    rewrite app_length, map_length, E_length. lia. 
  Qed. 

  Lemma string_reprTape_length p u s: u ≃t(p) s -> |s| = S z'. 
  Proof. 
    intros. unfold z'. eapply string_reprTapeP_length, H.
  Qed. 

  Lemma tape_repr_polarityFlip ls p w h : ls ≃t(p, w) h -> ls ≃t(polarityFlip p, w) map polarityFlipGamma h. 
  Proof. 
    intros (H1 & H2). repeat split. 
    - apply H1.
    - rewrite H2. unfold mapPolarity, polarityFlipGamma. rewrite map_app, map_map, E_polarityFlip. easy. 
  Qed. 

  (** ** Representation of configurations *)
  Notation strconfig := (list Gamma).

  Definition embedState (q : states) (m : stateSigma) : Gamma := inl (q, m). 
  Definition reprConfig' c ls qm rs := match c with (q, tape) => exists p, qm = embedState q (current tape) /\ reprTape (left tape) ls p /\ reprTape (right tape) rs p end. 
  Definition reprConfig c (s : list Gamma) := exists ls qm rs, s = rev ls ++ [qm] ++ rs /\ reprConfig' c ls qm rs. 

  Notation "c '≃c' '(' ls ',' q ',' rs ')'" := (reprConfig' c ls q rs) (at level 80) : cc_scope.
  Notation "c '≃c' s" := (reprConfig c s) (at level 80) : cc_scope. 

  Lemma string_reprConfig_length q tp s: (q, tp) ≃c s -> |s| = l. 
  Proof. 
    intros. unfold l. destruct H as (ls & qm & rs & -> & (p & -> & H3 & H4)). 
    apply string_reprTape_length in H3. apply string_reprTape_length in H4. 
    rewrite !app_length, rev_length. cbn. rewrite H3, H4. unfold z', z, wo. lia. 
  Qed.

  (**strings representing configs *)
  Definition stringForTapeHalf (s : list Sigma) := mapPolarity neutral s ++ E neutral (z' - |s|).  
  Definition stringForConfig (q : states) (s : tape Sigma) :=
    rev (stringForTapeHalf (left s)) ++ [inl (q, current s)] ++ stringForTapeHalf (right s). 

  Lemma stringForTapeHalf_reprTape s : |s| <= z -> s ≃t(neutral) stringForTapeHalf s.
  Proof. intros. now repeat split. Qed. 

  Lemma stringForConfig_reprConfig q s : sizeOfTape s <= z -> (q, s) ≃c stringForConfig q s. 
  Proof.
    intros.  destruct s; unfold reprConfig, stringForConfig;
               [ exists (stringForTapeHalf []), (inl (q, |_|)), (stringForTapeHalf [])
               | exists (stringForTapeHalf []), (inl (q, |_|)), (stringForTapeHalf (e::l0))
               | exists (stringForTapeHalf (e :: l0)), (inl (q, |_|)), (stringForTapeHalf [])
               | exists (stringForTapeHalf l0), (inl (q, Some e)), (stringForTapeHalf l1)
               ]. 
    all: split; [ reflexivity | ];
      unfold reprConfig'; exists neutral;
      split; cbn; [reflexivity | split; apply stringForTapeHalf_reprTape; cbn in *; try rewrite app_length, rev_length in H; cbn in H; easy].  
  Qed. 

  (** ** Automation for discrimination of the tape relation *)

  Lemma tape_repr_step u h a b p w : (a :: u) ≃t(p, S w) (b :: h) -> u ≃t(p, w) h. 
  Proof. 
    intros (H1 & H2). cbn [length] in *; repeat split. lia. 
    cbn [mapPolarity map] in H2. replace (wo + S w - S (|u|)) with (wo + w - (|u|)) in H2 by lia. 
    replace (map (fun e => inr (inr (p, Some e))) u) with (mapPolarity p u) in H2 by now cbn.  
    cbn [app] in H2. congruence. 
  Qed. 

  Lemma tape_repr_step' u h a b p w : 
    u ≃t(p, w) h 
    -> b = inr (inr (p, Some a)) 
    -> (a :: u) ≃t(p, S w) (b :: h).
  Proof. 
    intros (H1 & H2) H3. split. 
    - cbn; lia. 
    - rewrite H2, H3. easy.
  Qed. 

  Lemma tape_repr_inv w u p (x : States) a : u ≃t(p, w) (@inl States tapeSigma x) :: a -> False. 
  Proof. 
    intros [H H1]. destruct u; now cbn in H1. 
  Qed. 

  Lemma tape_repr_inv2 w p p' (σ : Sigma) a : [] ≃t(p, w) (@inr States tapeSigma (inr (p', Some σ)))::a -> False. 
  Proof. 
    intros (H1 & H2). cbn in H2. congruence. 
  Qed. 

  Lemma tape_repr_inv3 w p p' (u : Sigma) (us : list Sigma) h : u :: us ≃t(p, w) (inr (inr (p', |_|)) :: h) -> False. 
  Proof. intros (H1 & H2). cbn in H2. congruence. Qed. 

  Lemma tape_repr_inv4 w p (u : list Sigma) h : u ≃t(p, w) (inr #) :: h -> False. 
  Proof. intros (H1 & H2). cbn in H2. destruct u; cbn in H2; congruence. Qed. 

  Lemma tape_repr_inv5 w p u h e : u ≃t(p, w) (inr #) :: e:: h -> False. 
  Proof. intros (H1 & H2). destruct u; cbn in H2; congruence. Qed. 

  Lemma tape_repr_inv7 w p p' u us n : us :: u ≃t(p, w) E p' n -> False. 
  Proof. intros (H1 & H2). destruct n; cbn in H2; congruence. Qed.

  Lemma tape_repr_inv16 w p p' m u h : u ≃t(p, w) inr (inr (p', m)) :: h -> p = p'.
  Proof. intros (H1 & H2). destruct u; cbn in H2; inv H2; easy. Qed. 

  Lemma tape_repr_inv8 u us p p' w m rs : us :: u ≃t(p, w) inr(inr (p', m)) :: rs -> m = Some us. 
  Proof. intros (H1 & H2). cbn in H2. congruence. Qed. 

  Lemma tape_repr_inv9 us1 p w e1 rs : [us1] ≃t(p, S w) e1 :: rs -> rs = E p (wo + w). 
  Proof. intros (H1 & H2). cbn in H2. inv H2. easy. Qed. 

  Lemma tape_repr_inv11 u p w rs : u ≃t(p, w) rs -> |rs| >= S wo. 
  Proof. intros H. erewrite string_reprTapeP_length. 2: apply H. lia. Qed. 

  Lemma tape_repr_inv12 u p w rs : u ≃t(p, w) rs -> forall x, x el rs -> exists y, x = inr y. 
  Proof. 
    intros (_ & ->) x H1. 
    apply in_app_or in H1 as [H1 | H1]. 
    + unfold mapPolarity in H1. apply in_map_iff in H1 as (? & <- & H2). eauto. 
    + revert H1. generalize (wo + w - |u|). induction n; intros [H | H]; eauto. 
  Qed. 

  Lemma tape_repr_inv13 u p p' w rs σ: 
    u ≃t(p, w) (inr (inr (p', Some σ)) :: rs) 
    -> p' = p /\ exists u', u = σ :: u'. 
  Proof. 
    intros (H1 & H2). destruct u; cbn in *. 
    + congruence. 
    + split; [ | exists u];  congruence. 
  Qed. 

  Lemma tape_repr_inv14 u p w rs e: u ≃t(p, w) e :: inr (#) :: rs -> False. 
  Proof. 
    intros (H1 & H2). destruct u; unfold wo in H2; cbn in H2; try congruence.
    destruct u; cbn in H2; try congruence.
  Qed. 

  Lemma tape_repr_inv15 u p w : u ≃t(p, w) [] -> False. 
  Proof. intros H%string_reprTapeP_length. now cbn in H. Qed. 

  Lemma tape_repr_inv17 x u p l : x :: u ≃t(p, 0) l -> False. 
  Proof. destruct 1; cbn in *; lia. Qed.

  Ltac destruct_tape1 := repeat match goal with [H : delim |- _ ] => destruct H end.

  (** try to apply the inversion lemmas from above to derive a contradiction*)
  Ltac discr_tape_in H := destruct_tape1; match type of H with
                     | ?u ≃t(?p, ?w) [] => apply tape_repr_inv15 in H as []
                     | ?u ≃t(?p, ?w) (inl ?e) :: ?a => apply tape_repr_inv in H as []
                     | [] ≃t(?p, ?w) (inr (inr (_, Some ?e))) :: ?a => apply tape_repr_inv2 in H as []
                     | ?u :: ?us ≃t(?p, ?w) inr (inr (_, |_|)):: ?a => apply tape_repr_inv3 in H as []
                     | _ ≃t(_, _) _ :: inr # :: _ => apply tape_repr_inv14 in H as []
                     | ?us ≃t(?p, ?w) inr # :: ?a => apply tape_repr_inv4 in H as []
                     | _ ≃t(?p, ?w) inr # :: ?e :: ?a => apply tape_repr_inv5 in H as []
                     | ?u :: ?us ≃t(?p, 0) _ => exfalso; apply tape_repr_inv17 in H as [] 
                     | ?u :: ?us ≃t(?p, ?w) E _ ?n => apply tape_repr_inv7 in H as []
                      end. 
  (** a more expensive version which can solve more contradictions *)
  Ltac discr_tape_in_exp H := first [discr_tape_in H | 
      match type of H with 
      | ?us ≃t(?p, ?w) ?a => let H1 := fresh in apply tape_repr_inv11 in H as H1; unfold wo in H1; cbn [length] in H1; lia
      end]. 

  (**try to maximally invert the representation relation of tapes (hypothesis H) to derive equalities between the symbols of the represented tape and the representing string *)
  (**this tactic can be expensive to call as it goes into recursion after having eliminated the head of the strings *)
  Ltac inv_tape_with H discr := repeat match type of H with (* TODO: improve performance by doing an nested lazymatch instead of matching the term on toplevel? *)
                        | _ ≃t(?p, ?w) ?x :: ?h => is_var x; destruct x; [discr H | ]     
                        | _ ≃t(?p, ?w) (inr ?e) :: ?h => is_var e; destruct e; [discr H | ]
                        | _ ≃t(?p, ?w) (inr (inr ?e)) :: ?h => is_var e; destruct e
                        | _ ≃t(?p, ?w) (inr (inr (?p', _))) :: ?h => is_var p'; pose proof (tape_repr_inv16 H); subst p' 
                        | [] ≃t(?p, ?w) (inr (inr (_, ?e))) :: ?h => is_var e; destruct e; [ discr H | ]
                        | ?u ≃t(?p, ?w) inr (inr (_, |_|)) :: ?h => is_var u; destruct u; [ | discr H] 
                        | ?u :: ?us ≃t(?p, ?w) ?h => is_var h; destruct h; [ discr H | ]
                        | ?u :: ?us ≃t(?p, ?w) ?h' ++ ?h'' => is_var h'; destruct h'; cbn in H; try discr H
                        | ?u :: ?us ≃t(?p, ?w) inr(inr (_, ?m)) :: _ => is_var m; pose proof  (tape_repr_inv8 H); subst m  
                        | ?u1 :: _ ≃t(?p, ?w) _  => is_var w; destruct w; [ discr H | ]
                        | ?u1 :: [] ≃t(_, S ?w) _ :: ?h  => specialize (tape_repr_inv9 H) as ->
                        | ?u ≃t(_, _) inr (inr (_, Some _)) :: _ => is_var u;
                                                                  let Heqn := fresh "Hpeqn" in
                                                                  specialize (tape_repr_inv13 H) as (Heqn & (? & ->)); inv Heqn
                        end;
                        (*if we can, we go into recursion after applying tape_repr_step *)
                        once try match type of H with
                        |  ?u1 :: _ ≃t(?p, S ?w) ?e :: _  => 
                            let H' := fresh in 
                              specialize (tape_repr_step H) as H'; inv_tape_with H' discr; clear H' 
                        end.
  Ltac inv_tape H := inv_tape_with H discr_tape_in. 

  (**the destruct_tape_in tactic generates equations for subtapes which are equal to E _. *)
  (**We do not want to call inv on those equations since they might contain non-trivial equalities which cannot be resolved with a rewrite/subst and would thus be lost with inv*)
  Ltac clear_trivial_niltape H := cbn in H; match type of H with
        | inr (inr (?p, |_|)) :: ?h = inr (inr (?p, |_|)) :: ?h' => 
            let H' := fresh in 
              assert (h = h') as H' by congruence; 
              tryif clear_trivial_niltape H' then clear H else clear H'
        | ?h = inr (inr _) :: _ => is_var h; rewrite H in *; clear H
        | ?h = E _ _ => is_var h; rewrite H in *; clear H
  end.

  (**invert the tape relation given by hypothesis H and destruct up to one head symbol *)
  Ltac destruct_tape_in H := unfold reprTape in H;
                             inv_tape H;
                             try match type of H with
                                 | [] ≃t(_, _) ?h => 
                                     let H' := fresh in 
                                      specialize (proj2 (niltape_repr _ _ ) _ H) as H'; clear_trivial_niltape H'
                                 | ?u ≃t(?p, ?w) inr _ :: ?h  => is_var u; destruct u; try discr_tape_in H
                                 end;
                             inv_tape H;
                             repeat match goal with [H : ?h = ?h |- _] => clear H end.

  (**a variant of destruct_tape_in that takes care of the z constant for the inversion and later tries to substitute the z again *)
  Ltac destruct_tape_in_tidy H := unfold reprTape in H;
                             try match type of H with
                                 | _ ≃t(_, z) _ => let H' := fresh "n" in let H'' := fresh H' "Zeqn" in
                                                    remember z as H' eqn:H'' in H; destruct_tape_in H;
                                                    repeat match goal with [H2 : context[wo + H'] |- _]=> 
                                                        cbn [wo Nat.add] in H2 end; 
                                                    rewrite !H'' in *; try clear H' H'' 
                                 | _ => destruct_tape_in H
                             end. 
 
  (** ** Inductive rules for tape coverings *)
  (*For easier automation, we define the rewrite rules using inductive predicates *)

  (** We use the coversHeadInd predicate from TCC.v *)

  (** unfold the three symbols at the head of premise and conclusion of a rewrite card *)
  Ltac coversHeadInd_inv := 
    repeat match goal with
    | [H : coversHeadInd _ ?a _ |- _] => is_var a; destruct a; try (inv H; fail)
    | [H : coversHeadInd _ (_ :: ?a) _ |- _] => is_var a; destruct a; try (inv H; fail)
    | [H : coversHeadInd _ (_ :: _ :: ?a) _ |- _] => is_var a; destruct a; try (inv H; fail)
    | [H : coversHeadInd _ _ ?a |- _ ] => is_var a; destruct a; try (inv H; fail)
    | [H : coversHeadInd _ _ (_ :: ?a) |-_ ] => is_var a; destruct a; try (inv H; fail)
    | [H : coversHeadInd _ _ (_ :: _ :: ?a) |- _] => is_var a; destruct a; try (inv H; fail)
    end.

  (** the rules for shifting the tape to the right *)
  Inductive shiftRightRules : Gamma -> Gamma -> Gamma -> Gamma -> Gamma -> Gamma -> Prop :=
    | shiftRightSSSS σ1 σ2 σ3 σ4 p : shiftRightRules (inr (inr (p, Some σ1))) (inr (inr (p, Some σ2))) (inr (inr (p, Some σ3))) 
                                                     (inr (inr (↑ Some σ4))) (inr (inr (↑ Some σ1))) (inr (inr (↑ Some σ2))) 
    | shiftRightBBBS p σ1 : shiftRightRules (inr (inr (p, |_|))) (inr (inr (p, |_|))) (inr (inr (p, |_|))) 
                                            (inr (inr (↑ Some σ1))) (inr (inr (↑ |_|))) (inr (inr (↑ |_|)))
    | shiftRightBBBB p : shiftRightRules (inr (inr (p, |_|))) (inr (inr (p, |_|))) (inr (inr (p, |_|))) 
                                         (inr (inr (↑ |_|))) (inr (inr (↑ |_|))) (inr (inr (↑ |_|)))
    | shiftRightSBB σ1 σ2 p : shiftRightRules (inr (inr (p, Some σ1))) (inr (inr (p, |_|))) (inr (inr (p, |_|))) 
                                              (inr (inr (↑ Some σ2))) (inr (inr (↑ Some σ1))) (inr (inr (↑ |_|)))
    | shiftRightSSB σ1 σ2 σ3 p : shiftRightRules (inr (inr (p, Some σ1))) (inr (inr (p, Some σ2))) (inr (inr (p, |_|))) 
                                                 (inr (inr (↑ Some σ3))) (inr (inr (↑ Some σ1))) (inr (inr (↑ Some σ2))) 
    | shiftRightBBS σ1 p : shiftRightRules (inr (inr (p, |_|))) (inr (inr (p, |_|))) (inr (inr (p, Some σ1))) 
                                           (inr (inr (↑ |_|))) (inr (inr (↑ |_|))) (inr (inr (↑ |_|)))
    | shiftRightBSS σ1 σ2 p : shiftRightRules (inr (inr (p, |_|))) (inr (inr (p, Some σ1))) (inr (inr (p, Some σ2))) 
                                              (inr (inr (↑ |_|))) (inr (inr (↑ |_|))) (inr (inr (↑ Some σ1)))
    | shiftRightSSSB σ1 σ2 σ3 p : shiftRightRules (inr (inr (p, Some σ1))) (inr (inr (p, Some σ2))) (inr (inr (p, Some σ3))) 
                                                  (inr (inr (↑ |_|))) (inr (inr (↑ Some σ1))) (inr (inr (↑ Some σ2))).

  Hint Constructors shiftRightRules : core.

  (** identity rules *)
  (** the definition here is simplified: the first constructor creates spurious cards which don't do any harm,but simplify the definition as we need less cases
  *)
  Inductive identityRules : Gamma -> Gamma -> Gamma -> Gamma -> Gamma -> Gamma -> Prop :=
    | identityC (m1 m2 m3 : stateSigma) p : identityRules (inr (inr (p, m1))) (inr (inr (p, m2))) (inr (inr (p, m3))) (inr (inr (neutral, m1))) (inr (inr (neutral, m2))) (inr (inr (neutral, m3)))
  | identityDBB p p' : identityRules (inr #) (inr (inr (p, |_|))) (inr (inr (p, |_|))) (inr #) (inr (inr (p', |_|))) (inr (inr (p', |_|)))
  | identityBBD p p' : identityRules (inr (inr (p, |_|))) (inr (inr (p, |_|))) (inr #) (inr (inr (p', |_|))) (inr (inr (p', |_|))) (inr #). 

  Hint Constructors identityRules : core.

  (** the rules for shifting the tape left are derived from the ones for right shifts using reversion and polarity flips *)
  Inductive tapeRules : Gamma -> Gamma -> Gamma -> Gamma -> Gamma -> Gamma -> Prop :=
  | shiftLeftTapeC γ1 γ2 γ3 γ4 γ5 γ6: shiftRightRules (~γ3) (~γ2) (~γ1) (~γ6) (~γ5) (~γ4) -> tapeRules γ1 γ2 γ3 γ4 γ5 γ6
  | shiftRightTapeC γ1 γ2 γ3 γ4 γ5 γ6: shiftRightRules γ1 γ2 γ3 γ4 γ5 γ6 -> tapeRules γ1 γ2 γ3 γ4 γ5 γ6
  | identityTapeC γ1 γ2 γ3 γ4 γ5 γ6: identityRules γ1 γ2 γ3 γ4 γ5 γ6 -> tapeRules γ1 γ2 γ3 γ4 γ5 γ6. 

  Hint Constructors tapeRules : core. 

  Notation covHeadTape := (coversHeadInd tapeRules).
  Notation "a '⇝{' M '}' b" := (valid (coversHeadInd M) a b) (at level 40) : cc_scope.

  (** since the rules for shifting left are derived from the rules for shifting right using polarityFlipGamma,
    the polarity flip functions need to be reduced in order to be able to apply the constructors *)
  Hint Extern 4 (tapeRules _ _ _ _ _ _) => apply shiftLeftTapeC;
  cbn [polarityFlipGamma polarityFlipTapeSigma polarityFlipSigma polarityFlip] : core.

  Ltac covHeadTape_inv1 :=
    repeat match goal with
    | [H : covHeadTape _ _ |- _] => inv H
    | [H : tapeRules _ _ _ _ _ _ |- _] => inv H
    end.

  (** identity cards are invariant under polarity flip + reversion *)
  Lemma identityCard_revp (γ1 γ2 γ3 γ4 γ5 γ6 : Gamma) : 
    identityRules γ1 γ2 γ3 γ4 γ5 γ6 <-> identityRules (~γ3) (~γ2) (~γ1) (~γ6) (~γ5) (~γ4).
  Proof.
    split; intros; inv H; cbn.
    all: repeat match goal with
           | [H : delim |- _] => destruct H
           | [H : inr _ = (~ _) |- _] => symmetry in H
           | [H : inr _ = inr _ |- _] => inv H
           | [H : inl _ = inl _ |- _] => inv H
           | [H : (~ ?a) = inr (#) |- _ ] => is_var a; destruct a; cbn in H; [congruence | ]
           | [H : % ?a = # |- _] => is_var a; destruct a; cbn in H; try congruence
           | [H : (~ _)= inr(inr ((_, _))) |- _] => apply polarityFlipGammaInv1 in H as ->
                end; try congruence.
    all: eauto. 
  Qed. 

  (** in fact, all tape cards are invariant under polarity flip + reversion: for the shift cards, this directly follows from the definition *)
  Lemma tapeRules_revp' γ1 γ2 γ3 γ4 γ5 γ6 : tapeRules γ1 γ2 γ3 γ4 γ5 γ6 -> tapeRules (~γ3) (~γ2) (~γ1) (~γ6) (~γ5) (~γ4). 
  Proof. 
    intros. covHeadTape_inv1. 
    - eauto. 
    - constructor. now rewrite !polarityFlipGamma_involution.
    - apply identityCard_revp in H0. eauto.  
  Qed. 

  Lemma tapeRules_revp γ1 γ2 γ3 γ4 γ5 γ6 : tapeRules γ1 γ2 γ3 γ4 γ5 γ6 <-> tapeRules (~γ3) (~γ2) (~γ1) (~γ6) (~γ5) (~γ4).
  Proof. 
    split.
    apply tapeRules_revp'. intros H%tapeRules_revp'.
    specialize polarityFlipGamma_involution as H1. unfold involution in H1.
    now repeat rewrite H1 in H.
  Qed.

  (** inversion of the tape rules *)
  Ltac covHeadTape_inv2 :=
    repeat match goal with
      | [H : covHeadTape _ _ |- _ ] => inv H
      | [H : tapeRules _ _ _ _ _ _ |- _] => inv H
      | [H : shiftRightRules _ _ _ _ _ _ |- _ ] => inv H
      | [H : identityRules _ _ _ _ _ _ |- _] => inv H
      | [d : delim |- _] => destruct d
      | [H : (~?e) = inr (inr (_, _)) |- _] => apply polarityFlipGammaInv1 in H; try rewrite H in *; clear H
      | [H : inr (inr (_, _)) = (~?e) |- _] => symmetry in H; apply polarityFlipGammaInv1 in H; try rewrite H in *; clear H
      | [H : inr _ = inr _ |- _] => inv H
      | [H : inl _ = inl _ |- _] => inv H
    end; try congruence. 
 
  (** The follocardg lemmas allow us to prove results only for the right tape half and derive the corresponding results for the left tape half as corollaries *)
  Lemma tape_cover_symm1 h h' :
    h ⇝{tapeRules} h' -> (polarityRev h) ⇝{tapeRules} (polarityRev h').
  Proof.
    (*because of the reversion, we use the explicit characterisation *)
    intros.  
    induction H as [ | ? ? ? ? H IH H0 | ? ? ? ? H IH H0].
    - cbn; constructor. 
    - apply valid_length_inv in H.
      destruct a, b; try destruct a; try destruct b; cbn in *; try lia. all: repeat constructor. 
    - coversHeadInd_inv; cbn. 
      rewrite valid_iff. unfold validExplicit. repeat rewrite app_length.
      repeat rewrite rev_length, map_length. cbn [length]. split.
      1: apply valid_length_inv in H; now cbn [length] in H. 
      replace ((|a|) + 1 + 1 + 1 - 2) with (S (|a|)) by lia. intros. destruct (nat_eq_dec i (|a|)) as [-> | F]. 
      * (*rewrite at the new position, cannot apply IH *)
        unfold coversAt. 
        apply coversHeadInd_rem_tail in H0.
        inv H0. apply tapeRules_revp' in H3. 
        cbn [rev map].
        repeat rewrite <- app_assoc.
        rewrite skipn_app with (xs := rev (map polarityFlipGamma a)).
        rewrite skipn_app with (xs := rev (map polarityFlipGamma b)).
        2, 3: rewrite rev_length, map_length. 3: reflexivity. 
        2: { apply valid_length_inv in H; cbn [length] in H. lia. }
        cbn. constructor. apply H3. 
      * (*this follows by IH *)
        cbn [polarityRev map rev] in IH. 
        apply valid_iff in IH as (IH1 & IH2). 
        assert (0 <= i < |a|) by lia. 
        repeat rewrite app_length in IH2. rewrite rev_length, map_length in IH2. cbn [length] in IH2.
        replace ((|a|) + 1 + 1 - 2) with (|a|) in IH2 by lia. 
        specialize (IH2 i H2).
        apply coversAt_coversHeadInd_add_at_end. apply IH2. 
  Qed. 

  Lemma tape_cover_symm2 h h' : (polarityRev h) ⇝{tapeRules} (polarityRev h') -> h ⇝{tapeRules} h'.
  Proof.
    intros. specialize (tape_cover_symm1 H) as H1. now repeat rewrite polarityRev_involution in H1.
  Qed. 

  Lemma tape_cover_symm3 h h' : h ⇝{tapeRules} h' -> (map polarityFlipGamma h) ⇝{tapeRules} h'. 
  Proof. 
    intros. unfold reprTape in H. induction H as [ | ? ? ? ? H IH H0 | ? ? ? ? H IH H0]; intros. 
    - cbn; constructor. 
    - cbn; constructor. 2: now rewrite map_length. apply IH.
    - cbn. coversHeadInd_inv. constructor 3.
      + apply IH. 
      + cbn. apply coversHeadInd_rem_tail. covHeadTape_inv2; cbn; eauto 10.  
  Qed.

  (** We can rewrite to a blank tape again and this is uniquely determined*)
  Lemma E_cover_blank p p' n:
    (E p (S (S n))) ⇝{tapeRules} (E p' (S (S n)))
    /\ forall s, (E p (S (S n))) ⇝{tapeRules} (inr (inr (p', |_|)) :: s) -> s = E p' (S n).
  Proof. 
    split.
    - intros. induction n as [ | n IH]. 
      + apply valid_base. eauto. 
      + constructor 3. 
        * cbn [E] in IH. now apply IH. 
        * destruct p'; eauto. 
    - revert n. 
      enough (forall n, n >= 1 -> forall s, 
        (E p (S n)) ⇝{tapeRules} (inr (inr (p', |_|)) :: s) 
        -> s = E p' n) as H by (intros; now eapply H). 
    intros n H. induction n as [ | n IH]; intros; [lia | ]. 
    destruct n; cbn [E] in *. 
    + inv_valid. covHeadTape_inv2. 
      apply valid_length_inv in H4. inv H4. now (destruct s2; cbn in H1).
    + inv_valid. covHeadTape_inv2.
      1-2: cbn in *; destruct p'; cbn in H5; try congruence; clear H5.
      all: apply IH in H4; [foldAbbrevs;congruence | lia].
  Qed. 

  (** the same results for the left tape half; we use the symm lemmas from above *)
  Lemma E_cover_blank_rev p p' w :
    (rev (E p (S (S w)))) ⇝{tapeRules} (rev (E p' (S (S w))))
    /\ forall s, (rev (E p (S (S w)))) ⇝{tapeRules} (rev (inr (inr (p', |_|)) :: s)) -> s = (E p' (S (w))).
  Proof. 
    split. 
    - specialize (E_cover_blank (polarityFlip p) (polarityFlip p') w) as [H1 _]. 
      apply tape_cover_symm1 in H1. 
      rewrite <- !E_polarityFlip in H1. unfold polarityRev in H1.
      rewrite !map_involution in H1. 2-3: involution_simpl. apply H1. 
    - intros.
      assert (valid covHeadTape (polarityRev (E (polarityFlip p) (S (S w)))) (polarityRev (map polarityFlipGamma (inr (inr (p', |_|)) :: s)))). 
      {
        unfold polarityRev. rewrite E_polarityFlip. rewrite map_involution. 2: involution_simpl. rewrite polarityFlip_involution. apply H.
      }
      apply tape_cover_symm2 in H0.
      cbn in H0. apply E_cover_blank in H0.
      apply involution_invert_eqn2 with (a := s) (f:= (map polarityFlipGamma))  (b := E (polarityFlip p') (S w)) in H0.
      2: involution_simpl. now rewrite H0, E_polarityFlip, polarityFlip_involution.
  Qed. 

  (** We can add a symbol at the head of an empty tape string *)
  Lemma E_cover_sym p σ n :
    (E p (S (S (S n)))) ⇝{tapeRules} (inr (inr (positive, Some σ)) :: E positive (S (S n)))
    /\ (forall s, (E p (S (S (S n)))) ⇝{tapeRules} (inr (inr (positive, Some σ)) :: s) -> s = E positive (S (S n))).
  Proof. 
    split.
    - cbn [E]. constructor 3. 
      + apply E_cover_blank. 
      + eauto. 
    - intros. inv_valid. covHeadTape_inv2.
      all: cbn [E]; f_equal; apply E_cover_blank in H3; auto. 
   Qed.

  Lemma E_cover_sym_rev p σ n:
    (rev (E p (S (S (S n))))) ⇝{tapeRules} (rev (inr (inr (negative, Some σ)) :: E negative (S (S n))))
    /\ forall s, (rev (E p (S (S (S n))))) ⇝{tapeRules} (rev (inr (inr (negative, Some σ)) :: s)) -> s = E negative (S (S n)). 
  Proof. 
    specialize (E_cover_sym (polarityFlip p) σ n) as [H1 H2]. split.
    - (*follows using tape_cover_symm1, tape_cover_symm3 and E_cover_sym *)
      eapply tape_cover_symm1 in H1. 
      unfold polarityRev in H1. rewrite E_polarityFlip in H1. rewrite polarityFlip_involution in H1.
      cbn [map polarityFlipGamma polarityFlipTapeSigma polarityFlipSigma polarityFlip] in H1. 
      now rewrite E_polarityFlip in H1. 
    - clear H1. intros.
      assert (valid covHeadTape (polarityRev (E (polarityFlip p) (S (S (S n))))) (polarityRev (inr (inr (positive, Some σ)) :: map polarityFlipGamma s))). 
      {
        unfold polarityRev. rewrite E_polarityFlip. cbn. rewrite map_involution. 2: involution_simpl.
        specialize (polarityFlip_involution p) as H1. rewrite H1. apply H. 
      }
      eapply tape_cover_symm2 in H0. eapply H2 in H0. 
      enough (map polarityFlipGamma (E negative (S (S n))) = E positive (S (S n))).
      { rewrite <- H1 in H0. apply involution_invert_eqn in H0. assumption. apply map_involution, polarityFlipGamma_involution. }
      apply E_polarityFlip.
  Qed. 

  (** We can also remove a symbol *)
  Lemma E_cover_sym_rem p σ n :
    (inr (inr (p, Some σ)) :: E p (S (S n))) ⇝{tapeRules} (E negative (S (S (S n))))
    /\ forall s p', (inr (inr (p, Some σ)) :: E p (S (S n))) ⇝{tapeRules} (inr (inr (p', |_|)):: s) -> p' = negative /\ s = E negative (S (S n)).
  Proof. 
    split.
    - cbn. constructor 3.  
      + apply E_cover_blank.
      + eauto. 
    - intros. inv_valid. covHeadTape_inv2.
      destruct p'; cbn in H5; try congruence; clear H5.
      split; [reflexivity | ]. 
      inv_valid. 1: destruct n; cbn in H5; lia.
      covHeadTape_inv2.
      3: {
        destruct n; cbn in *; inv H3.
        apply valid_length_inv in H2; destruct s0; cbn in H2; foldAbbrevs;congruence.
      }
      all: destruct n; cbn in H3; [congruence | ];
        apply E_cover_blank in H2;
        rewrite H2; easy.   
  Qed. 

  Lemma E_cover_sym_rem_rev p σ n : 
    (rev (inr (inr (p, Some σ)) :: E p (S (S n)))) ⇝{tapeRules} (rev (E positive (S (S (S n)))))
    /\ forall s p', (rev (inr (inr (p, Some σ)) :: E p (S (S n)))) ⇝{tapeRules} (rev (inr (inr (p', |_|)) :: s)) 
        -> p' = positive /\ s = E p' (S (S n)).
  Proof. 
    split.
    - specialize (E_cover_sym_rem p σ n) as [H1 _].
      eapply tape_cover_symm3 in H1.
      eapply tape_cover_symm1 in H1. 
      unfold polarityRev in H1. rewrite map_involution in H1 by involution_simpl.
      cbn [map polarityFlipGamma polarityFlipTapeSigma polarityFlipSigma polarityFlip] in H1. 
      now rewrite E_polarityFlip in H1.
    - intros.
      assert (valid covHeadTape (polarityRev (inr (inr (polarityFlip p, Some σ)) :: E (polarityFlip p) (S (S n)))) (polarityRev (inr (inr (polarityFlip p', |_|)) :: map polarityFlipGamma s))). 
      {
        unfold polarityRev. cbn [map]. rewrite E_polarityFlip. cbn. rewrite map_involution. 2: apply polarityFlipGamma_involution.
        specialize (polarityFlip_involution) as H1. unfold involution in H1. 
        rewrite !H1. apply H. 
      }
      eapply tape_cover_symm2 in H0.
      apply (proj2 (E_cover_sym_rem _ _ _)) in H0 as (H0 & H1). 
      destruct p'; cbn in H0; try congruence; clear H0. 
      split; [reflexivity | ]. 
      enough (map polarityFlipGamma (E negative (S (S n))) = E positive (S (S n))).
      { rewrite <- H1 in H0. rewrite map_involution in H0; [apply H0 | involution_simpl]. }
      apply E_polarityFlip. 
  Qed. 

  (** ** Changing tape representations by one symbol *)

  (** We can add a symbol to an arbitrary tape string if there is enough space left *)
  Lemma tape_repr_add_right rs σ h p w:
    rs ≃t(p, w) h -> length rs < w
    -> exists h', h ⇝{tapeRules} (inr (inr (↑ (Some σ))) :: h')
            /\ (forall h0, h ⇝{tapeRules} (inr (inr (↑ (Some σ))) :: h0) -> h0 = h')
            /\ σ :: rs ≃t(positive, w)  (inr (inr (↑ (Some σ))) :: h').
  Proof. 
    intros. revert w h σ H H0. 
    induction rs as [ | a rs IH]; intros w h σ H H0.
    - destruct_tape_in H.
      exists (E positive (wo + w - 1)). rewrite <- and_assoc; split.
      + cbn in H0. destruct w; [lia | ]. unfold wo. cbn [Nat.add Nat.sub]. split.
        * (*existence*) apply E_cover_sym.
        * (*uniqueness*) intros. eapply E_cover_sym, H1. 
      + repeat split. easy. 
    - destruct_tape_in H.
      edestruct IH with (σ := a) as (h' & H1 & H2 & H3).
      1: { apply tape_repr_step in H; apply H. } 1: cbn in H0; easy.
      clear IH. 
      exists (inr (inr (↑ Some a)) ::h'). 
      split; [ | split]. 
      + econstructor 3; [ apply H1 | ]. 
        destruct rs; destruct_tape_in H3; [ | destruct rs; destruct_tape_in H3]; destruct_tape_in H; cbn; eauto. 
      + intros. inv H4. 
        { destruct h; [ discr_tape_in_exp H | destruct h; [discr_tape_in_exp H | now cbn in H10]].  }
        covHeadTape_inv2; apply H2 in H8; now inv H8. 
      + now apply tape_repr_step'.
  Qed.

  (**The same result for the left tape half can be derived using the symm lemmas*)
  Corollary tape_repr_add_left ls σ h p w:
    ls ≃t(p, w) h -> length ls < w
    -> exists h', (rev h) ⇝{tapeRules} (rev (inr (inr (↓ (Some σ))) :: h'))
            /\ (forall h0, (rev h) ⇝{tapeRules} (rev (inr (inr (↓ (Some σ))) :: h0)) -> h0 = h')
            /\ σ :: ls ≃t(negative, w)  (inr (inr (↓ (Some σ))) :: h').
  Proof. 
    intros. specialize (@tape_repr_add_right ls σ h p w H H0) as (h' & H1 & H3 & H2). 
    exists (map polarityFlipGamma h'). rewrite <- and_assoc. split. 
    - apply tape_cover_symm3 in H1. eapply tape_cover_symm1 in H1.
      split. 
      + cbn in *. unfold polarityRev in H1. rewrite map_involution in H1 by involution_simpl.
        apply H1. 
      + intros. specialize (H3 (map polarityFlipGamma h0)).
        rewrite <- involution_invert_eqn2 with (f := map polarityFlipGamma) (a := h0) (b := h'); [reflexivity | involution_simpl | ]. 
        apply H3. eapply tape_cover_symm2. 
        unfold polarityRev. rewrite <- map_rev. apply tape_cover_symm3. 
        cbn. rewrite map_involution; [now apply H4 | apply polarityFlipGamma_involution]. 
   - apply tape_repr_polarityFlip in H2. cbn in H2. easy. 
  Qed. 

  (** We can remove a symbol from the right tape half *)
  Lemma tape_repr_rem_right rs σ1 m2(h : list Gamma) p w :
    σ1 :: rs ≃t(p, w) inr (inr (p, Some σ1)) :: inr (inr (p, m2)) :: h
    -> exists (h' : list Gamma), (inr (inr (p, Some σ1)) :: inr (inr (p, m2)) :: h) ⇝{tapeRules} (inr (inr (↓ m2)) :: h')
                           /\ (forall h0, (inr (inr (p, Some σ1)) :: inr (inr (p, m2)) :: h) ⇝{tapeRules} (inr (inr (↓ m2)) :: h0) -> h0 = h')
                           /\ rs ≃t(negative, w) (inr (inr (↓ m2)) :: h').
  Proof. 
    revert w h σ1 m2. 
    induction rs as [ | a rs IH]; intros w h σ1 m2 H. 
    - destruct_tape_in H. exists (E negative (wo + w)). rewrite <- and_assoc; split. 
      + split.
        * apply E_cover_sym_rem.  
        * intros. now apply E_cover_sym_rem in H0.
      + repeat split; now cbn.
    - destruct_tape_in H.
      destruct h; [discr_tape_in_exp H | ]; destruct_tape_in H. rename s into o. 
      edestruct IH as (h' & H1 & H2 & H3). 1: apply tape_repr_step in H; apply H. 
      exists (inr (inr (↓ o)) :: h'). split; [ | split]. 
      + constructor 3; [apply H1 | ]. 
        destruct rs; destruct_tape_in H3; [ | destruct rs; destruct_tape_in H3]; destruct_tape_in H; cbn; eauto. 
      + intros. inv_valid. covHeadTape_inv2; apply H2 in H7; now inv H7. 
      + now apply tape_repr_step'.
  Qed. 

  Corollary tape_repr_rem_left ls σ (m : stateSigma) h p w :
    σ :: ls ≃t(p, w) inr (inr (p, Some σ)) :: inr (inr (p, m)) :: h
    -> exists h', (rev (inr (inr (p, Some σ)) :: inr (inr (p, m)) :: h)) ⇝{tapeRules} (rev (inr (inr (↑m)) :: h'))
            /\ (forall h0, (rev (inr (inr (p, Some σ)) :: inr (inr (p, m)) :: h)) ⇝{tapeRules} (rev (inr (inr (↑m)) :: h0)) -> h0 = h')
            /\ ls ≃t(positive, w) (inr (inr (↑m)) :: h').
  Proof. 
    intros. specialize (@tape_repr_rem_right ls σ m h p w H) as (h' & H1 & H3 & H2). 
    exists (map polarityFlipGamma h'). rewrite <- and_assoc. split. 
    - apply tape_cover_symm3 in H1. eapply tape_cover_symm1 in H1.
      split. 
      + unfold polarityRev in H1. rewrite map_involution in H1 by involution_simpl.
        destruct m; cbn in H1; cbn; apply H1.
      + intros. specialize (H3 (map polarityFlipGamma h0)).
        rewrite <- involution_invert_eqn2 with (f := map polarityFlipGamma) (a := h0) (b := h'); [reflexivity | involution_simpl | ]. 
        apply H3. eapply tape_cover_symm2. 
        unfold polarityRev. rewrite <- map_rev. apply tape_cover_symm3. 
        cbn in *. rewrite map_involution; [destruct m; cbn in *; now apply H0 | apply polarityFlipGamma_involution]. 
   - apply tape_repr_polarityFlip in H2. destruct m; cbn in H2; easy. 
  Qed. 

  Lemma tape_repr_stay_right rs m h p w :
    rs ≃t(p, w) inr(inr (p, m)) :: h
    -> exists h', (inr (inr (p, m)) :: h) ⇝{tapeRules} (inr (inr (neutral, m)) :: h')
            /\ (forall h0, (inr (inr (p, m)) :: h) ⇝{tapeRules} (inr (inr (∘ m)) :: h0) -> h0 = h')
            /\ rs ≃t(neutral, w) (inr (inr (∘ m))) :: h'.
  Proof. 
    revert w h m.  
    induction rs as [ | a rs IH]; intros w h m H.
    - destruct_tape_in H. exists (E neutral (S w)). split; [ | split]. 
      + apply E_cover_blank.
      + intros. now apply E_cover_blank in H0.
      + repeat split; cbn in *; easy. 
    - destruct_tape_in H.
      destruct h; [ discr_tape_in_exp H | ]. destruct_tape_in H. rename s into o. 
      edestruct IH as (h' & H1 & H2 & H3). { apply tape_repr_step in H. apply H. }
      exists (inr (inr (∘ o)) :: h'). split; [ | split]. 
      + econstructor 3; [ apply H1 | ].
        destruct rs; destruct_tape_in H3; [ | destruct rs; destruct_tape_in H3]; destruct_tape_in H; cbn; eauto. 
      + intros. inv_valid. { destruct h; [discr_tape_in_exp H | now cbn in H9]. }
        covHeadTape_inv2. apply H2 in H7; now inv H7. 
      + now apply tape_repr_step'.
   Qed. 

  Corollary tape_repr_stay_left ls e h p w :
    ls ≃t(p, w) inr(inr (p, e)) :: h
    -> exists h', (rev (inr (inr (p, e)) :: h)) ⇝{tapeRules} (rev (inr (inr (neutral, e)) :: h'))
            /\ (forall h0, (rev (inr (inr (p, e)) :: h)) ⇝{tapeRules} (rev (inr (inr (neutral, e)) :: h0)) -> h0 = h')
            /\ ls ≃t(neutral, w) (inr (inr (neutral, e))) :: h'.
  Proof. 
    intros. specialize (@tape_repr_stay_right ls e h p w H) as (h' & H1 & H3 & H2). 
    exists (map polarityFlipGamma h'). rewrite <- and_assoc. split. 
    - apply tape_cover_symm3 in H1.
      eapply tape_cover_symm1 in H1.
      split. 
      + cbn [rev].
        unfold polarityRev in H1. rewrite map_involution in H1 by involution_simpl.  
        destruct e; cbn in H1; apply H1. 
      + intros. specialize (H3 (map polarityFlipGamma h0)).
        rewrite <- involution_invert_eqn2 with (f := map polarityFlipGamma) (a := h0) (b := h'); [reflexivity | involution_simpl | ].
        apply H3. eapply tape_cover_symm2. 
        unfold polarityRev. rewrite <- map_rev. apply tape_cover_symm3. 
        cbn. rewrite map_involution; [destruct e; cbn; now apply H0 | apply polarityFlipGamma_involution]. 
   - apply tape_repr_polarityFlip in H2. destruct e; cbn in H2; easy. 
  Qed. 

  (** ** Transition rules *)
  (** preliminaries *)

  Notation "s '≻' s'" := (halt (configState s) = false /\ sstep s = s') (at level 50). 

  (** decomposition into left, center, right *)
  Lemma tapeToList_lcr sig (tp : tape sig) : tapeToList tp = rev (left tp) ++ (match current tp with Some a => [a] | _ => [] end) ++ right tp. 
  Proof.
    clear_all. destruct tp; cbn. all: firstorder. now rewrite app_nil_r.   
  Qed. 

  Lemma sizeOfTape_lcr sig (tp : tape sig) : sizeOfTape tp = |left tp| + |right tp| + (if current tp then 1 else 0). 
  Proof. 
    unfold sizeOfTape. rewrite tapeToList_lcr. rewrite !app_length. rewrite rev_length. destruct current; cbn; lia. 
  Qed.

  (** simplification tactic for equations that arise from inversions*)
  Lemma prod_eq (X Y : Type) (a c : X) (b d : Y) : (a, b) = (c, d) -> a = c /\ b = d. 
  Proof. intros; split; congruence. Qed. 

  Proposition inl_injective (A B : Type) : forall (x y : A), inl B x = inl y -> x = y. 
  Proof. intros; congruence. Qed. 
  Proposition inr_injective (A B : Type) : forall (x y : B), inr A x = inr A y -> x = y. 
  Proof. intros; congruence. Qed. 
  Proposition Some_injective (A : Type) : forall (x y : A), Some x = Some y -> x = y. 
  Proof. intros; congruence. Qed. 

  Ltac simp_eqn := repeat match goal with
                          | [H : trans (?a, ?b) = ?h1, H1 : trans (?a, ?b) = ?h2 |- _] => assert (h1 = h2) by (now (rewrite <- H;rewrite <- H1)); clear H1
                          | [H : (?a, ?b) = (?c, ?d) |- _] => simple apply prod_eq in H as []
                          | [H : ?a = ?a |- _] => clear H
                          | [H : ?a = _ |- _] => is_var a; move a at bottom; subst a
                          | [H : Some ?a = Some ?b |- _] => apply Some_injective in H
                          | [H : inr ?a = inr ?b |- _] => apply inr_injective in H 
                          | [H : inl ?a = inl ?b |- _] => apply inl_injective in H 
                          | [H : ?h1 :: ?a = ?h2 :: ?b |- _] => apply Code.cons_injective in H as [? ?]
                          | [H : rev ?A = _ |- _ ] => is_var A; apply involution_invert_eqn2 in H as ?; [ | involution_simpl]; clear H
                          | [H : _ = rev ?A |- _ ] => is_var A; symmetry in H; apply involution_invert_eqn2 in H; [ | involution_simpl]
                          | [H : _ = ?a |- _] => is_var a; symmetry in H;move H at bottom; subst a
                          | [H : context[E _ (S _)] |- _] => cbn in H
                          | [H : context[E _ (wo + _)] |- _] => cbn in H
                    end; try congruence.


  (** again, we use inductive definitions *)
  Create HintDb trans discriminated. 
  Definition transRule := Gamma -> Gamma -> Gamma -> Gamma -> Gamma -> Gamma -> Prop.

  (** We structure the rules in several layers: first of all, we have to differentiate whether, for a transition, the Turing machine writes a symbol or not 
    (note that we take the view that the TM can write a symbol even if our transition function returns None (this just means that the symbol under the head remains unchanged) if there is currently a symbol under the head: in this case the written symbol is just the current symbol) 
    in the cases (Some, Some), (Some, None), (None, Some) (denoting the read/write positions of the transition function) the TM writes a symbol; only in the (None, None) case it does not write one 
  *)

  (** The rules are simplified and generate spurious cards which do not harm rewriting in any way.
    As long as the reprConfig invariant is fulfilled, the spurious cards cannot be applied.
  *)

  (**rules for the case where the Turing machine writes a symbol *)
  (**shift right rules *)
  (**order of additional arguments: current state, next state, read symbol, written symbol (does not match output of transition function!) *)
  Inductive transSomeRightCenter :  states -> states -> stateSigma -> stateSigma -> transRule :=
    | tsrc q q' (a b : stateSigma) (m1 m2 m3 : stateSigma) p : transSomeRightCenter q q' a b (inr (inr (p, m1))) (inl (q, a)) (inr (inr (p, m2))) (inr (inr (positive, m3))) (inl (q', m1)) (inr (inr (positive, b))).  

  Hint Constructors transSomeRightCenter : trans.
  (** We generate the inversion schemes for performance reasons. Sadly, they do not work as intended in Sections, we thus explicetly copy them and fix the Sigma & fTM-Parameter by hand. We also remove the predicate itself from the assumptions for each inversion case, to allow easier implementation of an repeating tactic. *)
  Derive Inversion transSomeRightCenter_inv' with (forall q q' a b γ1 γ2 γ3 γ4 γ5 γ6, transSomeRightCenter q q' a b γ1 γ2 γ3 γ4 γ5 γ6) Sort Prop.
  Definition transSomeRightCenter_inv (q q' : states) (a b : option Sigma) (γ1 γ2 γ3 γ4 γ5 γ6 : Gamma) (P : forall q q' a b γ1 γ2 γ3 γ4 γ5 γ6, Prop) :
       (forall (m1 m2 m3 : option Sigma) (p : polarity),
        inr (inr (p, m1)) = γ1 :> Gamma ->
        inl (q, a) = γ2 :> Gamma ->
        inr (inr (p, m2)) = γ3 :> Gamma ->
        inr (inr (↑ m3)) = γ4 :> Gamma ->
        inl (q', m1) = γ5 :> Gamma ->
        inr (inr (↑ b)) = γ6 :> Gamma ->
        P q q' a b (inr (inr (p, m1))) (inl (q, a)) (inr (inr (p, m2))) (inr (inr (↑ m3))) (inl (q', m1)) (inr (inr (↑ b)))) ->
       transSomeRightCenter q q' a b γ1 γ2 γ3 γ4 γ5 γ6 -> P q q' a b γ1 γ2 γ3 γ4 γ5 γ6.
  Proof.
    intros H ?. inversion H0;subst. eapply H. all:reflexivity.
  Qed.
  
  Inductive transSomeRightRight : states -> states -> stateSigma -> transRule :=
    | tsrr q q' (a : stateSigma) (m1 m2 m3 : stateSigma) p : transSomeRightRight q q' a (inr (inr (p, m1))) (inr (inr (p, m2))) (inl (q, a)) (inr (inr (positive, m3))) (inr (inr (positive, m1))) (inl (q', m2)). 

  Hint Constructors transSomeRightRight : trans.
  Derive Inversion transSomeRightRight_inv' with (forall q q' a γ1 γ2 γ3 γ4 γ5 γ6, transSomeRightRight q q' a γ1 γ2 γ3 γ4 γ5 γ6) Sort Prop.
  Definition transSomeRightRight_inv (q q' : states) (a : option Sigma) (γ1 γ2 γ3 γ4 γ5 γ6 : Gamma) (P : forall q q' a γ1 γ2 γ3 γ4 γ5 γ6, Prop) :
    (forall (m1 m2 m3 : option Sigma) (p : polarity),
       inr (inr (p, m1)) = γ1 :> Gamma ->
       inr (inr (p, m2)) = γ2 :> Gamma ->
       inl (q, a) = γ3 :> Gamma ->
       inr (inr (↑ m3)) = γ4 :> Gamma ->
       inr (inr (↑ m1)) = γ5 :> Gamma ->
       inl (q', m2) = γ6 :> Gamma ->
       P q q' a (inr (inr (p, m1))) (inr (inr (p, m2))) (inl (q, a)) 
         (inr (inr (↑ m3))) (inr (inr (↑ m1))) (inl (q', m2))) ->
    transSomeRightRight q q' a γ1 γ2 γ3 γ4 γ5 γ6 -> P q q' a γ1 γ2 γ3 γ4 γ5 γ6.
  Proof.
    intros H H0. inv H0.  eauto. 
  Qed.

  Inductive transSomeRightLeft : states -> states -> stateSigma -> stateSigma -> transRule :=
    | tsrl q q' (a b : stateSigma) (m1 m2 m3 : stateSigma) p: transSomeRightLeft q q' a b (inl (q, a)) (inr (inr (p, m1))) (inr (inr (p, m2))) (inl (q', m3)) (inr (inr (positive, b))) (inr (inr (positive, m1))). 

  Hint Constructors transSomeRightLeft : trans. 
  Derive Inversion transSomeRightLeft_inv' with (forall q q' a b γ1 γ2 γ3 γ4 γ5 γ6, transSomeRightLeft q q' a b γ1 γ2 γ3 γ4 γ5 γ6) Sort Prop.
  Definition transSomeRightLeft_inv (q q' : states) (a b: option Sigma) (γ1 γ2 γ3 γ4 γ5 γ6 : Gamma) (P : forall q q' a b γ1 γ2 γ3 γ4 γ5 γ6, Prop) :
    ( forall (m1 m2 m3 : option Sigma) (p : polarity),
        inl (q, a) = γ1 :> Gamma ->
        inr (inr (p, m1)) = γ2 :> Gamma ->
        inr (inr (p, m2)) = γ3 :> Gamma ->
        inl (q', m3) = γ4 :> Gamma ->
        inr (inr (↑ b)) = γ5 :> Gamma ->
        inr (inr (↑ m1)) = γ6 :> Gamma ->
        P q q' a b (inl (q, a)) (inr (inr (p, m1))) (inr (inr (p, m2))) 
          (inl (q', m3)) (inr (inr (↑ b))) (inr (inr (↑ m1)))) ->
    transSomeRightLeft q q' a b γ1 γ2 γ3 γ4 γ5 γ6 -> P q q' a b γ1 γ2 γ3 γ4 γ5 γ6.
  Proof.
    intros H H0. inv H0.  eauto. 
  Qed.

  (**shift left rules *)
  Inductive transSomeLeftCenter : states -> states -> stateSigma -> stateSigma -> transRule :=
    | tslc q q' (a b : stateSigma) (m1 m2 m3 : stateSigma) p : transSomeLeftCenter q q' a b (inr (inr (p, m1))) (inl (q, a)) (inr (inr (p, m2))) (inr (inr (negative, b))) (inl (q', m2)) (inr (inr (negative, m3))). 

  Hint Constructors transSomeLeftCenter : trans.
  Derive Inversion transSomeLeftCenter_inv' with (forall q q' a b γ1 γ2 γ3 γ4 γ5 γ6, transSomeLeftCenter q q' a b γ1 γ2 γ3 γ4 γ5 γ6) Sort Prop.
  Definition transSomeLeftCenter_inv (q q' : states) a b (γ1 γ2 γ3 γ4 γ5 γ6 : Gamma) (P : forall q q' a b γ1 γ2 γ3 γ4 γ5 γ6, Prop) :
     ( forall (m1 m2 m3 : option Sigma) (p : polarity),
        inr (inr (p, m1)) = γ1 :> Gamma ->
        inl (q, a) = γ2 :> Gamma ->
        inr (inr (p, m2)) = γ3 :> Gamma ->
        inr (inr (↓ b)) = γ4 :> Gamma ->
        inl (q', m2) = γ5 :> Gamma ->
        inr (inr (↓ m3)) = γ6 :> Gamma ->
        P q q' a b (inr (inr (p, m1))) (inl (q, a)) (inr (inr (p, m2))) 
          (inr (inr (↓ b))) (inl (q', m2)) (inr (inr (↓ m3)))) ->
    transSomeLeftCenter q q' a b γ1 γ2 γ3 γ4 γ5 γ6 -> P q q' a b γ1 γ2 γ3 γ4 γ5 γ6.
  Proof.
    intros H H0. inv H0.  eauto. 
  Qed.

  Inductive transSomeLeftLeft : states -> states -> stateSigma -> transRule :=
    | tsll q q' (a : stateSigma) (m1 m2 m3 : stateSigma) p : transSomeLeftLeft q q' a (inl (q, a)) (inr (inr (p, m1))) (inr (inr (p, m2))) (inl (q', m1)) (inr (inr (negative, m2))) (inr (inr(negative, m3))). 

  Hint Constructors transSomeLeftLeft : trans.
  Derive Inversion transSomeLeftLeft_inv' with (forall q q' a γ1 γ2 γ3 γ4 γ5 γ6, transSomeLeftLeft q q' a γ1 γ2 γ3 γ4 γ5 γ6) Sort Prop.
  Definition transSomeLeftLeft_inv (q q' : states) (a : option Sigma) (γ1 γ2 γ3 γ4 γ5 γ6 : Gamma) (P : forall q q' a γ1 γ2 γ3 γ4 γ5 γ6, Prop) :
    (forall (m1 m2 m3 : option Sigma) (p : polarity),
       inl (q, a) = γ1 :> Gamma ->
       inr (inr (p, m1)) = γ2 :> Gamma ->
       inr (inr (p, m2)) = γ3 :> Gamma ->
       inl (q', m1) = γ4 :> Gamma ->
       inr (inr (↓ m2)) = γ5 :> Gamma ->
       inr (inr (↓ m3)) = γ6 :> Gamma ->
       P q q' a (inl (q, a)) (inr (inr (p, m1))) (inr (inr (p, m2))) 
         (inl (q', m1)) (inr (inr (↓ m2))) (inr (inr (↓ m3)))) ->
    transSomeLeftLeft q q' a γ1 γ2 γ3 γ4 γ5 γ6 -> P q q' a γ1 γ2 γ3 γ4 γ5 γ6.
  Proof.
    intros H H0. inv H0.  eauto. 
  Qed.

  
  Inductive transSomeLeftRight : states -> states -> stateSigma -> stateSigma -> transRule :=
    | tslr q q' (a b : stateSigma) (m1 m2 m3 : stateSigma) p : transSomeLeftRight q q' a b (inr (inr (p, m1))) (inr (inr (p, m2))) (inl (q, a)) (inr (inr (negative, m2))) (inr (inr (negative, b))) (inl (q', m3)).

  Hint Constructors transSomeLeftRight : trans.
  Derive Inversion transSomeLeftRight_inv' with (forall q q' a b γ1 γ2 γ3 γ4 γ5 γ6, transSomeLeftRight q q' a b γ1 γ2 γ3 γ4 γ5 γ6) Sort Prop.
  Definition transSomeLeftRight_inv (q q' : states) a b (γ1 γ2 γ3 γ4 γ5 γ6 : Gamma) (P : forall q q' a b γ1 γ2 γ3 γ4 γ5 γ6, Prop) :
    ( forall (m1 m2 m3 : option Sigma) (p : polarity),
        inr (inr (p, m1)) = γ1 :> Gamma ->
        inr (inr (p, m2)) = γ2 :> Gamma ->
        inl (q, a) = γ3 :> Gamma ->
        inr (inr (↓ m2)) = γ4 :> Gamma ->
        inr (inr (↓ b)) = γ5 :> Gamma ->
        inl (q', m3) = γ6 :> Gamma ->
        P q q' a b (inr (inr (p, m1))) (inr (inr (p, m2))) (inl (q, a)) 
          (inr (inr (↓ m2))) (inr (inr (↓ b))) (inl (q', m3))) ->
    transSomeLeftRight q q' a b γ1 γ2 γ3 γ4 γ5 γ6 -> P q q' a b γ1 γ2 γ3 γ4 γ5 γ6.
  Proof.
    intros H H0. inv H0.  eauto. 
  Qed.
  
  (**stay rules *)
  
  Inductive transSomeStayCenter : states -> states -> stateSigma -> stateSigma -> transRule :=
  | tssc q q' (a b : stateSigma) (m1 m2 : stateSigma) p : transSomeStayCenter q q' a b (inr (inr (p, m1))) (inl (q, a)) (inr (inr (p, m2))) (inr (inr (neutral, m1))) (inl (q', b)) (inr (inr (neutral, m2))). 

  Hint Constructors transSomeStayCenter : trans.
  Derive Inversion transSomeStayCenter_inv' with (forall q q' a b γ1 γ2 γ3 γ4 γ5 γ6, transSomeStayCenter q q' a b γ1 γ2 γ3 γ4 γ5 γ6) Sort Prop.
  Definition transSomeStayCenter_inv (q q' : states) a b (γ1 γ2 γ3 γ4 γ5 γ6 : Gamma) (P : forall q q' a b γ1 γ2 γ3 γ4 γ5 γ6, Prop) :
    (forall (m1 m2 : option Sigma) (p : polarity),
       inr (inr (p, m1)) = γ1 :> Gamma ->
       inl (q, a) = γ2 :> Gamma ->
       inr (inr (p, m2)) = γ3 :> Gamma ->
       inr (inr (∘ m1)) = γ4 :> Gamma ->
       inl (q', b) = γ5 :> Gamma ->
       inr (inr (∘ m2)) = γ6 :> Gamma ->
       P q q' a b (inr (inr (p, m1))) (inl (q, a)) (inr (inr (p, m2))) 
         (inr (inr (∘ m1))) (inl (q', b)) (inr (inr (∘ m2))))  ->
    transSomeStayCenter q q' a b γ1 γ2 γ3 γ4 γ5 γ6 -> P q q' a b γ1 γ2 γ3 γ4 γ5 γ6.
  Proof.
    intros H H0. inv H0.  eauto. 
  Qed.

  Inductive transSomeStayLeft : states -> states -> stateSigma -> stateSigma -> transRule :=
    | tssl q q' (a b : stateSigma) (m1 m2 : stateSigma) p : transSomeStayLeft q q' a b (inl (q, a)) (inr (inr (p, m1))) (inr (inr (p, m2))) (inl (q', b)) (inr (inr (neutral, m1))) (inr (inr (neutral, m2))). 

  Hint Constructors transSomeStayLeft : trans.
  Derive Inversion transSomeStayLeft_inv' with (forall q q' a b γ1 γ2 γ3 γ4 γ5 γ6, transSomeStayLeft q q' a b γ1 γ2 γ3 γ4 γ5 γ6) Sort Prop.
  Definition transSomeStayLeft_inv (q q' : states) a b (γ1 γ2 γ3 γ4 γ5 γ6 : Gamma) (P : forall q q' a b γ1 γ2 γ3 γ4 γ5 γ6, Prop) :
    (forall (m1 m2 : option Sigma) (p : polarity),
       inl (q, a) = γ1 :> Gamma ->
       inr (inr (p, m1)) = γ2 :> Gamma ->
       inr (inr (p, m2)) = γ3 :> Gamma ->
       inl (q', b) = γ4 :> Gamma ->
       inr (inr (∘ m1)) = γ5 :> Gamma ->
       inr (inr (∘ m2)) = γ6 :> Gamma ->
       P q q' a b (inl (q, a)) (inr (inr (p, m1))) (inr (inr (p, m2))) 
         (inl (q', b)) (inr (inr (∘ m1))) (inr (inr (∘ m2)))) ->
    transSomeStayLeft q q' a b γ1 γ2 γ3 γ4 γ5 γ6 -> P q q' a b γ1 γ2 γ3 γ4 γ5 γ6.
  Proof.
    intros H H0. inv H0.  eauto.     
  Qed.

  Inductive transSomeStayRight : states -> states -> stateSigma -> stateSigma -> transRule :=
    | tssr q q' (a b : stateSigma) (m1 m2 : stateSigma) p : transSomeStayRight q q' a b (inr (inr (p, m1))) (inr (inr (p, m2))) (inl (q, a)) (inr (inr (neutral, m1))) (inr (inr (neutral, m2))) (inl (q', b)). 

  Hint Constructors transSomeStayRight : trans.
  Derive Inversion transSomeStayRight_inv' with (forall q q' a b γ1 γ2 γ3 γ4 γ5 γ6, transSomeStayRight q q' a b γ1 γ2 γ3 γ4 γ5 γ6) Sort Prop.
  Definition transSomeStayRight_inv (q q' : states) a b (γ1 γ2 γ3 γ4 γ5 γ6 : Gamma) (P : forall q q' a b γ1 γ2 γ3 γ4 γ5 γ6, Prop) :
    (forall (m1 m2 : option Sigma) (p : polarity),
       inr (inr (p, m1)) = γ1 :> Gamma ->
       inr (inr (p, m2)) = γ2 :> Gamma ->
       inl (q, a) = γ3 :> Gamma ->
       inr (inr (∘ m1)) = γ4 :> Gamma ->
       inr (inr (∘ m2)) = γ5 :> Gamma ->
       inl (q', b) = γ6 :> Gamma ->
       P q q' a b (inr (inr (p, m1))) 
         (inr (inr (p, m2))) (inl (q, a)) (inr (inr (∘ m1)))
         (inr (inr (∘ m2))) (inl (q', b))) ->
    transSomeStayRight q q' a b γ1 γ2 γ3 γ4 γ5 γ6 -> P q q' a b γ1 γ2 γ3 γ4 γ5 γ6.
  Proof.
    intros H H0. inv H0.  eauto. 
  Qed.

  (** bundling predicates *)

  (** we first group together according to where the state symbol is: left/right/center *)
  (** note that we have to differentiate between the three cases (Some, Some), (Some, None), (None, Some) *)

  (** Some, Some *)
  Inductive transSomeSomeLeft : states -> transRule :=
  | transSSLeftLeftC q q' (a b : Sigma) γ2 γ3 γ4 γ5 γ6: trans (q, Some a) = (q', (Some b, Rmove)) -> transSomeLeftLeft q q' (Some a) (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6 -> transSomeSomeLeft q (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6
  | transSSRightLeftC q q' (a b : Sigma) γ2 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some b, Lmove)) ->  transSomeRightLeft q q' (Some a) (Some b) (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6 -> transSomeSomeLeft q (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6
  | transSSStayLeftC q q' (a b : Sigma) γ2 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some b, Nmove)) -> transSomeStayLeft q q' (Some a) (Some b) (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6 -> transSomeSomeLeft q (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6. 

  Hint Constructors transSomeSomeLeft : trans.
  Derive Inversion transSomeSomeLeft_inv' with (forall q γ1 γ2 γ3 γ4 γ5 γ6, transSomeSomeLeft q γ1 γ2 γ3 γ4 γ5 γ6) Sort Prop.
  Definition transSomeSomeLeft_inv (q : states) (γ1 γ2 γ3 γ4 γ5 γ6 : Gamma) (P : forall q γ1 γ2 γ3 γ4 γ5 γ6, Prop) :
    (forall (q' : states) (a b : Sigma),
       trans (q, Some a) = (q', (Some b, positive)) ->
       transSomeLeftLeft q q' (Some a) (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6 ->
       inl (q, Some a) = γ1 :> Gamma -> P q (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6) ->
    (forall (q' : states) (a b : Sigma),
       trans (q, Some a) = (q', (Some b, negative)) ->
       transSomeRightLeft q q' (Some a) (Some b) (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6 ->
       inl (q, Some a) = γ1 :> Gamma -> P q (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6) ->
    (forall (q' : states) (a b : Sigma),
       trans (q, Some a) = (q', (Some b, neutral)) ->
       transSomeStayLeft q q' (Some a) (Some b) (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6 ->
       inl (q, Some a) = γ1 :> Gamma -> P q (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6) ->
    transSomeSomeLeft q γ1 γ2 γ3 γ4 γ5 γ6 -> P q γ1 γ2 γ3 γ4 γ5 γ6.
  Proof.
    intros ? ? ? H0. inv H0. all:eauto.     
  Qed.

  Inductive transSomeSomeRight : states -> transRule :=
  | transSSLeftRightC q q' (a b: Sigma) γ1 γ2 γ4 γ5 γ6: trans (q, Some a) = (q', (Some b, Rmove)) -> transSomeLeftRight q q' (Some a) (Some b) γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6 -> transSomeSomeRight q γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6
  | transSSRightRightC q q' (a b : Sigma) γ1 γ2 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some b, Lmove)) -> transSomeRightRight q q' (Some a) γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6 -> transSomeSomeRight q γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6
  | transSSStayRightC q q' (a b : Sigma)  γ1 γ2 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some b, Nmove)) -> transSomeStayRight q q' (Some a) (Some b) γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6 -> transSomeSomeRight q γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6. 

  Hint Constructors transSomeSomeRight : trans.
  Derive Inversion transSomeSomeRight_inv' with (forall q γ1 γ2 γ3 γ4 γ5 γ6, transSomeSomeRight q γ1 γ2 γ3 γ4 γ5 γ6) Sort Prop.
  Definition transSomeSomeRight_inv (q : states) (γ1 γ2 γ3 γ4 γ5 γ6 : Gamma) (P : forall q γ1 γ2 γ3 γ4 γ5 γ6, Prop) :
    (forall (q' : states) (a b : Sigma),
        trans (q, Some a) = (q', (Some b, positive)) ->
        transSomeLeftRight q q' (Some a) (Some b) γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6 ->
        inl (q, Some a) = γ3 :> Gamma -> P q γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6) ->
    (forall (q' : states) (a b : Sigma),
       trans (q, Some a) = (q', (Some b, negative)) ->
       transSomeRightRight q q' (Some a) γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6 ->
       inl (q, Some a) = γ3 :> Gamma -> P q γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6) ->
    (forall (q' : states) (a b : Sigma),
       trans (q, Some a) = (q', (Some b, neutral)) ->
       transSomeStayRight q q' (Some a) (Some b) γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6 ->
       inl (q, Some a) = γ3 :> Gamma -> P q γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6) ->
    transSomeSomeRight q γ1 γ2 γ3 γ4 γ5 γ6 -> P q γ1 γ2 γ3 γ4 γ5 γ6.
  Proof.
    intros ? ? ? H0. inv H0. all:eauto.     
  Qed.

  Inductive transSomeSomeCenter : states -> transRule :=
  | transSSLeftCenterC q q' (a b: Sigma) γ1 γ3 γ4 γ5 γ6: trans (q, Some a) = (q', (Some b, Rmove)) -> transSomeLeftCenter q q' (Some a) (Some b) γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6 -> transSomeSomeCenter q γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6
  | transSSRightCenterC q q' (a b: Sigma) γ1 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some b, Lmove)) -> transSomeRightCenter q q' (Some a) (Some b) γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6 -> transSomeSomeCenter q γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6
  | transSSStayCenterC q q' (a b: Sigma) γ1 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some b, Nmove)) -> transSomeStayCenter q q' (Some a) (Some b) γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6 -> transSomeSomeCenter q γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6. 

  Hint Constructors transSomeSomeCenter : trans.
  Derive Inversion transSomeSomeCenter_inv' with (forall q γ1 γ2 γ3 γ4 γ5 γ6, transSomeSomeCenter q γ1 γ2 γ3 γ4 γ5 γ6) Sort Prop.
  Definition transSomeSomeCenter_inv (q : states) (γ1 γ2 γ3 γ4 γ5 γ6 : Gamma) (P : forall q γ1 γ2 γ3 γ4 γ5 γ6, Prop) :
    ( forall (q' : states) (a b : Sigma),
        trans (q, Some a) = (q', (Some b, positive)) ->
        transSomeLeftCenter q q' (Some a) (Some b) γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6 ->
        inl (q, Some a) = γ2 :> Gamma -> P q γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6) ->
    ( forall (q' : states) (a b : Sigma),
       trans (q, Some a) = (q', (Some b, negative)) ->
       transSomeRightCenter q q' (Some a) (Some b) γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6 ->
       inl (q, Some a) = γ2 :> Gamma ->P q γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6) ->
    ( forall (q' : states) (a b : Sigma),
       trans (q, Some a) = (q', (Some b, neutral)) ->
       transSomeStayCenter q q' (Some a) (Some b) γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6 ->
       inl (q, Some a) = γ2 :> Gamma -> P q γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6) ->
    transSomeSomeCenter q γ1 γ2 γ3 γ4 γ5 γ6 -> P q γ1 γ2 γ3 γ4 γ5 γ6.
  Proof.
    intros ? ? ? H0. inv H0. all:eauto.     
  Qed.
  
  (** None, Some *)
  Inductive transNoneSomeLeft : states -> transRule :=
  | transNSLeftLeftC q q' (b : Sigma) γ2 γ3 γ4 γ5 γ6: trans (q, None) = (q', (Some b, Rmove)) -> transSomeLeftLeft q q' |_| (inl (q, |_|)) γ2 γ3 γ4 γ5 γ6 -> transNoneSomeLeft q (inl (q, |_|)) γ2 γ3 γ4 γ5 γ6
  | transNSRightLeftC q q' (b : Sigma) γ2 γ3 γ4 γ5 γ6 : trans (q, |_|) = (q', (Some b, Lmove)) ->  transSomeRightLeft q q' (|_|) (Some b) (inl (q, |_|)) γ2 γ3 γ4 γ5 γ6 -> transNoneSomeLeft q (inl (q, |_|)) γ2 γ3 γ4 γ5 γ6
  | transNSStayLeftC q q' (b : Sigma) γ2 γ3 γ4 γ5 γ6 : trans (q, |_|) = (q', (Some b, Nmove)) -> transSomeStayLeft q q' (|_|) (Some b) (inl (q, |_|)) γ2 γ3 γ4 γ5 γ6 -> transNoneSomeLeft q (inl (q, |_|)) γ2 γ3 γ4 γ5 γ6. 

  Hint Constructors transNoneSomeLeft : trans.
  Derive Inversion transNoneSomeLeft_inv' with (forall q γ1 γ2 γ3 γ4 γ5 γ6, transNoneSomeLeft q γ1 γ2 γ3 γ4 γ5 γ6) Sort Prop.
  Definition transNoneSomeLeft_inv (q : states) (γ1 γ2 γ3 γ4 γ5 γ6 : Gamma) (P : forall q γ1 γ2 γ3 γ4 γ5 γ6, Prop) :
    ( forall (q' : states) (b : Sigma),
        trans (q, (|_|)) = (q', (Some b, positive)) ->
        transSomeLeftLeft q q' (|_|) (inl (q, (|_|))) γ2 γ3 γ4 γ5 γ6 ->
        inl (q, (|_|)) = γ1 :> Gamma -> P q (inl (q, (|_|))) γ2 γ3 γ4 γ5 γ6) ->
    (forall (q' : states) (b : Sigma),
        trans (q, (|_|)) = (q', (Some b, negative)) ->
        transSomeRightLeft q q' (|_|) (Some b) (inl (q, (|_|))) γ2 γ3 γ4 γ5 γ6 ->
        inl (q, (|_|)) = γ1 :> Gamma -> P q (inl (q, (|_|))) γ2 γ3 γ4 γ5 γ6) ->
    (forall (q' : states) (b : Sigma),
        trans (q, (|_|)) = (q', (Some b, neutral)) ->
        transSomeStayLeft q q' (|_|) (Some b) (inl (q, (|_|))) γ2 γ3 γ4 γ5 γ6 ->
        inl (q, (|_|)) = γ1 :> Gamma -> P q (inl (q, (|_|))) γ2 γ3 γ4 γ5 γ6) ->
    transNoneSomeLeft q γ1 γ2 γ3 γ4 γ5 γ6 -> P q γ1 γ2 γ3 γ4 γ5 γ6.
  Proof.
    intros ? ? ? H0. inv H0. all:eauto.     
  Qed.

  Inductive transNoneSomeRight : states -> transRule :=
  | transNSLeftRightC q q' (b: Sigma) γ1 γ2 γ4 γ5 γ6: trans (q, |_|) = (q', (Some b, Rmove)) -> transSomeLeftRight q q' (|_|) (Some b) γ1 γ2 (inl (q, |_|)) γ4 γ5 γ6 -> transNoneSomeRight q γ1 γ2 (inl (q, |_|)) γ4 γ5 γ6
  | transNSRightRightC q q' (b : Sigma) γ1 γ2 γ4 γ5 γ6 : trans (q, |_|) = (q', (Some b, Lmove)) -> transSomeRightRight q q' (|_|) γ1 γ2 (inl (q, |_|)) γ4 γ5 γ6 -> transNoneSomeRight q γ1 γ2 (inl (q, |_|)) γ4 γ5 γ6
  | transNSStayRightC q q' (b : Sigma)  γ1 γ2 γ4 γ5 γ6 : trans (q, |_|) = (q', (Some b, Nmove)) -> transSomeStayRight q q' (|_|) (Some b) γ1 γ2 (inl (q, |_|)) γ4 γ5 γ6 -> transNoneSomeRight q γ1 γ2 (inl (q, |_|)) γ4 γ5 γ6. 

  Hint Constructors transNoneSomeRight : trans.
  Derive Inversion transNoneSomeRight_inv' with (forall q γ1 γ2 γ3 γ4 γ5 γ6, transNoneSomeRight q γ1 γ2 γ3 γ4 γ5 γ6) Sort Prop.
  Definition transNoneSomeRight_inv (q : states) (γ1 γ2 γ3 γ4 γ5 γ6 : Gamma) (P : forall q γ1 γ2 γ3 γ4 γ5 γ6, Prop) :
    (forall (q' : states) (b : Sigma),
        trans (q, (|_|)) = (q', (Some b, positive)) ->
        transSomeLeftRight q q' (|_|) (Some b) γ1 γ2 (inl (q, (|_|))) γ4 γ5 γ6 ->
        inl (q, (|_|)) = γ3 :> Gamma -> P q γ1 γ2 (inl (q, (|_|))) γ4 γ5 γ6) ->
    (forall (q' : states) (b : Sigma),
        trans (q, (|_|)) = (q', (Some b, negative)) ->
        transSomeRightRight q q' (|_|) γ1 γ2 (inl (q, (|_|))) γ4 γ5 γ6 ->
        inl (q, (|_|)) = γ3 :> Gamma -> P q γ1 γ2 (inl (q, (|_|))) γ4 γ5 γ6) ->
    (forall (q' : states) (b : Sigma),
        trans (q, (|_|)) = (q', (Some b, neutral)) ->
        transSomeStayRight q q' (|_|) (Some b) γ1 γ2 (inl (q, (|_|))) γ4 γ5 γ6 ->
        inl (q, (|_|)) = γ3 :> Gamma -> P q γ1 γ2 (inl (q, (|_|))) γ4 γ5 γ6) ->
    transNoneSomeRight q γ1 γ2 γ3 γ4 γ5 γ6 -> P q γ1 γ2 γ3 γ4 γ5 γ6.
  Proof.
    intros ? ? ? H0. inv H0. all:eauto.     
  Qed.

  Inductive transNoneSomeCenter : states -> transRule :=
  | transNSLeftCenterC q q' (b: Sigma) γ1 γ3 γ4 γ5 γ6: trans (q, |_|) = (q', (Some b, Rmove)) -> transSomeLeftCenter q q' (|_|) (Some b) γ1 (inl (q, |_|)) γ3 γ4 γ5 γ6 -> transNoneSomeCenter q γ1 (inl (q, |_|)) γ3 γ4 γ5 γ6
  | transNSRightCenterC q q' (b: Sigma) γ1 γ3 γ4 γ5 γ6 : trans (q, |_|) = (q', (Some b, Lmove)) -> transSomeRightCenter q q' (|_|) (Some b) γ1 (inl (q, |_|)) γ3 γ4 γ5 γ6 -> transNoneSomeCenter q γ1 (inl (q, |_|)) γ3 γ4 γ5 γ6
  | transNSStayCenterC q q' (b: Sigma) γ1 γ3 γ4 γ5 γ6 : trans (q, |_|) = (q', (Some b, Nmove)) -> transSomeStayCenter q q' (|_|) (Some b) γ1 (inl (q, |_|)) γ3 γ4 γ5 γ6 -> transNoneSomeCenter q γ1 (inl (q, |_|)) γ3 γ4 γ5 γ6. 

  Hint Constructors transNoneSomeCenter : trans.
  Derive Inversion transNoneSomeCenter_inv' with (forall q γ1 γ2 γ3 γ4 γ5 γ6, transNoneSomeCenter q γ1 γ2 γ3 γ4 γ5 γ6) Sort Prop.
  Definition transNoneSomeCenter_inv (q : states) (γ1 γ2 γ3 γ4 γ5 γ6 : Gamma) (P : forall q γ1 γ2 γ3 γ4 γ5 γ6, Prop) :
    (forall (q' : states) (b : Sigma),
        trans (q, (|_|)) = (q', (Some b, positive)) ->
        transSomeLeftCenter q q' (|_|) (Some b) γ1 (inl (q, (|_|))) γ3 γ4 γ5 γ6 ->
        inl (q, (|_|)) = γ2 :> Gamma -> P q γ1 (inl (q, (|_|))) γ3 γ4 γ5 γ6) ->
    ( forall (q' : states) (b : Sigma),
        trans (q, (|_|)) = (q', (Some b, negative)) ->
        transSomeRightCenter q q' (|_|) (Some b) γ1 (inl (q, (|_|))) γ3 γ4 γ5 γ6 ->
        inl (q, (|_|)) = γ2 :> Gamma -> P q γ1 (inl (q, (|_|))) γ3 γ4 γ5 γ6) ->
    ( forall (q' : states) (b : Sigma),
        trans (q, (|_|)) = (q', (Some b, neutral)) ->
        transSomeStayCenter q q' (|_|) (Some b) γ1 (inl (q, (|_|))) γ3 γ4 γ5 γ6 ->
        inl (q, (|_|)) = γ2 :> Gamma -> P q γ1 (inl (q, (|_|))) γ3 γ4 γ5 γ6)  ->
    transNoneSomeCenter q γ1 γ2 γ3 γ4 γ5 γ6 -> P q γ1 γ2 γ3 γ4 γ5 γ6.
  Proof.
    intros ? ? ? H0. inv H0. all:eauto.     
  Qed.

  (** Some, None  *)
  Inductive transSomeNoneLeft : states -> transRule :=
  | transSNLeftLeftC q q' (a : Sigma) γ2 γ3 γ4 γ5 γ6: trans (q, Some a) = (q', (None, Rmove)) -> transSomeLeftLeft q q' (Some a) (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6 -> transSomeNoneLeft q (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6
  | transSNRightLeftC q q' (a : Sigma) γ2 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (None, Lmove)) ->  transSomeRightLeft q q' (Some a) (Some a) (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6 -> transSomeNoneLeft q (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6
  | transSNStayLeftC q q' (a : Sigma) γ2 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (None, Nmove)) -> transSomeStayLeft q q' (Some a) (Some a) (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6 -> transSomeNoneLeft q (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6. 

  Hint Constructors transSomeNoneLeft : trans.
  Derive Inversion transSomeNoneLeft_inv' with (forall q γ1 γ2 γ3 γ4 γ5 γ6, transSomeNoneLeft q γ1 γ2 γ3 γ4 γ5 γ6) Sort Prop.
  Definition transSomeNoneLeft_inv (q : states) (γ1 γ2 γ3 γ4 γ5 γ6 : Gamma) (P : forall q γ1 γ2 γ3 γ4 γ5 γ6, Prop) :
    ( forall (q' : states) (a : Sigma),
        trans (q, Some a) = (q', ((|_|), positive)) ->
        transSomeLeftLeft q q' (Some a) (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6 ->
        inl (q, Some a) = γ1 :> Gamma ->
        P q (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6) ->
    (forall (q' : states) (a : Sigma),
        trans (q, Some a) = (q', ((|_|), negative)) ->
        transSomeRightLeft q q' (Some a) (Some a) 
                           (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6 ->
        inl (q, Some a) = γ1 :> Gamma ->
        P q (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6) ->
    (forall (q' : states) (a : Sigma),
        trans (q, Some a) = (q', ((|_|), neutral)) ->
        transSomeStayLeft q q' (Some a) (Some a) 
                          (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6 ->
        inl (q, Some a) = γ1 :> Gamma ->
        P q (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6) ->
    transSomeNoneLeft q γ1 γ2 γ3 γ4 γ5 γ6 -> P q γ1 γ2 γ3 γ4 γ5 γ6.
  Proof.
    intros ? ? ? H0. inv H0. all:eauto.     
  Qed.

  Inductive transSomeNoneRight : states -> transRule :=
  | transSNLeftRightC q q' (a : Sigma) γ1 γ2 γ4 γ5 γ6: trans (q, Some a) = (q', (None, Rmove)) -> transSomeLeftRight q q' (Some a) (Some a) γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6 -> transSomeNoneRight q γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6
  | transSNRightRightC q q' (a : Sigma) γ1 γ2 γ4 γ5 γ6 : trans (q, Some a) = (q', (None, Lmove)) -> transSomeRightRight q q' (Some a) γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6 -> transSomeNoneRight q γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6
  | transSNStayRightC q q' (a : Sigma)  γ1 γ2 γ4 γ5 γ6 : trans (q, Some a) = (q', (None, Nmove)) -> transSomeStayRight q q' (Some a) (Some a) γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6 -> transSomeNoneRight q γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6. 

  Hint Constructors transSomeNoneRight : trans.
  Derive Inversion transSomeNoneRight_inv' with (forall q γ1 γ2 γ3 γ4 γ5 γ6, transSomeNoneRight q γ1 γ2 γ3 γ4 γ5 γ6) Sort Prop.
  Definition transSomeNoneRight_inv (q : states) (γ1 γ2 γ3 γ4 γ5 γ6 : Gamma) (P : forall q γ1 γ2 γ3 γ4 γ5 γ6, Prop) :
    (forall (q' : states) (a : Sigma),
        trans (q, Some a) = (q', ((|_|), positive)) ->
        transSomeLeftRight q q' (Some a) (Some a) γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6 ->
        inl (q, Some a) = γ3 :> Gamma -> P q γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6) ->
    (forall (q' : states) (a : Sigma),
        trans (q, Some a) = (q', ((|_|), negative)) ->
        transSomeRightRight q q' (Some a) γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6 ->
        inl (q, Some a) = γ3 :> Gamma -> P q γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6) ->
    (forall (q' : states) (a : Sigma),
        trans (q, Some a) = (q', ((|_|), neutral)) ->
        transSomeStayRight q q' (Some a) (Some a) γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6 ->
        inl (q, Some a) = γ3 :> Gamma ->P q γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6) -> 
    transSomeNoneRight q γ1 γ2 γ3 γ4 γ5 γ6 -> P q γ1 γ2 γ3 γ4 γ5 γ6.
  Proof.
    intros ? ? ? H0. inv H0. all:eauto.     
  Qed.

  Inductive transSomeNoneCenter : states -> transRule :=
  | transSNLeftCenterC q q' (a: Sigma) γ1 γ3 γ4 γ5 γ6: trans (q, Some a) = (q', (None, Rmove)) -> transSomeLeftCenter q q' (Some a) (Some a) γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6 -> transSomeNoneCenter q γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6
  | transSNRightCenterC q q' (a: Sigma) γ1 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (None, Lmove)) -> transSomeRightCenter q q' (Some a) (Some a) γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6 -> transSomeNoneCenter q γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6
  | transSNStayCenterC q q' (a: Sigma) γ1 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (None, Nmove)) -> transSomeStayCenter q q' (Some a) (Some a) γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6 -> transSomeNoneCenter q γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6. 

  Hint Constructors transSomeNoneCenter : trans.
  Derive Inversion transSomeNoneCenter_inv' with (forall q γ1 γ2 γ3 γ4 γ5 γ6, transSomeNoneCenter q γ1 γ2 γ3 γ4 γ5 γ6) Sort Prop.
  Definition transSomeNoneCenter_inv (q : states) (γ1 γ2 γ3 γ4 γ5 γ6 : Gamma) (P : forall q γ1 γ2 γ3 γ4 γ5 γ6, Prop) :
    (forall (q' : states) (a : Sigma),
        trans (q, Some a) = (q', ((|_|), positive)) ->
        transSomeLeftCenter q q' (Some a) (Some a) γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6 ->
        inl (q, Some a) = γ2 :> Gamma -> P q γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6) ->
    ( forall (q' : states) (a : Sigma),
        trans (q, Some a) = (q', ((|_|), negative)) ->
        transSomeRightCenter q q' (Some a) (Some a) γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6 ->
        inl (q, Some a) = γ2 :> Gamma -> P q γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6) ->
    (forall (q' : states) (a : Sigma),
        trans (q, Some a) = (q', ((|_|), neutral)) ->
        transSomeStayCenter q q' (Some a) (Some a) γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6 ->
        inl (q, Some a) = γ2 :> Gamma -> P q γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6) ->
    transSomeNoneCenter q γ1 γ2 γ3 γ4 γ5 γ6 -> P q γ1 γ2 γ3 γ4 γ5 γ6.
  Proof.
    intros ? ? ? H0. inv H0. all:eauto.     
  Qed.
  
  (** finally, also group those three cases together *)
  Inductive transSomeSome : states -> transRule :=
  | transSSLeft q γ1 γ2 γ3 γ4 γ5 γ6 : transSomeSomeLeft q γ1 γ2 γ3 γ4 γ5 γ6 -> transSomeSome q γ1 γ2 γ3 γ4 γ5 γ6
  | transSSRight q γ1 γ2 γ3 γ4 γ5 γ6 : transSomeSomeRight q γ1 γ2 γ3 γ4 γ5 γ6 -> transSomeSome q γ1 γ2 γ3 γ4 γ5 γ6
  | transSSCenter q γ1 γ2 γ3 γ4 γ5 γ6 : transSomeSomeCenter q γ1 γ2 γ3 γ4 γ5 γ6 -> transSomeSome q γ1 γ2 γ3 γ4 γ5 γ6.

  Hint Constructors transSomeSome : trans.
  Derive Inversion_clear transSomeSome_inv' with (forall q γ1 γ2 γ3 γ4 γ5 γ6, transSomeSome q γ1 γ2 γ3 γ4 γ5 γ6) Sort Prop.
  Definition transSomeSome_inv (q : states) (γ1 γ2 γ3 γ4 γ5 γ6 : Gamma) (P : forall q γ1 γ2 γ3 γ4 γ5 γ6, Prop) :
    (transSomeSomeLeft q γ1 γ2 γ3 γ4 γ5 γ6 -> P q γ1 γ2 γ3 γ4 γ5 γ6) ->
    (transSomeSomeRight q γ1 γ2 γ3 γ4 γ5 γ6 -> P q γ1 γ2 γ3 γ4 γ5 γ6) ->
    (transSomeSomeCenter q γ1 γ2 γ3 γ4 γ5 γ6 -> P q γ1 γ2 γ3 γ4 γ5 γ6) ->
    transSomeSome q γ1 γ2 γ3 γ4 γ5 γ6 -> P q γ1 γ2 γ3 γ4 γ5 γ6.
  Proof.
    intros ? ? ? H0. inv H0. all:eauto.     
  Qed.

  Inductive transNoneSome : states -> transRule :=
  | transNSLeft q γ1 γ2 γ3 γ4 γ5 γ6 : transNoneSomeLeft q γ1 γ2 γ3 γ4 γ5 γ6 -> transNoneSome q γ1 γ2 γ3 γ4 γ5 γ6
  | transNSRight q γ1 γ2 γ3 γ4 γ5 γ6 : transNoneSomeRight q γ1 γ2 γ3 γ4 γ5 γ6 -> transNoneSome q γ1 γ2 γ3 γ4 γ5 γ6
  | transNSCenter q γ1 γ2 γ3 γ4 γ5 γ6 : transNoneSomeCenter q γ1 γ2 γ3 γ4 γ5 γ6 -> transNoneSome q γ1 γ2 γ3 γ4 γ5 γ6.

  Hint Constructors transNoneSome : trans.
  Derive Inversion_clear transNoneSome_inv' with (forall q γ1 γ2 γ3 γ4 γ5 γ6, transNoneSome q γ1 γ2 γ3 γ4 γ5 γ6) Sort Prop.
  Definition transNoneSome_inv (q : states) (γ1 γ2 γ3 γ4 γ5 γ6 : Gamma) (P : forall q γ1 γ2 γ3 γ4 γ5 γ6, Prop) :
    (transNoneSomeLeft q γ1 γ2 γ3 γ4 γ5 γ6 -> P q γ1 γ2 γ3 γ4 γ5 γ6) ->
    (transNoneSomeRight q γ1 γ2 γ3 γ4 γ5 γ6 -> P q γ1 γ2 γ3 γ4 γ5 γ6) ->
    (transNoneSomeCenter q γ1 γ2 γ3 γ4 γ5 γ6 -> P q γ1 γ2 γ3 γ4 γ5 γ6) ->
    transNoneSome q γ1 γ2 γ3 γ4 γ5 γ6 -> P q γ1 γ2 γ3 γ4 γ5 γ6.
  Proof.
    intros ? ? ? H0. inv H0. all:eauto.     
  Qed.
  
  Inductive transSomeNone : states -> transRule :=
  | transSNLeft q γ1 γ2 γ3 γ4 γ5 γ6 : transSomeNoneLeft q γ1 γ2 γ3 γ4 γ5 γ6 -> transSomeNone q γ1 γ2 γ3 γ4 γ5 γ6
  | transSNRight q γ1 γ2 γ3 γ4 γ5 γ6 : transSomeNoneRight q γ1 γ2 γ3 γ4 γ5 γ6 -> transSomeNone q γ1 γ2 γ3 γ4 γ5 γ6
  | transSNCenter q γ1 γ2 γ3 γ4 γ5 γ6 : transSomeNoneCenter q γ1 γ2 γ3 γ4 γ5 γ6 -> transSomeNone q γ1 γ2 γ3 γ4 γ5 γ6.

  Hint Constructors transSomeNone : trans.
  Derive Inversion_clear transSomeNone_inv' with (forall q γ1 γ2 γ3 γ4 γ5 γ6, transSomeNone q γ1 γ2 γ3 γ4 γ5 γ6) Sort Prop.
  Definition transSomeNone_inv (q : states) (γ1 γ2 γ3 γ4 γ5 γ6 : Gamma) (P : forall q γ1 γ2 γ3 γ4 γ5 γ6, Prop) :
    (transSomeNoneLeft q γ1 γ2 γ3 γ4 γ5 γ6 -> P q γ1 γ2 γ3 γ4 γ5 γ6) ->
    (transSomeNoneRight q γ1 γ2 γ3 γ4 γ5 γ6 -> P q γ1 γ2 γ3 γ4 γ5 γ6) ->
    (transSomeNoneCenter q γ1 γ2 γ3 γ4 γ5 γ6 -> P q γ1 γ2 γ3 γ4 γ5 γ6) ->
    transSomeNone q γ1 γ2 γ3 γ4 γ5 γ6 -> P q γ1 γ2 γ3 γ4 γ5 γ6.
  Proof.
    intros ? ? ? H0. inv H0. all:eauto.     
  Qed.

  (**the special case of (None, None) needs extra care as the Turing machine doesn't write any symbol *) 
  (**the structure of the rules is the same for this case, but we need a more fine-grained definition of the base rules because of the special handling if we are at the border of the visited tape region *)

  (**shift right rules *)
  Inductive transNoneRightCenter :  states -> states -> transRule :=
  | tnrc1 q q' (m : stateSigma) p : transNoneRightCenter q q' (inr (inr (p, |_|))) (inl (q, |_|)) (inr (inr (p, m))) (inr (inr (neutral, |_|))) (inl (q', |_|)) (inr (inr (neutral, m)))
  | tnrc2 q q' (σ : Sigma) (m: stateSigma) p : transNoneRightCenter q q' (inr (inr (p, Some σ))) (inl (q, |_|)) (inr (inr (p, |_|))) (inr (inr (positive, m))) (inl (q', Some σ)) (inr (inr (positive, |_|))). 

  Hint Constructors transNoneRightCenter : trans. 
  Derive Inversion transNoneRightCenter_inv' with (forall q q' γ1 γ2 γ3 γ4 γ5 γ6, transNoneRightCenter q q' γ1 γ2 γ3 γ4 γ5 γ6) Sort Prop.
  Definition transNoneRightCenter_inv (q q' : states) (γ1 γ2 γ3 γ4 γ5 γ6 : Gamma) (P : forall q q' γ1 γ2 γ3 γ4 γ5 γ6, Prop) :
    (forall (m : option Sigma) (p : polarity),
        inr (inr (p, (|_|))) = γ1 :> Gamma ->
        inl (q, (|_|)) = γ2 :> Gamma ->
        inr (inr (p, m)) = γ3 :> Gamma ->
        inr (inr (∘ (|_|))) = γ4 :> Gamma ->
        inl (q', (|_|)) = γ5 :> Gamma ->
        inr (inr (∘ m)) = γ6 :> Gamma ->
        P q q' (inr (inr (p, (|_|)))) (inl (q, (|_|))) (inr (inr (p, m)))
          (inr (inr (∘ (|_|)))) (inl (q', (|_|))) (inr (inr (∘ m)))) ->
    (forall (σ : Sigma) (m : option Sigma) (p : polarity),
        inr (inr (p, Some σ)) = γ1 :> Gamma ->
        inl (q, (|_|)) = γ2 :> Gamma ->
        inr (inr (p, (|_|))) = γ3 :> Gamma ->
        inr (inr (↑ m)) = γ4 :> Gamma ->
        inl (q', Some σ) = γ5 :> Gamma ->
        inr (inr (↑ (|_|))) = γ6 :> Gamma ->
        P q q' (inr (inr (p, Some σ))) (inl (q, (|_|))) (inr (inr (p, (|_|))))
          (inr (inr (↑ m))) (inl (q', Some σ)) (inr (inr (↑ (|_|))))) ->
    transNoneRightCenter q q' γ1 γ2 γ3 γ4 γ5 γ6 -> P q q' γ1 γ2 γ3 γ4 γ5 γ6.
  Proof.
    intros ? ? H0. inv H0. all:eauto.     
  Qed.
  
  Inductive transNoneRightRight : states -> states -> transRule :=
  | tnrr1 q q' p p': transNoneRightRight q q' (inr (inr (p, |_|))) (inr (inr (p, |_|))) (inl (q, |_|)) (inr (inr (p', |_|))) (inr (inr (p', |_|))) (inl (q', |_|))
  | tnrr2 q q' σ p p': transNoneRightRight q q' (inr (inr (p, |_|))) (inr (inr (p,Some σ))) (inl (q, |_|)) (inr (inr (p', |_|))) (inr (inr (p', |_|))) (inl (q', Some σ))
  | tnrr3 q q' σ1 σ2 (m1 : stateSigma) p : transNoneRightRight q q' (inr (inr (p, Some σ1))) (inr (inr (p, Some σ2))) (inl (q, |_|)) (inr (inr (positive, m1))) (inr (inr (positive, Some σ1))) (inl (q', Some σ2)).

  Hint Constructors transNoneRightRight : trans. 
  Derive Inversion transNoneRightRight_inv' with (forall q q' γ1 γ2 γ3 γ4 γ5 γ6, transNoneRightRight q q' γ1 γ2 γ3 γ4 γ5 γ6) Sort Prop.
  Definition transNoneRightRight_inv (q q' : states) (γ1 γ2 γ3 γ4 γ5 γ6 : Gamma) (P : forall q q' γ1 γ2 γ3 γ4 γ5 γ6, Prop) :
    (forall (p p' : polarity),
        inr (inr (p, |_|)) = γ1 :> Gamma ->
        inr (inr (p, |_|)) = γ2 :> Gamma ->
        inl (q, |_|) = γ3 :> Gamma ->
        inr (inr (p', |_|)) = γ4 :> Gamma ->
        inr (inr (p', |_|)) = γ5 :> Gamma ->
        inl (q', |_|) = γ6 :> Gamma ->
        P q q' (inr (inr (p, |_|))) (inr (inr (p, |_|))) (inl (q, |_|))
          (inr (inr (p', |_|))) (inr (inr (p', |_|))) (inl (q', |_|))) ->
    (forall (σ : Sigma) (p p' : polarity),
        inr (inr (p, |_|)) = γ1 :> Gamma ->
        inr (inr (p, Some σ)) = γ2 :> Gamma ->
        inl (q, |_|) = γ3 :> Gamma ->
        inr (inr (p', |_|)) = γ4 :> Gamma ->
        inr (inr (p', |_|)) = γ5 :> Gamma ->
        inl (q', Some σ) = γ6 :> Gamma ->
        P q q' (inr (inr (p, |_|))) (inr (inr (p, Some σ))) 
          (inl (q, |_|)) (inr (inr (p', |_|))) (inr (inr (p', |_|))) (inl (q', Some σ))) ->
    (forall (σ1 σ2 : Sigma) (m1 : option Sigma) (p : polarity),
        inr (inr (p, Some σ1)) = γ1 :> Gamma ->
        inr (inr (p, Some σ2)) = γ2 :> Gamma ->
        inl (q, |_|) = γ3 :> Gamma ->
        inr (inr (↑ m1)) = γ4 :> Gamma ->
        inr (inr (↑ Some σ1)) = γ5 :> Gamma ->
        inl (q', Some σ2) = γ6 :> Gamma ->
        P q q' (inr (inr (p, Some σ1))) (inr (inr (p, Some σ2))) 
          (inl (q, |_|)) (inr (inr (↑ m1))) (inr (inr (↑ Some σ1))) (inl (q', Some σ2))) ->
    transNoneRightRight q q' γ1 γ2 γ3 γ4 γ5 γ6 -> P q q' γ1 γ2 γ3 γ4 γ5 γ6.
  Proof.
    intros ? ? ? H0. inv H0. all:eauto.     
  Qed.
  
  Inductive transNoneRightLeft : states -> states -> transRule :=
  | tnrl1 q q' (m : stateSigma) p p': transNoneRightLeft q q' (inl (q, |_|)) (inr (inr (p, |_|))) (inr (inr (p, |_|))) (inl (q', m)) (inr (inr (p', |_|))) (inr (inr (p', |_|)))
  | tnrl2 q q' (m : stateSigma) σ p p' : transNoneRightLeft q q' (inl (q, |_|)) (inr (inr (p, Some σ))) (inr (inr (p, m))) (inl (q', |_|)) (inr (inr (p', Some σ))) (inr (inr (p', m))).  

  Hint Constructors transNoneRightLeft : trans. 
  Derive Inversion transNoneRightLeft_inv' with (forall q q' γ1 γ2 γ3 γ4 γ5 γ6, transNoneRightLeft q q' γ1 γ2 γ3 γ4 γ5 γ6) Sort Prop.
  Definition transNoneRightLeft_inv (q q' : states) (γ1 γ2 γ3 γ4 γ5 γ6 : Gamma) (P : forall q q' γ1 γ2 γ3 γ4 γ5 γ6, Prop) :
    (forall (m : option Sigma) (p p': polarity),
        inl (q, |_|) = γ1 :> Gamma ->
        inr (inr (p, |_|)) = γ2 :> Gamma ->
        inr (inr (p, |_|)) = γ3 :> Gamma ->
        inl (q', m) = γ4 :> Gamma ->
        inr (inr (p', |_|)) = γ5 :> Gamma ->
        inr (inr (p', |_|)) = γ6 :> Gamma ->
        P q q' (inl (q, |_|)) (inr (inr (p, |_|))) (inr (inr (p, |_|))) 
          (inl (q', m)) (inr (inr (p', |_|))) (inr (inr (p', |_|)))) ->
    (forall (m : option Sigma) (σ : Sigma) (p p' : polarity),
        inl (q, |_|) = γ1 :> Gamma ->
        inr (inr (p, Some σ)) = γ2 :> Gamma ->
        inr (inr (p, m)) = γ3 :> Gamma ->
        inl (q', |_|) = γ4 :> Gamma ->
        inr (inr (p', Some σ)) = γ5 :> Gamma ->
        inr (inr (p', m)) = γ6 :> Gamma ->
        P q q' (inl (q, |_|)) (inr (inr (p, Some σ))) (inr (inr (p, m))) 
          (inl (q', |_|)) (inr (inr (p', Some σ))) (inr (inr (p', m)))) ->
    transNoneRightLeft q q' γ1 γ2 γ3 γ4 γ5 γ6 -> P q q' γ1 γ2 γ3 γ4 γ5 γ6.
  Proof.
    intros ? ? H0. inv H0. all:eauto.     
  Qed.
  
  (**shift left rules *)
  Inductive transNoneLeftCenter : states -> states -> transRule :=
  | tnlc1 q q' (m : stateSigma) p : transNoneLeftCenter q q' (inr (inr (p, m))) (inl (q, |_|)) (inr (inr (p, |_|))) (inr (inr (neutral, m))) (inl (q', |_|)) (inr (inr (neutral, |_|)))
  | tnlc2 q q' (m : stateSigma) σ p : transNoneLeftCenter q q' (inr (inr (p, |_|))) (inl (q, |_|)) (inr (inr (p, Some σ))) (inr (inr (negative, |_|))) (inl (q', Some σ)) (inr (inr (negative, m))). 

  Hint Constructors transNoneLeftCenter : trans. 
  Derive Inversion transNoneLeftCenter_inv' with (forall q q' γ1 γ2 γ3 γ4 γ5 γ6, transNoneLeftCenter q q' γ1 γ2 γ3 γ4 γ5 γ6) Sort Prop.
  Definition transNoneLeftCenter_inv (q q' : states) (γ1 γ2 γ3 γ4 γ5 γ6 : Gamma) (P : forall q q' γ1 γ2 γ3 γ4 γ5 γ6, Prop) :
    (forall  (m : option Sigma) (p : polarity),
        inr (inr (p, m)) = γ1 :> Gamma ->
        inl (q, |_|) = γ2 :> Gamma ->
        inr (inr (p, |_|)) = γ3 :> Gamma ->
        inr (inr (∘ m)) = γ4 :> Gamma ->
        inl (q', |_|) = γ5 :> Gamma ->
        inr (inr (∘ |_|)) = γ6 :> Gamma ->
        P  q q' (inr (inr (p, m))) (inl (q, |_|)) (inr (inr (p, |_|))) 
           (inr (inr (∘ m))) (inl (q', |_|)) (inr (inr (∘ |_|)))) ->
    ( forall (m : option Sigma) (σ : Sigma) (p : polarity),
        inr (inr (p, |_|)) = γ1 :> Gamma ->
        inl (q, |_|) = γ2 :> Gamma ->
        inr (inr (p, Some σ)) = γ3 :> Gamma ->
        inr (inr (↓ |_|)) = γ4 :> Gamma ->
        inl (q', Some σ) = γ5 :> Gamma ->
        inr (inr (↓ m)) = γ6 :> Gamma ->
        P q q' (inr (inr (p, |_|))) (inl (q, |_|)) (inr (inr (p, Some σ)))
          (inr (inr (↓ |_|))) (inl (q', Some σ)) (inr (inr (↓ m)))) -> 
    transNoneLeftCenter q q' γ1 γ2 γ3 γ4 γ5 γ6 -> P q q' γ1 γ2 γ3 γ4 γ5 γ6.
  Proof.
    intros ? ? H0. inv H0. all:eauto.     
  Qed.
  
  Inductive transNoneLeftLeft : states -> states -> transRule :=
  | tnll1 q q' p p': transNoneLeftLeft q q' (inl (q, |_|)) (inr (inr (p, |_|))) (inr (inr (p, |_|))) (inl (q', |_|)) (inr (inr (p', |_|))) (inr (inr (p', |_|)))
  | tnll2 q q' σ p p': transNoneLeftLeft q q' (inl (q, |_|)) (inr (inr (p, Some σ))) (inr (inr (p, |_|))) (inl (q', Some σ)) (inr (inr (p', |_|))) (inr (inr (p', |_|)))
  | tnll3 q q' σ1 σ2 (m : stateSigma) p : transNoneLeftLeft q q' (inl (q, |_|)) (inr (inr (p, Some σ1))) (inr (inr (p, Some σ2))) (inl (q', Some σ1)) (inr (inr (negative, Some σ2))) (inr (inr (negative, m))).

  Hint Constructors transNoneLeftLeft : trans.
  Derive Inversion transNoneLeftLeft_inv' with (forall q q' γ1 γ2 γ3 γ4 γ5 γ6, transNoneLeftLeft q q' γ1 γ2 γ3 γ4 γ5 γ6) Sort Prop.
  Definition transNoneLeftLeft_inv (q q' : states) (γ1 γ2 γ3 γ4 γ5 γ6 : Gamma) (P : forall q q' γ1 γ2 γ3 γ4 γ5 γ6, Prop) :
    (forall (p p' : polarity),
        inl (q, |_|) = γ1 :> Gamma ->
        inr (inr (p, |_|)) = γ2 :> Gamma ->
        inr (inr (p, |_|)) = γ3 :> Gamma ->
        inl (q', |_|) = γ4 :> Gamma ->
        inr (inr (p', |_|)) = γ5 :> Gamma ->
        inr (inr (p', |_|)) = γ6 :> Gamma ->
        P q q' (inl (q, |_|)) (inr (inr (p, |_|))) (inr (inr (p, |_|))) 
          (inl (q', |_|)) (inr (inr (p', |_|))) (inr (inr (p', |_|)))) ->
    (forall (σ : Sigma) (p p' : polarity),
        inl (q, |_|) = γ1 :> Gamma ->
        inr (inr (p, Some σ)) = γ2 :> Gamma ->
        inr (inr (p, |_|)) = γ3 :> Gamma ->
        inl (q', Some σ) = γ4 :> Gamma ->
        inr (inr (p', |_|)) = γ5 :> Gamma ->
        inr (inr (p', |_|)) = γ6 :> Gamma ->
        P q q' (inl (q, |_|)) (inr (inr (p, Some σ))) (inr (inr (p, |_|)))
          (inl (q', Some σ)) (inr (inr (p', |_|))) (inr (inr (p', |_|)))) ->
    ( forall (σ1 σ2 : Sigma) (m : option Sigma) (p : polarity),
        inl (q, |_|) = γ1 :> Gamma ->
        inr (inr (p, Some σ1)) = γ2 :> Gamma ->
        inr (inr (p, Some σ2)) = γ3 :> Gamma ->
        inl (q', Some σ1) = γ4 :> Gamma ->
        inr (inr (↓ Some σ2)) = γ5 :> Gamma ->
        inr (inr (↓ m)) = γ6 :> Gamma ->
        P q q' (inl (q, |_|)) (inr (inr (p, Some σ1))) (inr (inr (p, Some σ2)))
          (inl (q', Some σ1)) (inr (inr (↓ Some σ2))) (inr (inr (↓ m)))) ->
    transNoneLeftLeft q q' γ1 γ2 γ3 γ4 γ5 γ6 -> P q q' γ1 γ2 γ3 γ4 γ5 γ6.
  Proof.
    intros ? ? ? H0. inv H0. all:eauto.     
  Qed.

  Inductive transNoneLeftRight : states -> states -> transRule :=
  | tnlr1 q q' (m : stateSigma) p p': transNoneLeftRight q q' (inr (inr (p,  |_|))) (inr (inr (p, |_|))) (inl (q, |_|)) (inr (inr (p', |_|))) (inr (inr (p', |_|))) (inl (q', m))
  | tnlr2 q q' (m1 : stateSigma) σ p : transNoneLeftRight q q' (inr (inr (p, m1))) (inr (inr (p, Some σ))) (inl (q, |_|)) (inr (inr (neutral, m1))) (inr (inr (neutral, Some σ))) (inl (q', |_|)). 

  Hint Constructors transNoneLeftRight : trans. 
  Derive Inversion transNoneLeftRight_inv' with (forall q q' γ1 γ2 γ3 γ4 γ5 γ6, transNoneLeftRight q q' γ1 γ2 γ3 γ4 γ5 γ6) Sort Prop.
  Definition transNoneLeftRight_inv (q q' : states) (γ1 γ2 γ3 γ4 γ5 γ6 : Gamma) (P : forall q q' γ1 γ2 γ3 γ4 γ5 γ6, Prop) :
    (forall (m : option Sigma) (p p' : polarity),
        inr (inr (p, |_|)) = γ1 :> Gamma ->
        inr (inr (p, |_|)) = γ2 :> Gamma ->
        inl (q, |_|) = γ3 :> Gamma ->
        inr (inr (p', |_|)) = γ4 :> Gamma ->
        inr (inr (p', |_|)) = γ5 :> Gamma ->
        inl (q', m) = γ6 :> Gamma ->
        P q q' (inr (inr (p, |_|))) (inr (inr (p, |_|))) (inl (q, |_|))
          (inr (inr (p', |_|))) (inr (inr (p', |_|))) (inl (q', m))) ->
    (forall (m1 : option Sigma) (σ : Sigma) (p : polarity),
        inr (inr (p, m1)) = γ1 :> Gamma ->
        inr (inr (p, Some σ)) = γ2 :> Gamma ->
        inl (q, |_|) = γ3 :> Gamma ->
        inr (inr (∘ m1)) = γ4 :> Gamma ->
        inr (inr (∘ Some σ)) = γ5 :> Gamma ->
        inl (q', |_|) = γ6 :> Gamma ->
        P q q' (inr (inr (p, m1))) (inr (inr (p, Some σ))) (inl (q, |_|))
          (inr (inr (∘ m1))) (inr (inr (∘ Some σ))) (inl (q', |_|))) ->
    transNoneLeftRight q q' γ1 γ2 γ3 γ4 γ5 γ6 -> P q q' γ1 γ2 γ3 γ4 γ5 γ6.
  Proof.
    intros ? ? H0. inv H0. all:eauto.     
  Qed.
  
  (**stay rules *)
  Inductive transNoneStayCenter : states -> states -> transRule :=
  | tnsc1 q q' (m : stateSigma) p : transNoneStayCenter q q' (inr (inr (p, m))) (inl (q, |_|)) (inr (inr (p, |_|))) (inr (inr (neutral, m))) (inl (q', |_|)) (inr (inr (neutral, |_|)))
  | tnsc2 q q' (m : stateSigma) p : transNoneStayCenter q q' (inr (inr (p, |_|))) (inl (q, |_|)) (inr (inr (p, m))) (inr (inr (neutral, |_|))) (inl (q', |_|)) (inr (inr (neutral, m))). 

  Hint Constructors transNoneStayCenter : trans.
  Derive Inversion transNoneStayCenter_inv' with (forall q q' γ1 γ2 γ3 γ4 γ5 γ6, transNoneStayCenter q q' γ1 γ2 γ3 γ4 γ5 γ6) Sort Prop.
  Definition transNoneStayCenter_inv (q q' : states) (γ1 γ2 γ3 γ4 γ5 γ6 : Gamma) (P : forall q q' γ1 γ2 γ3 γ4 γ5 γ6, Prop) :
    (forall  (m : option Sigma) (p : polarity),
        inr (inr (p, m)) = γ1 :> Gamma ->
        inl (q, |_|) = γ2 :> Gamma ->
        inr (inr (p, |_|)) = γ3 :> Gamma ->
        inr (inr (∘ m)) = γ4 :> Gamma ->
        inl (q', |_|) = γ5 :> Gamma ->
        inr (inr (∘ |_|)) = γ6 :> Gamma ->
        P q q' (inr (inr (p, m))) (inl (q, |_|)) (inr (inr (p, |_|))) 
          (inr (inr (∘ m))) (inl (q', |_|)) (inr (inr (∘ |_|)))) ->
    (forall (m : option Sigma) (p : polarity),
        inr (inr (p, |_|)) = γ1 :> Gamma ->
        inl (q, |_|) = γ2 :> Gamma ->
        inr (inr (p, m)) = γ3 :> Gamma ->
        inr (inr (∘ |_|)) = γ4 :> Gamma ->
        inl (q', |_|) = γ5 :> Gamma ->
        inr (inr (∘ m)) = γ6 :> Gamma ->
        P q q' (inr (inr (p, |_|))) (inl (q, |_|)) (inr (inr (p, m)))
          (inr (inr (∘ |_|))) (inl (q', |_|)) (inr (inr (∘ m)))) ->
    transNoneStayCenter q q' γ1 γ2 γ3 γ4 γ5 γ6 -> P q q' γ1 γ2 γ3 γ4 γ5 γ6.
  Proof.
    intros ? ? H0. inv H0. all:eauto.     
  Qed.

  Inductive transNoneStayLeft : states -> states -> transRule :=
  | tnsl1 q q' σ (m : stateSigma) p : transNoneStayLeft q q' (inl (q, |_|)) (inr (inr (p, Some σ))) (inr (inr (p, m))) (inl (q', |_|)) (inr (inr (neutral, Some σ))) (inr (inr (neutral, m)))
  | tnsl2 q q' p: transNoneStayLeft q q' (inl (q, |_|)) (inr (inr (p, |_|))) (inr (inr (p, |_|))) (inl (q', |_|)) (inr (inr (neutral, |_|))) (inr (inr (neutral, |_|))).

  Hint Constructors transNoneStayLeft : trans.
  Derive Inversion transNoneStayLeft_inv' with (forall q q' γ1 γ2 γ3 γ4 γ5 γ6, transNoneStayLeft q q' γ1 γ2 γ3 γ4 γ5 γ6) Sort Prop.
  Definition transNoneStayLeft_inv (q q' : states) (γ1 γ2 γ3 γ4 γ5 γ6 : Gamma) (P : forall q q' γ1 γ2 γ3 γ4 γ5 γ6, Prop) :
    (forall (σ : Sigma) (m : option Sigma) (p : polarity),
        inl (q, |_|) = γ1 :> Gamma ->
        inr (inr (p, Some σ)) = γ2 :> Gamma ->
        inr (inr (p, m)) = γ3 :> Gamma ->
        inl (q', |_|) = γ4 :> Gamma ->
        inr (inr (∘ Some σ)) = γ5 :> Gamma ->
        inr (inr (∘ m)) = γ6 :> Gamma ->
        P q q' (inl (q, |_|)) (inr (inr (p, Some σ))) (inr (inr (p, m))) 
          (inl (q', |_|)) (inr (inr (∘ Some σ))) (inr (inr (∘ m)))) ->
    (forall (p : polarity),
        inl (q, |_|) = γ1 :> Gamma ->
        inr (inr (p, |_|)) = γ2 :> Gamma ->
        inr (inr (p, |_|)) = γ3 :> Gamma ->
        inl (q', |_|) = γ4 :> Gamma ->
        inr (inr (∘ |_|)) = γ5 :> Gamma ->
        inr (inr (∘ |_|)) = γ6 :> Gamma ->
        P q q' (inl (q, |_|)) (inr (inr (p, |_|))) (inr (inr (p, |_|))) 
          (inl (q', |_|)) (inr (inr (∘ |_|))) (inr (inr (∘ |_|)))) ->
    transNoneStayLeft q q' γ1 γ2 γ3 γ4 γ5 γ6 -> P q q' γ1 γ2 γ3 γ4 γ5 γ6.
  Proof.
    intros ? ? H0. inv H0. all:eauto.     
  Qed.

  Inductive transNoneStayRight : states -> states ->  transRule :=
  | tnsr1 q q' σ (m : stateSigma) p : transNoneStayRight q q' (inr (inr (p, m))) (inr (inr (p, Some σ))) (inl (q, |_|)) (inr (inr (neutral, m))) (inr (inr (neutral, Some σ))) (inl (q', |_|))
  | tnsr2 q q' p : transNoneStayRight q q' (inr (inr (p, |_|))) (inr (inr (p, |_|))) (inl (q, |_|)) (inr (inr (neutral, |_|))) (inr (inr (neutral, |_|))) (inl (q', |_|)). 

  Hint Constructors transNoneStayRight : trans. 
  Derive Inversion transNoneStayRight_inv' with (forall q q' γ1 γ2 γ3 γ4 γ5 γ6, transNoneStayRight q q' γ1 γ2 γ3 γ4 γ5 γ6) Sort Prop.
  Definition transNoneStayRight_inv (q q' : states) (γ1 γ2 γ3 γ4 γ5 γ6 : Gamma) (P : forall q q' γ1 γ2 γ3 γ4 γ5 γ6, Prop) :
    (forall (σ : Sigma) (m : option Sigma) (p : polarity),
        inr (inr (p, m)) = γ1 :> Gamma ->
        inr (inr (p, Some σ)) = γ2 :> Gamma ->
        inl (q, |_|) = γ3 :> Gamma ->
        inr (inr (∘ m)) = γ4 :> Gamma ->
        inr (inr (∘ Some σ)) = γ5 :> Gamma ->
        inl (q', |_|) = γ6 :> Gamma ->
        P q q' (inr (inr (p, m))) (inr (inr (p, Some σ))) (inl (q, |_|))
          (inr (inr (∘ m))) (inr (inr (∘ Some σ))) (inl (q', |_|))) ->
    (forall (p : polarity),
        inr (inr (p, |_|)) = γ1 :> Gamma ->
        inr (inr (p, |_|)) = γ2 :> Gamma ->
        inl (q, |_|) = γ3 :> Gamma ->
        inr (inr (∘ |_|)) = γ4 :> Gamma ->
        inr (inr (∘ |_|)) = γ5 :> Gamma ->
        inl (q', |_|) = γ6 :> Gamma ->
        P q q' (inr (inr (p, |_|))) (inr (inr (p, |_|))) (inl (q, |_|))
          (inr (inr (∘ |_|))) (inr (inr (∘ |_|))) (inl (q', |_|))) ->
    transNoneStayRight q q' γ1 γ2 γ3 γ4 γ5 γ6 -> P q q' γ1 γ2 γ3 γ4 γ5 γ6.
  Proof.
    intros ? ? H0. inv H0. all:eauto.     
  Qed.
  
  Inductive transNoneNoneLeft : states -> transRule :=
  | transNNLeftLeftC q q' γ2 γ3 γ4 γ5 γ6: trans (q, None) = (q', (None, Rmove)) -> transNoneLeftLeft q q' (inl (q, |_|)) γ2 γ3 γ4 γ5 γ6 -> transNoneNoneLeft q (inl (q, |_|)) γ2 γ3 γ4 γ5 γ6
  | transNNRightLeftC q q' γ2 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (None, Lmove)) ->  transNoneRightLeft q q' (inl (q, |_|)) γ2 γ3 γ4 γ5 γ6 -> transNoneNoneLeft q (inl (q, |_|)) γ2 γ3 γ4 γ5 γ6
  | transNNCenterLeftC q q' γ2 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (None, Nmove)) -> transNoneStayLeft q q' (inl (q, |_|)) γ2 γ3 γ4 γ5 γ6 -> transNoneNoneLeft q (inl (q, |_|)) γ2 γ3 γ4 γ5 γ6. 

  Hint Constructors transNoneNoneLeft : trans.
  Derive Inversion transNoneNoneLeft_inv' with (forall q γ1 γ2 γ3 γ4 γ5 γ6, transNoneNoneLeft q γ1 γ2 γ3 γ4 γ5 γ6) Sort Prop.
  Definition transNoneNoneLeft_inv (q : states) (γ1 γ2 γ3 γ4 γ5 γ6 : Gamma) (P : forall q γ1 γ2 γ3 γ4 γ5 γ6, Prop) :
    (forall (q' : states),
        trans (q, |_|) = (q', (|_|, positive)) ->
        transNoneLeftLeft q q' (inl (q, |_|)) γ2 γ3 γ4 γ5 γ6 ->
        inl (q, |_|) = γ1 :> Gamma -> P q (inl (q, |_|)) γ2 γ3 γ4 γ5 γ6) ->
    (forall (q' : states),
        trans (q, |_|) = (q', (|_|, negative)) ->
        transNoneRightLeft q q' (inl (q, |_|)) γ2 γ3 γ4 γ5 γ6 ->
        inl (q, |_|) = γ1 :> Gamma ->P q (inl (q, |_|)) γ2 γ3 γ4 γ5 γ6) ->
    (forall (q' : states),
        trans (q, |_|) = (q', (|_|, neutral)) ->
        transNoneStayLeft q q' (inl (q, |_|)) γ2 γ3 γ4 γ5 γ6 ->
        inl (q, |_|) = γ1 :> Gamma -> P q (inl (q, |_|)) γ2 γ3 γ4 γ5 γ6) ->
    transNoneNoneLeft q γ1 γ2 γ3 γ4 γ5 γ6 -> P q γ1 γ2 γ3 γ4 γ5 γ6.
  Proof.
    intros ? ? ? H0. inv H0. all:eauto.     
  Qed.
  

  Inductive transNoneNoneRight : states -> transRule :=
  | transNNLeftRightC q q' γ1 γ2 γ4 γ5 γ6: trans (q, None) = (q', (None, Rmove)) -> transNoneLeftRight q q' γ1 γ2 (inl (q, |_|)) γ4 γ5 γ6 -> transNoneNoneRight q γ1 γ2 (inl (q, |_|)) γ4 γ5 γ6
  | transNNRightRightC q q' γ1 γ2 γ4 γ5 γ6 : trans (q, None) = (q', (None, Lmove)) -> transNoneRightRight q q' γ1 γ2 (inl (q, |_|)) γ4 γ5 γ6 -> transNoneNoneRight q γ1 γ2 (inl (q, |_|)) γ4 γ5 γ6
  | transNNCenterRightC q q' γ1 γ2 γ4 γ5 γ6 : trans (q, None) = (q', (None, Nmove)) -> transNoneStayRight q q' γ1 γ2 (inl (q, |_|)) γ4 γ5 γ6 -> transNoneNoneRight q γ1 γ2 (inl (q, |_|)) γ4 γ5 γ6. 

  Hint Constructors transNoneNoneRight : trans. 
  Derive Inversion transNoneNoneRight_inv' with (forall q γ1 γ2 γ3 γ4 γ5 γ6, transNoneNoneRight q γ1 γ2 γ3 γ4 γ5 γ6) Sort Prop.
  Definition transNoneNoneRight_inv (q : states) (γ1 γ2 γ3 γ4 γ5 γ6 : Gamma) (P : forall q γ1 γ2 γ3 γ4 γ5 γ6, Prop) :
    (forall (q' : states),
        trans (q, |_|) = (q', (|_|, positive)) ->
        transNoneLeftRight q q' γ1 γ2 (inl (q, |_|)) γ4 γ5 γ6 ->
        inl (q, |_|) = γ3 :> Gamma -> P q γ1 γ2 (inl (q, |_|)) γ4 γ5 γ6) ->
    (forall (q' : states),
        trans (q, |_|) = (q', (|_|, negative)) ->
        transNoneRightRight q q' γ1 γ2 (inl (q, |_|)) γ4 γ5 γ6 ->
        inl (q, |_|) = γ3 :> Gamma -> P q γ1 γ2 (inl (q, |_|)) γ4 γ5 γ6) ->
    (forall (q' : states),
        trans (q, |_|) = (q', (|_|, neutral)) ->
        transNoneStayRight q q' γ1 γ2 (inl (q, |_|)) γ4 γ5 γ6 ->
        inl (q, |_|) = γ3 :> Gamma -> P q γ1 γ2 (inl (q, |_|)) γ4 γ5 γ6) ->
    transNoneNoneRight q γ1 γ2 γ3 γ4 γ5 γ6 -> P q γ1 γ2 γ3 γ4 γ5 γ6.
  Proof.
    intros ? ? ? H0. inv H0. all:eauto.     
  Qed.
  
  Inductive transNoneNoneCenter : states -> transRule :=
  | transNNLeftCenterC q q' γ1 γ3 γ4 γ5 γ6: trans (q, None) = (q', (None, Rmove)) -> transNoneLeftCenter q q' γ1 (inl (q, |_|)) γ3 γ4 γ5 γ6 -> transNoneNoneCenter q γ1 (inl (q, |_|)) γ3 γ4 γ5 γ6
  | transNNRightCenterC q q' γ1 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (None, Lmove)) -> transNoneRightCenter q q' γ1 (inl (q, |_|)) γ3 γ4 γ5 γ6 -> transNoneNoneCenter q γ1 (inl (q, |_|)) γ3 γ4 γ5 γ6
  | transNNCenterCenterC q q' γ1 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (None, Nmove)) -> transNoneStayCenter q q' γ1 (inl (q, |_|)) γ3 γ4 γ5 γ6 -> transNoneNoneCenter q γ1 (inl (q, |_|)) γ3 γ4 γ5 γ6. 

  Hint Constructors transNoneNoneCenter : trans. 
  Derive Inversion transNoneNoneCenter_inv' with (forall q γ1 γ2 γ3 γ4 γ5 γ6, transNoneNoneCenter q γ1 γ2 γ3 γ4 γ5 γ6) Sort Prop.
  Definition transNoneNoneCenter_inv (q : states) (γ1 γ2 γ3 γ4 γ5 γ6 : Gamma) (P : forall q γ1 γ2 γ3 γ4 γ5 γ6, Prop) :
    (forall (q' : states),
        trans (q, |_|) = (q', (|_|, positive)) ->
        transNoneLeftCenter q q' γ1 (inl (q, |_|)) γ3 γ4 γ5 γ6 ->
        inl (q, |_|) = γ2 :> Gamma -> P q γ1 (inl (q, |_|)) γ3 γ4 γ5 γ6) ->
    (forall (q' : states),
        trans (q, |_|) = (q', (|_|, negative)) ->
        transNoneRightCenter q q' γ1 (inl (q, |_|)) γ3 γ4 γ5 γ6 ->
        inl (q, |_|) = γ2 :> Gamma -> P q γ1 (inl (q, |_|)) γ3 γ4 γ5 γ6) ->
    (forall (q' : states),
        trans (q, |_|) = (q', (|_|, neutral)) ->
        transNoneStayCenter q q' γ1 (inl (q, |_|)) γ3 γ4 γ5 γ6 ->
        inl (q, |_|) = γ2 :> Gamma -> P q γ1 (inl (q, |_|)) γ3 γ4 γ5 γ6) ->
    transNoneNoneCenter q γ1 γ2 γ3 γ4 γ5 γ6 -> P q γ1 γ2 γ3 γ4 γ5 γ6.
  Proof.
    intros ? ? ? H0. inv H0. all:eauto.     
  Qed.

  
  Inductive transNoneNone : states -> transRule :=
  | transNNLeft q γ1 γ2 γ3 γ4 γ5 γ6 : transNoneNoneLeft q γ1 γ2 γ3 γ4 γ5 γ6 -> transNoneNone q γ1 γ2 γ3 γ4 γ5 γ6
  | transNNRight q γ1 γ2 γ3 γ4 γ5 γ6 : transNoneNoneRight q γ1 γ2 γ3 γ4 γ5 γ6 -> transNoneNone q γ1 γ2 γ3 γ4 γ5 γ6
  | transNNCenter q γ1 γ2 γ3 γ4 γ5 γ6 : transNoneNoneCenter q γ1 γ2 γ3 γ4 γ5 γ6 -> transNoneNone q γ1 γ2 γ3 γ4 γ5 γ6.

  Hint Constructors transNoneNone : trans. 
  Derive Inversion_clear transNoneNone_inv' with (forall q γ1 γ2 γ3 γ4 γ5 γ6, transNoneNone q γ1 γ2 γ3 γ4 γ5 γ6) Sort Prop.
  Definition transNoneNone_inv (q : states) (γ1 γ2 γ3 γ4 γ5 γ6 : Gamma) (P : forall q γ1 γ2 γ3 γ4 γ5 γ6, Prop) :
    (transNoneNoneLeft q γ1 γ2 γ3 γ4 γ5 γ6 -> P q γ1 γ2 γ3 γ4 γ5 γ6) ->
    (transNoneNoneRight q γ1 γ2 γ3 γ4 γ5 γ6 -> P q γ1 γ2 γ3 γ4 γ5 γ6) ->
    (transNoneNoneCenter q γ1 γ2 γ3 γ4 γ5 γ6 -> P q γ1 γ2 γ3 γ4 γ5 γ6) ->
    transNoneNone q γ1 γ2 γ3 γ4 γ5 γ6 -> P q γ1 γ2 γ3 γ4 γ5 γ6.
  Proof.
    intros ? ? ? H0. inv H0. all:eauto.     
  Qed.
  
  (** finally, group together all of the four cases *)
  Inductive transRules  : transRule :=
  | transSomeSomeC q γ1 γ2 γ3 γ4 γ5 γ6: halt q = false -> transSomeSome q γ1 γ2 γ3 γ4 γ5 γ6 -> transRules γ1 γ2 γ3 γ4 γ5 γ6
  | transSomeNoneC q γ1 γ2 γ3 γ4 γ5 γ6 : halt q = false -> transSomeNone q γ1 γ2 γ3 γ4 γ5 γ6 -> transRules γ1 γ2 γ3 γ4 γ5 γ6
  | transNoneSomeC q γ1 γ2 γ3 γ4 γ5 γ6 : halt q = false -> transNoneSome q γ1 γ2 γ3 γ4 γ5 γ6 -> transRules γ1 γ2 γ3 γ4 γ5 γ6
  | transNoneNoneC q γ1 γ2 γ3 γ4 γ5 γ6 : halt q = false -> transNoneNone q γ1 γ2 γ3 γ4 γ5 γ6 -> transRules γ1 γ2 γ3 γ4 γ5 γ6.

  Hint Constructors transRules : trans.
  Derive Inversion_clear transRules_inv' with (forall γ1 γ2 γ3 γ4 γ5 γ6, transRules γ1 γ2 γ3 γ4 γ5 γ6) Sort Prop.
  Definition transRules_inv (γ1 γ2 γ3 γ4 γ5 γ6 : Gamma) (P : forall γ1 γ2 γ3 γ4 γ5 γ6, Prop) :
    (forall q, halt q = false -> transSomeSome q γ1 γ2 γ3 γ4 γ5 γ6 -> P γ1 γ2 γ3 γ4 γ5 γ6) ->
    (forall q, halt q = false -> transSomeNone q γ1 γ2 γ3 γ4 γ5 γ6 -> P γ1 γ2 γ3 γ4 γ5 γ6) ->
    (forall q, halt q = false -> transNoneSome q γ1 γ2 γ3 γ4 γ5 γ6 -> P γ1 γ2 γ3 γ4 γ5 γ6) ->
    (forall q, halt q = false -> transNoneNone q γ1 γ2 γ3 γ4 γ5 γ6 -> P γ1 γ2 γ3 γ4 γ5 γ6) ->
    transRules γ1 γ2 γ3 γ4 γ5 γ6 -> P γ1 γ2 γ3 γ4 γ5 γ6.
  Proof.
    intros ? ? ? ? H0. inv H0. all:eauto 2.     
  Qed.

  Tactic Notation "inv'" hyp(H) uconstr(L):= inversion H using L; try clear H; intros.

  (** *** inversion of transition rules*)
  Ltac transRules_inv1 :=
    match goal with
    | [H : transRules _ _ _ _ _ _ |- _] => inv' H transRules_inv
    end.

  (** full inversions - very (!) costly *)
  Ltac transRules_inv2_once :=
    once
      match goal with
      (*| H : ?s = ?s |- _ => clear H*)
      | [H : inl _ = inr _ |- _] => discriminate H
      | [H : inr _ = inl _ |- _] => discriminate H
      | [H : transRules    _ _ _ _ _ _ |- _] => inv' H transRules_inv
      | [H : transSomeSome _ _ _ _ _ _ _ |- _ ] => inv' H transSomeSome_inv
      | [H : transNoneSome _ _ _ _ _ _ _ |- _ ] => inv' H transNoneSome_inv
      | [H : transSomeNone _ _ _ _ _ _ _ |- _ ] => inv' H transSomeNone_inv
      | [H : transNoneNone _ _ _ _ _ _ _ |- _ ] => inv' H transNoneNone_inv
      | [H : transSomeSomeLeft   _ _ _ _ _ _ _ |- _ ] => inv' H transSomeSomeLeft_inv
      | [H : transSomeSomeRight  _ _ _ _ _ _ _ |- _] => inv' H transSomeSomeRight_inv
      | [H : transSomeSomeCenter _ _ _ _ _ _ _ |- _ ] => inv' H transSomeSomeCenter_inv
      | [H : transSomeNoneLeft   _ _ _ _ _ _ _ |- _ ] => inv' H transSomeNoneLeft_inv
      | [H : transSomeNoneRight  _ _ _ _ _ _ _ |- _] => inv' H transSomeNoneRight_inv
      | [H : transSomeNoneCenter _ _ _ _ _ _ _ |- _ ] => inv' H transSomeNoneCenter_inv
      | [H : transNoneSomeLeft   _ _ _ _ _ _ _ |- _ ] => inv' H transNoneSomeLeft_inv
      | [H : transNoneSomeRight  _ _ _ _ _ _ _ |- _] => inv' H transNoneSomeRight_inv
      | [H : transNoneSomeCenter _ _ _ _ _ _ _ |- _ ] => inv' H transNoneSomeCenter_inv
      | [H : transSomeStayLeft   _ _ _ _ _ _ _ _ _ _ |- _] => inv' H transSomeStayLeft_inv
      | [H : transSomeStayCenter _ _ _ _ _ _ _ _ _ _ |- _ ] => inv' H transSomeStayCenter_inv
      | [H : transSomeStayRight  _ _ _ _ _ _ _ _ _ _ |- _ ] => inv' H transSomeStayRight_inv
      | [H : transSomeLeftCenter _ _ _ _ _ _ _ _ _ _ |- _ ] => inv' H transSomeLeftCenter_inv
      | [H : transSomeLeftLeft   _ _ _ _ _ _ _ _ _ |- _] => inv' H transSomeLeftLeft_inv
      | [H : transSomeLeftRight  _ _ _ _ _ _ _ _ _ _ |- _] => inv' H transSomeLeftRight_inv
      | [H : transSomeRightLeft  _ _ _ _ _ _ _ _ _ _ |- _] => inv' H transSomeRightLeft_inv
      | [H : transSomeRightRight _ _ _ _ _ _ _ _ _ |- _] => inv' H transSomeRightRight_inv
      | [H : transSomeRightCenter _ _ _ _ _ _ _ _ _ _ |- _] => inv' H transSomeRightCenter_inv
      | [H : transNoneNoneLeft   _ _ _ _ _ _ _ |- _ ] => inv' H transNoneNoneLeft_inv
      | [H : transNoneNoneRight  _ _ _ _ _ _ _ |- _] => inv' H transNoneNoneRight_inv
      | [H : transNoneNoneCenter _ _ _ _ _ _ _ |- _ ] => inv' H transNoneNoneCenter_inv
      | [H : transNoneStayLeft   _ _ _ _ _ _ _ _ |- _] => inv' H transNoneStayLeft_inv
      | [H : transNoneStayCenter _ _ _ _ _ _ _ _ |- _ ] => inv' H transNoneStayCenter_inv
      | [H : transNoneStayRight  _ _ _ _ _ _ _ _ |- _ ] => inv' H transNoneStayRight_inv
      | [H : transNoneLeftCenter _ _ _ _ _ _ _ _ |- _ ] => inv' H transNoneLeftCenter_inv
      | [H : transNoneLeftLeft   _ _ _ _ _ _ _ _ |- _] => inv' H transNoneLeftLeft_inv
      | [H : transNoneLeftRight  _ _ _ _ _ _ _ _ |- _] => inv' H transNoneLeftRight_inv
      | [H : transNoneRightLeft  _ _ _ _ _ _ _ _ |- _] => inv' H transNoneRightLeft_inv
      | [H : transNoneRightRight _ _ _ _ _ _ _ _ |- _] => inv' H transNoneRightRight_inv
      | [H : transNoneRightCenter _ _ _ _ _ _ _ _ |- _] => inv' H transNoneRightCenter_inv
      | [H : inl _ = inl _ |- _] => inv H
      | [H : inr _ = inr _ |- _] => inv H
      end. 

  Ltac transRules_inv2 := repeat transRules_inv2_once;subst. 

  Lemma transRules_semCasesLeft q q' m m' dir (γ2 γ3 γ4 γ5 γ6 : Gamma) :
  transRules (inl (q, m)) γ2 γ3 γ4 γ5 γ6
  -> trans (q, m) = (q',(m',dir))
  -> match γ2 with
    | inr (inr (p2,m2)) =>
      match γ3 with
      | inr (inr (p3,m3)) =>
        (match m,m' with None,None => m2 = |_| ->  m3 = |_| | _,_ => True end) /\
          let effectiveMove := (* not at border *)
            match m,m' with
            | None,None =>
              match dir with
                neutral => Some neutral
              | positive => match m2,m3 with
                            | None,_ => None
                            | _,None => None
                            | _,_ => Some positive
                            end
              | _ => None
              end
            | _, _ => Some dir
            end in
          let mout :=  match m' with None => m | Some mout => m' end in
          match effectiveMove with
          | Some negative => (exists m1,γ4 = (inl (q', m1))) /\ γ5 = inr (inr (positive,mout)) /\ γ6 = inr (inr (positive,m2))
          | Some neutral => γ4 = (inl (q', mout)) /\ γ5 = inr (inr (∘ m2)) /\ γ6 = inr (inr (∘m3))
          | Some positive => γ4 = (inl (q', m2)) /\ γ5 = inr (inr (negative,m3)) /\ (exists m4,γ6 = inr (inr (negative,m4)))
          | None =>
            match dir,m2 with
            | positive,None | negative,Some _ => γ4 = (inl (q', None)) /\ (exists p', γ5 = inr (inr (p', m2)) /\ γ6 = inr (inr (p',m3)))
            | positive,Some _ => γ4 = (inl (q', m2)) /\ (exists p', γ5 = inr (inr (p', m)) /\ γ6 = inr (inr (p',m3)))
            | negative,None => (exists m', γ4 = (inl (q', m'))) /\ (exists p', γ5 = inr (inr (p', m)) /\ γ6 = inr (inr (p',m3)))
            | _,_ => False
            end
          end
      | _ => False
    end
    | _ => False
  end.
  Proof.
    intros H H2; assert (H':=H);lock H'; transRules_inv2;lazymatch goal with H2 : trans _ = _ , H' : trans _ = _ |- _ => rewrite H2 in H';injection H' as [= -> -> ->] end;
    (split;[solve [exact I |congruence]|]);intros ? ?;cbn;try solve [repeat esplit].
  Qed.

  
  Lemma transRules_semCasesRight q q' m m' dir (γ1 γ2 γ4 γ5 γ6 : Gamma) :
  transRules  γ1 γ2 (inl (q, m)) γ4 γ5 γ6
  -> trans (q, m) = (q',(m',dir))
  -> match γ2 with
    | inr (inr (p2,m2)) =>
      match γ1 with
      | inr (inr (p1,m1)) =>
        (match m,m' with None,None => m2 = |_| ->  m1 = |_| | _,_ => True end) /\
          let effectiveMove := (* not at border *)
            match m,m' with
            | None,None =>
              match dir with
                neutral => Some neutral
              | negative => match m2,m1 with
                            | None,_ => None
                            | _,None => None
                            | _,_ => Some negative
                            end
              | _ => None
              end
            | _, _ => Some dir
            end in
          let mout :=  match m' with None => m | Some mout => m' end in
          match effectiveMove with
          | Some positive => γ4 = inr (inr (negative,m2)) /\ γ5 = inr (inr (negative,mout)) /\ (exists m3,γ6 = (inl (q', m3)))
          | Some neutral => γ4 = inr (inr (∘ m1)) /\ γ5 = inr (inr (∘ m2)) /\ γ6 = (inl (q', mout))
          | Some negative => (exists m1,γ4 = inr (inr (positive,m1))) /\ γ5 = inr (inr (positive,m1)) /\ γ6 = (inl (q', m2))
          | None => (*TODO:flip *)
            match dir,m2 with
            | negative,None | positive, Some _ => (exists p', γ4 = inr (inr (p',m1)) /\  γ5 = inr (inr (p', m2))) /\ γ6 = (inl (q', None))
            | negative,Some _ => (exists p', γ4 = inr (inr (p',m1)) /\ γ5 = inr (inr (p', m))) /\ γ6 = (inl (q', m2)) 
            | positive,None =>  (exists p', γ4 = inr (inr (p',m1)) /\ γ5 = inr (inr (p', m))) /\ (exists m', γ6 = (inl (q', m')))
            | _,_ => False
            end
          end
      | _ => False
    end
    | _ => False
  end.
  Proof.
    intros H H2; assert (H':=H);lock H'; transRules_inv2;lazymatch goal with H2 : trans _ = _ , H' : trans _ = _ |- _ => rewrite H2 in H';injection H' as [= -> -> ->] end;
    (split;[solve [exact I |congruence]|]);intros ? ?;cbn;try solve [repeat esplit].
  Qed.


  Lemma transRules_semCasesCenter q q' m m' dir (γ1 γ3 γ4 γ5 γ6 : Gamma) :
  transRules γ1 (inl (q, m)) γ3 γ4 γ5 γ6
  -> trans (q, m) = (q',(m',dir))
  -> match γ1 with
    | inr (inr (p1,m1)) =>
      match γ3 with
      | inr (inr (p3,m3)) => 
          let effectiveMove := (* not at border *)
            match m,m' with
            | None,None =>
              match dir with
              | positive => match m3 with
                            | None => None
                            | _ => Some dir
                            end
              | negative => match m1 with
                            | None => None
                            | _=> Some dir
                            end
              | _ => Some dir
              end
            | _, _ => Some dir
            end in
          let mout :=  match m' with None => m | Some mout => m' end in 
          match effectiveMove with
          | Some negative => (exists m0,γ4 = (inr (inr (positive, m0)))) /\ γ5 = inl (q', m1) /\ γ6 = inr (inr (positive,mout))
          | Some neutral => γ4 = (inr (inr (∘ m1))) /\ γ5 = inl (q',mout)  /\ γ6 = inr (inr (∘m3))
          | Some positive => γ4 = inr (inr (negative,mout)) /\ γ5 = inl (q', m3) /\ (exists m0,γ6 = (inr (inr (negative, m0))))
          (*| Some positive => γ4 = (inl (q', m2)) /\ γ5 = inr (inr (negative,m3)) /\ (exists m4,γ6 = inr (inr (negative,m4)))*)
          | None => 
            match dir with
            | positive => γ4 = inr (inr (∘ m1)) /\ γ5 = inl (q',mout) /\ γ6 = inr (inr (∘ m3))
            | negative => γ4 = inr (inr (∘ m1)) /\ γ5 = inl (q',mout) /\ γ6 = inr (inr (∘ m3))
            | _ => False
            end 
          end
      | _ => False
    end
    | _ => False
  end.
  Proof.
    intros H H2; assert (H':=H);lock H'; transRules_inv2;lazymatch goal with H2 : trans _ = _ , H' : trans _ = _ |- _ => rewrite H2 in H';
    injection H' as [= -> -> ->] end;
    (*(split;[solve [exact I |congruence]|]);*)intros;cbn;try solve [repeat esplit].
  Qed.

  (** manual inversion lemmas because of performance *) 
  Lemma transSomeSome_inv1 q q0 m γ2 γ3 γ4 γ5 γ6 : transSomeSome q (inl (q0, m)) γ2 γ3 γ4 γ5 γ6 -> q0 = q /\ (exists σ, m = Some σ) /\ exists q' m', γ4 = inl (q', m') /\ transSomeSomeLeft q (inl (q, m)) γ2 γ3 (inl (q', m')) γ5 γ6. 
  Proof.
   intros. transRules_inv2;eauto 10 with trans.
  Qed.  

  Lemma transSomeSome_inv2 q q0 m γ1 γ3 γ4 γ5 γ6 : transSomeSome q γ1 (inl (q0, m)) γ3 γ4 γ5 γ6 -> q0 = q /\ (exists σ, m = Some σ) /\ exists q' m', γ5 = inl (q', m') /\ transSomeSomeCenter q γ1 (inl (q, m)) γ3 γ4 (inl (q', m')) γ6. 
  Proof. 
    intros. transRules_inv2;eauto 10 with trans.
  Qed.  

  Lemma transSomeSome_inv3 q q0 m γ1 γ2 γ4 γ5 γ6 : transSomeSome q γ1 γ2 (inl (q0, m)) γ4 γ5 γ6 -> q0 = q /\ (exists σ, m = Some σ) /\ exists q' m', γ6 = inl (q', m') /\ transSomeSomeRight q γ1 γ2 (inl (q, m)) γ4 γ5 (inl (q', m')).  
  Proof.
    intros. transRules_inv2;eauto 10 with trans.
  Qed.  

  Lemma transSomeNone_inv1 q q0 m γ2 γ3 γ4 γ5 γ6 : transSomeNone q (inl (q0, m)) γ2 γ3 γ4 γ5 γ6 -> q0 = q /\ (exists σ, m = Some σ) /\ exists q' m', γ4 = inl (q', m') /\ transSomeNoneLeft q (inl (q, m)) γ2 γ3 (inl (q', m')) γ5 γ6. 
  Proof.
    intros. transRules_inv2;eauto 10 with trans.
  Qed.  

  Lemma transSomeNone_inv2 q q0 m γ1 γ3 γ4 γ5 γ6 : transSomeNone q γ1 (inl (q0, m)) γ3 γ4 γ5 γ6 -> q0 = q /\ (exists σ, m = Some σ) /\ exists q' m', γ5 = inl (q', m') /\ transSomeNoneCenter q γ1 (inl (q, m)) γ3 γ4 (inl (q', m')) γ6. 
  Proof.
    intros. transRules_inv2;eauto 10 with trans.
  Qed.

 (*Set Ltac Profiling. *)
  Lemma transSomeNone_inv3 q q0 m γ1 γ2 γ4 γ5 γ6 : transSomeNone q γ1 γ2 (inl (q0, m)) γ4 γ5 γ6 -> q0 = q /\ (exists σ, m = Some σ) /\ exists q' m', γ6 = inl (q', m') /\ transSomeNoneRight q γ1 γ2 (inl (q, m)) γ4 γ5 (inl (q', m')).  
  Proof.  
    intros. transRules_inv2;eauto 10 with trans.
  Qed.
  (*Show Ltac Profile CutOff 0. (*Old: 0.579 total, 81% in inversion; New: 0.329s, 75% in inversion, but only 1/3 of nversion calls have been converted to using inversion lemmas.  *)*)
 

  Lemma transNoneSome_inv1 q q0 m γ2 γ3 γ4 γ5 γ6 : transNoneSome q (inl (q0, m)) γ2 γ3 γ4 γ5 γ6 -> q0 = q /\ m = |_| /\ exists q' m', γ4 = inl (q', m') /\ transNoneSomeLeft q (inl (q, m)) γ2 γ3 (inl (q', m')) γ5 γ6. 
  Proof.
    intros. transRules_inv2;eauto 10 with trans.
  Qed.  

  Lemma transNoneSome_inv2 q q0 m γ1 γ3 γ4 γ5 γ6 : transNoneSome q γ1 (inl (q0, m)) γ3 γ4 γ5 γ6 -> q0 = q /\ m = |_| /\  exists q' m', γ5 = inl (q', m') /\ transNoneSomeCenter q γ1 (inl (q, m)) γ3 γ4 (inl (q', m')) γ6. 
  Proof.
    intros. transRules_inv2;eauto 10 with trans.
  Qed.  

  Lemma transNoneSome_inv3 q q0 m γ1 γ2 γ4 γ5 γ6 : transNoneSome q γ1 γ2 (inl (q0, m)) γ4 γ5 γ6 -> q0 = q /\ m = |_| /\ exists q' m', γ6 = inl (q', m') /\ transNoneSomeRight q γ1 γ2 (inl (q, m)) γ4 γ5 (inl (q', m')).  
  Proof.
    intros. transRules_inv2;eauto 10 with trans.
  Qed. 

  Lemma transNoneNone_inv1 q q0 m γ2 γ3 γ4 γ5 γ6 : transNoneNone q (inl (q0, m)) γ2 γ3 γ4 γ5 γ6 -> q0 = q /\ m = |_| /\ exists q' m', γ4 = inl (q', m') /\ transNoneNoneLeft q (inl (q, m)) γ2 γ3 (inl (q', m')) γ5 γ6. 
  Proof.
    intros. transRules_inv2;eauto 10 with trans. 
  Qed.  

  Lemma transNoneNone_inv2 q q0 m γ1 γ3 γ4 γ5 γ6 : transNoneNone q γ1 (inl (q0, m)) γ3 γ4 γ5 γ6 -> q0 = q /\ m = |_| /\ exists q' m', γ5 = inl (q', m') /\ transNoneNoneCenter q γ1 (inl (q, m)) γ3 γ4 (inl (q', m')) γ6. 
  Proof.
        intros. transRules_inv2;eauto 10 with trans.
  Qed.  

  Lemma transNoneNone_inv3 q q0 m γ1 γ2 γ4 γ5 γ6 : transNoneNone q γ1 γ2 (inl (q0, m)) γ4 γ5 γ6 -> q0 = q /\ m = |_| /\ exists q' m', γ6 = inl (q', m') /\ transNoneNoneRight q γ1 γ2 (inl (q, m)) γ4 γ5 (inl (q', m')).  
  Proof.
    intros. transRules_inv2;eauto 10 with trans.
  Qed. 

  Ltac inv_eqn H :=
    let t:= type of H in
    match t with 
    | ?h = ?h' => is_var h ; subst h
    | ?h = ?h' => is_var h'; first [symmetry in H;move H at bottom; subst h' | is_var h;constr_eq h h';clear H]
    | _ => 
      once lazymatch t with 
      | ?x = ?x => clear H
      | None = Some _ => discriminate H
      | Some _ = None => discriminate H
      | Some _ = Some _ => apply Some_injective in H;inv_eqn H
      | inl _ = inr _ => discriminate H
      | inr _ = inl _ => discriminate H
      | inl _ = inl _ => apply inl_injective in H;inv_eqn H
      | inr _ = inr _ => apply inr_injective in H;inv_eqn H
      | (_,_) = (_,_) =>
          let H1 := fresh in 
          let H2 := fresh in
          simple apply prod_eq in H as [H1 H2]; inv_eqn H1;inv_eqn H2
      | _ /\ _ =>
        let H1 := fresh in 
        let H2 := fresh in destruct H as [H1 H2];inv_eqn H1;inv_eqn H2
      | exists x, _ => destruct H as [? H];inv_eqn H
      | True => first [clear H | destruct H]
      | _ => fail 1000 "inv_eqn" t
      end
    end.  

  (** inversions for the second level of the hierarchy of predicates *) 
  Ltac inv_trans_prim := repeat match goal with 
        | [H : transSomeSome _ _ _ (inl (_, _)) _ _ _ |- _] => let Heqn := fresh "eqn" in let Heqn' := fresh "eqn" in apply transSomeSome_inv3 in H as (<- & (? & Heqn') & (? & ? & Heqn & ?)); inv_eqn Heqn; inv_eqn Heqn' 
        | [H : transSomeSome _ (inl (_, _)) _ _ _ _ _ |- _] => let Heqn := fresh "eqn" in let Heqn' := fresh "eqn" in apply transSomeSome_inv1 in H as (<- & (? & Heqn') & (? & ? & Heqn & ?)); inv_eqn Heqn; inv_eqn Heqn' 
        | [H : transSomeSome _ _ (inl (_, _)) _ _ _ _ |- _] => let Heqn := fresh "eqn" in let Heqn' := fresh "eqn" in apply transSomeSome_inv2 in H as (<- & (? & Heqn') & (? & ? & Heqn & ?)); inv_eqn Heqn; inv_eqn Heqn' 
        | [H : transSomeNone _ _ _ (inl (_, _)) _ _ _ |- _] => let Heqn := fresh "eqn" in let Heqn' := fresh "eqn" in apply transSomeNone_inv3 in H as (<- & (? & Heqn') & (? & ? & Heqn & ?)); inv_eqn Heqn; inv_eqn Heqn' 
        | [H : transSomeNone _ (inl (_, _)) _ _ _ _ _ |- _] => let Heqn := fresh "eqn" in let Heqn' := fresh "eqn" in apply transSomeNone_inv1 in H as (<- & (? & Heqn') & (? & ? & Heqn & ?)); inv_eqn Heqn; inv_eqn Heqn' 
        | [H : transSomeNone _ _ (inl (_, _)) _ _ _ _ |- _] => let Heqn := fresh "eqn" in let Heqn' := fresh "eqn" in apply transSomeNone_inv2 in H as (<- & (? & Heqn') & (? & ? & Heqn & ?)); inv_eqn Heqn; inv_eqn Heqn' 
        | [H : transNoneSome _ _ _ (inl (_, _)) _ _ _ |- _] => let Heqn := fresh "eqn" in let Heqn' := fresh "eqn" in apply transNoneSome_inv3 in H as (<- & Heqn' & (? & ? & Heqn & ?)); inv_eqn Heqn; inv_eqn Heqn' 
        | [H : transNoneSome _ (inl (_, _)) _ _ _ _ _ |- _] => let Heqn := fresh "eqn" in let Heqn' := fresh "eqn" in apply transNoneSome_inv1 in H as (<- & Heqn' & (? & ? & Heqn & ?)); inv_eqn Heqn; inv_eqn Heqn' 
        | [H : transNoneSome _ _ (inl (_, _)) _ _ _ _ |- _] => let Heqn := fresh "eqn" in let Heqn' := fresh "eqn" in apply transNoneSome_inv2 in H as (<- & Heqn' & (? & ? & Heqn & ?)); inv_eqn Heqn; inv_eqn Heqn' 
        | [H : transNoneNone _ _ _ (inl (_, _)) _ _ _ |- _] => let Heqn := fresh "eqn" in let Heqn' := fresh "eqn" in apply transNoneNone_inv3 in H as (<- & Heqn' & (? & ? & Heqn & ?)); inv_eqn Heqn; inv_eqn Heqn' 
        | [H : transNoneNone _ (inl (_, _)) _ _ _ _ _ |- _] => let Heqn := fresh "eqn" in let Heqn' := fresh "eqn" in apply transNoneNone_inv1 in H as (<- & Heqn' & (? & ? & Heqn & ?)); inv_eqn Heqn; inv_eqn Heqn' 
        | [H : transNoneNone _ _ (inl (_, _)) _ _ _ _ |- _] => let Heqn := fresh "eqn" in let Heqn' := fresh "eqn" in apply transNoneNone_inv2 in H as (<- & Heqn' & (? & ? & Heqn & ?)); inv_eqn Heqn; inv_eqn Heqn' 
      end. 

  (** third-level inversions *) 
  Lemma transSomeSomeRight_inv1 q a b q' γ1 γ2 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some b, positive)) -> transSomeSomeRight q γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6 -> transSomeLeftRight q q' (Some a) (Some b) γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6.  
  Proof. intros. inv H0; simp_eqn. Qed.  

  Lemma transSomeSomeRight_inv2 q a b q' γ1 γ2 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some b, negative)) -> transSomeSomeRight q γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6 -> transSomeRightRight q q' (Some a) γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6. 
  Proof. intros. inv H0; simp_eqn. Qed. 

  Lemma transSomeSomeRight_inv3 q a b q' γ1 γ2 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some b, neutral)) -> transSomeSomeRight q γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6 -> transSomeStayRight q q' (Some a) (Some b) γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6. 
  Proof. intros. inv H0; simp_eqn. Qed. 

  Lemma transSomeSomeLeft_inv1 q a b q' γ2 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some b, positive)) -> transSomeSomeLeft q (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6 -> transSomeLeftLeft q q' (Some a) (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6. 
  Proof. intros. inv H0; simp_eqn. Qed.  

  Lemma transSomeSomeLeft_inv2 q a b q' γ2 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some b, negative)) -> transSomeSomeLeft q (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6 -> transSomeRightLeft q q' (Some a) (Some b) (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6. 
  Proof. intros. inv H0; simp_eqn. Qed. 

  Lemma transSomeSomeLeft_inv3 q a b q' γ2 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some b, neutral)) -> transSomeSomeLeft q  (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6 -> transSomeStayLeft q q' (Some a) (Some b) (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6. 
  Proof. intros. inv H0; simp_eqn. Qed. 

  Lemma transSomeSomeCenter_inv1 q a b q' γ1 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some b, positive)) -> transSomeSomeCenter q γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6 -> transSomeLeftCenter q q' (Some a) (Some b) γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6. 
  Proof. intros. inv H0; simp_eqn. Qed.  

  Lemma transSomeSomeCenter_inv2 q a b q' γ1 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some b, negative)) -> transSomeSomeCenter q γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6 -> transSomeRightCenter q q' (Some a) (Some b) γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6. 
  Proof. intros. inv H0; simp_eqn. Qed. 

  Lemma transSomeSomeCenter_inv3 q a b q' γ1 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some b, neutral)) -> transSomeSomeCenter q  γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6 -> transSomeStayCenter q q' (Some a) (Some b) γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6. 
  Proof. intros. inv H0; simp_eqn. Qed. 

  (*the same for None, Some *) 
  Lemma transNoneSomeRight_inv1 q b q' γ1 γ2 γ4 γ5 γ6 : trans (q, None) = (q', (Some b, positive)) -> transNoneSomeRight q γ1 γ2 (inl (q, None)) γ4 γ5 γ6 -> transSomeLeftRight q q' (None) (Some b) γ1 γ2 (inl (q, None)) γ4 γ5 γ6.  
  Proof. intros. inv H0; simp_eqn. Qed.  

  Lemma transNoneSomeRight_inv2 q b q' γ1 γ2 γ4 γ5 γ6 : trans (q, None) = (q', (Some b, negative)) -> transNoneSomeRight q γ1 γ2 (inl (q, None)) γ4 γ5 γ6 -> transSomeRightRight q q' (None) γ1 γ2 (inl (q, None)) γ4 γ5 γ6. 
  Proof. intros. inv H0; simp_eqn. Qed. 

  Lemma transNoneSomeRight_inv3 q b q' γ1 γ2 γ4 γ5 γ6 : trans (q, None) = (q', (Some b, neutral)) -> transNoneSomeRight q γ1 γ2 (inl (q, None)) γ4 γ5 γ6 -> transSomeStayRight q q' (None) (Some b) γ1 γ2 (inl (q, None)) γ4 γ5 γ6. 
  Proof. intros. inv H0; simp_eqn. Qed. 

  Lemma transNoneSomeLeft_inv1 q b q' γ2 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (Some b, positive)) -> transNoneSomeLeft q (inl (q, None)) γ2 γ3 γ4 γ5 γ6 -> transSomeLeftLeft q q' (None) (inl (q, None)) γ2 γ3 γ4 γ5 γ6. 
  Proof. intros. inv H0; simp_eqn. Qed.  

  Lemma transNoneSomeLeft_inv2 q b q' γ2 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (Some b, negative)) -> transNoneSomeLeft q (inl (q, None)) γ2 γ3 γ4 γ5 γ6 -> transSomeRightLeft q q' (None) (Some b) (inl (q, None)) γ2 γ3 γ4 γ5 γ6. 
  Proof. intros. inv H0; simp_eqn. Qed. 

  Lemma transNoneSomeLeft_inv3 q b q' γ2 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (Some b, neutral)) -> transNoneSomeLeft q  (inl (q, None)) γ2 γ3 γ4 γ5 γ6 -> transSomeStayLeft q q' (None) (Some b) (inl (q, None)) γ2 γ3 γ4 γ5 γ6. 
  Proof. intros. inv H0; simp_eqn. Qed. 

  Lemma transNoneSomeCenter_inv1 q b q' γ1 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (Some b, positive)) -> transNoneSomeCenter q γ1 (inl (q, None)) γ3 γ4 γ5 γ6 -> transSomeLeftCenter q q' (None) (Some b) γ1 (inl (q, None)) γ3 γ4 γ5 γ6. 
  Proof. intros. inv H0; simp_eqn. Qed.  

  Lemma transNoneSomeCenter_inv2 q b q' γ1 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (Some b, negative)) -> transNoneSomeCenter q γ1 (inl (q, None)) γ3 γ4 γ5 γ6 -> transSomeRightCenter q q' (None) (Some b) γ1 (inl (q, None)) γ3 γ4 γ5 γ6. 
  Proof. intros. inv H0; simp_eqn. Qed. 

  Lemma transNoneSomeCenter_inv3 q b q' γ1 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (Some b, neutral)) -> transNoneSomeCenter q  γ1 (inl (q, None)) γ3 γ4 γ5 γ6 -> transSomeStayCenter q q' (None) (Some b) γ1 (inl (q, None)) γ3 γ4 γ5 γ6. 
  Proof. intros. inv H0; simp_eqn. Qed. 

  (*Some, None*) 
  Lemma transSomeNoneRight_inv1 q a q' γ1 γ2 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some a, positive)) -> transSomeNoneRight q γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6 -> transSomeLeftRight q q' (Some a) (Some a) γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6.  
  Proof. intros. inv H0; simp_eqn. Qed.  

  Lemma transSomeNoneRight_inv2 q a q' γ1 γ2 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some a, negative)) -> transSomeNoneRight q γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6 -> transSomeRightRight q q' (Some a) γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6. 
  Proof. intros. inv H0; simp_eqn. Qed. 

  Lemma transSomeNoneRight_inv3 q a q' γ1 γ2 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some a, neutral)) -> transSomeNoneRight q γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6 -> transSomeStayRight q q' (Some a) (Some a) γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6. 
  Proof. intros. inv H0; simp_eqn. Qed. 

  Lemma transSomeNoneLeft_inv1 q a q' γ2 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some a, positive)) -> transSomeNoneLeft q (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6 -> transSomeLeftLeft q q' (Some a) (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6. 
  Proof. intros. inv H0; simp_eqn. Qed.  

  Lemma transSomeNoneLeft_inv2 q a q' γ2 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some a, negative)) -> transSomeNoneLeft q (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6 -> transSomeRightLeft q q' (Some a) (Some a) (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6. 
  Proof. intros. inv H0; simp_eqn. Qed. 

  Lemma transSomeNoneLeft_inv3 q a q' γ2 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some a, neutral)) -> transSomeNoneLeft q  (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6 -> transSomeStayLeft q q' (Some a) (Some a) (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6. 
  Proof. intros. inv H0; simp_eqn. Qed. 

  Lemma transSomeNoneCenter_inv1 q a q' γ1 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some a, positive)) -> transSomeNoneCenter q γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6 -> transSomeLeftCenter q q' (Some a) (Some a) γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6. 
  Proof. intros. inv H0; simp_eqn. Qed.  

  Lemma transSomeNoneCenter_inv2 q a q' γ1 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some a, negative)) -> transSomeNoneCenter q γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6 -> transSomeRightCenter q q' (Some a) (Some a) γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6. 
  Proof. intros. inv H0; simp_eqn. Qed. 

  Lemma transSomeNoneCenter_inv3 q a q' γ1 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some a, neutral)) -> transSomeNoneCenter q  γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6 -> transSomeStayCenter q q' (Some a) (Some a) γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6. 
  Proof. intros. inv H0; simp_eqn. Qed. 

  (* None, None*) 
  Lemma transNoneNoneRight_inv1 q q' γ1 γ2 γ4 γ5 γ6 : trans (q, None) = (q', (None, positive)) -> transNoneNoneRight q γ1 γ2 (inl (q, None)) γ4 γ5 γ6 -> transNoneLeftRight q q' γ1 γ2 (inl (q, None)) γ4 γ5 γ6.  
  Proof. intros. inv H0; simp_eqn. Qed.  

  Lemma transNoneNoneRight_inv2 q q' γ1 γ2 γ4 γ5 γ6 : trans (q, None) = (q', (None, negative)) -> transNoneNoneRight q γ1 γ2 (inl (q, None)) γ4 γ5 γ6 -> transNoneRightRight q q' γ1 γ2 (inl (q, None)) γ4 γ5 γ6. 
  Proof. intros. inv H0; simp_eqn. Qed. 

  Lemma transNoneNoneRight_inv3 q q' γ1 γ2 γ4 γ5 γ6 : trans (q, None) = (q', (None, neutral)) -> transNoneNoneRight q γ1 γ2 (inl (q, None)) γ4 γ5 γ6 -> transNoneStayRight q q' γ1 γ2 (inl (q, None)) γ4 γ5 γ6. 
  Proof. intros. inv H0; simp_eqn. Qed. 

  Lemma transNoneNoneLeft_inv1 q q' γ2 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (None, positive)) -> transNoneNoneLeft q (inl (q, None)) γ2 γ3 γ4 γ5 γ6 -> transNoneLeftLeft q q' (inl (q, None)) γ2 γ3 γ4 γ5 γ6. 
  Proof. intros. inv H0; simp_eqn. Qed.  

  Lemma transNoneNoneLeft_inv2 q q' γ2 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (None, negative)) -> transNoneNoneLeft q (inl (q, None)) γ2 γ3 γ4 γ5 γ6 -> transNoneRightLeft q q' (inl (q, None)) γ2 γ3 γ4 γ5 γ6. 
  Proof. intros. inv H0; simp_eqn. Qed. 

  Lemma transNoneNoneLeft_inv3 q q' γ2 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (None, neutral)) -> transNoneNoneLeft q  (inl (q, None)) γ2 γ3 γ4 γ5 γ6 -> transNoneStayLeft q q' (inl (q, None)) γ2 γ3 γ4 γ5 γ6. 
  Proof. intros. inv H0; simp_eqn. Qed. 

  Lemma transNoneNoneCenter_inv1 q q' γ1 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (None, positive)) -> transNoneNoneCenter q γ1 (inl (q, None)) γ3 γ4 γ5 γ6 -> transNoneLeftCenter q q' γ1 (inl (q, None)) γ3 γ4 γ5 γ6. 
  Proof. intros. inv H0; simp_eqn. Qed.  

  Lemma transNoneNoneCenter_inv2 q q' γ1 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (None, negative)) -> transNoneNoneCenter q γ1 (inl (q, None)) γ3 γ4 γ5 γ6 -> transNoneRightCenter q q' γ1 (inl (q, None)) γ3 γ4 γ5 γ6. 
  Proof. intros. inv H0; simp_eqn. Qed. 

  Lemma transNoneNoneCenter_inv3 q q' γ1 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (None, neutral)) -> transNoneNoneCenter q  γ1 (inl (q, None)) γ3 γ4 γ5 γ6 -> transNoneStayCenter q q' γ1 (inl (q, None)) γ3 γ4 γ5 γ6. 
  Proof. intros. inv H0; simp_eqn. Qed. 

  (** apply the inversion lemmas from above *) 
  Ltac inv_trans_sec := 
  match goal with 
  | [H : trans (_, _) = (_, (_, neutral)) |- _] => 
    repeat match goal with 
            | [H2 : context[transSomeSomeLeft] |- _] => first [eapply transSomeSomeLeft_inv3 in H2; [ | exact H]]  
            | [H2 : context[transSomeSomeRight] |- _] => first [eapply transSomeSomeRight_inv3 in H2; [ | exact H]]
            | [H2 : context[transSomeSomeCenter] |- _] => first [eapply transSomeSomeCenter_inv3 in H2; [ | exact H]]
            | [H2 : context[transNoneSomeLeft] |- _] => first [eapply transNoneSomeLeft_inv3 in H2; [ | exact H]] 
            | [H2 : context[transNoneSomeRight] |- _] => first [eapply transNoneSomeRight_inv3 in H2; [ | exact H]]
            | [H2 : context[transNoneSomeCenter] |- _] => first [eapply transNoneSomeCenter_inv3 in H2; [ | exact H]]
            | [H2 : context[transSomeNoneLeft] |- _] => first [eapply transSomeNoneLeft_inv3 in H2; [ | exact H]] 
            | [H2 : context[transSomeNoneRight] |- _] => first [eapply transSomeNoneRight_inv3 in H2; [ | exact H]]
            | [H2 : context[transSomeNoneCenter] |- _] => first [eapply transSomeNoneCenter_inv3 in H2; [ | exact H]]
            | [H2 : context[transNoneNoneLeft] |- _] => first [eapply transNoneNoneLeft_inv3 in H2; [ | exact H]] 
            | [H2 : context[transNoneNoneRight] |- _] => first [eapply transNoneNoneRight_inv3 in H2; [ | exact H]]
            | [H2 : context[transNoneNoneCenter] |- _] => first [eapply transNoneNoneCenter_inv3 in H2; [ | exact H]]
    end 
  | [H : trans (_, _) = (_, (_, negative)) |- _] => 
    repeat match goal with 
            | [H2 : context[transSomeSomeLeft] |- _] => first [eapply transSomeSomeLeft_inv2 in H2; [ | exact H]] 
            | [H2 : context[transSomeSomeRight] |- _] => first [eapply transSomeSomeRight_inv2 in H2; [ | exact H]]
            | [H2 : context[transSomeSomeCenter] |- _] => first [eapply transSomeSomeCenter_inv2 in H2; [ | exact H]]
            | [H2 : context[transNoneSomeLeft] |- _] => first [eapply transNoneSomeLeft_inv2 in H2; [ | exact H]] 
            | [H2 : context[transNoneSomeRight] |- _] => first [eapply transNoneSomeRight_inv2 in H2; [ | exact H]]
            | [H2 : context[transNoneSomeCenter] |- _] => first [eapply transNoneSomeCenter_inv2 in H2; [ | exact H]]
            | [H2 : context[transSomeNoneLeft] |- _] => first [eapply transSomeNoneLeft_inv2 in H2; [ | exact H]] 
            | [H2 : context[transSomeNoneRight] |- _] => first [eapply transSomeNoneRight_inv2 in H2; [ | exact H]]
            | [H2 : context[transSomeNoneCenter] |- _] => first [eapply transSomeNoneCenter_inv2 in H2; [ | exact H]]
            | [H2 : context[transNoneNoneLeft] |- _] => first [eapply transNoneNoneLeft_inv2 in H2; [ | exact H]] 
            | [H2 : context[transNoneNoneRight] |- _] => first [eapply transNoneNoneRight_inv2 in H2; [ | exact H]]
            | [H2 : context[transNoneNoneCenter] |- _] => first [eapply transNoneNoneCenter_inv2 in H2; [ | exact H]]
    end 
  | [H : trans (_, _) = (_, (_, positive)) |- _] => 
    repeat match goal with 
            | [H2 : context[transSomeSomeLeft] |- _] => first [eapply transSomeSomeLeft_inv1 in H2; [ | exact H]] 
            | [H2 : context[transSomeSomeRight] |- _] => first [eapply transSomeSomeRight_inv1 in H2; [ | exact H]]
            | [H2 : context[transSomeSomeCenter] |- _] => first [eapply transSomeSomeCenter_inv1 in H2; [ | exact H]]
            | [H2 : context[transNoneSomeLeft] |- _] => first [eapply transNoneSomeLeft_inv1 in H2; [ | exact H]] 
            | [H2 : context[transNoneSomeRight] |- _] => first [eapply transNoneSomeRight_inv1 in H2; [ | exact H]]
            | [H2 : context[transNoneSomeCenter] |- _] => first [eapply transNoneSomeCenter_inv1 in H2; [ | exact H]]
            | [H2 : context[transSomeNoneLeft] |- _] => first [eapply transSomeNoneLeft_inv1 in H2; [ | exact H]] 
            | [H2 : context[transSomeNoneRight] |- _] => first [eapply transSomeNoneRight_inv1 in H2; [ | exact H]]
            | [H2 : context[transSomeNoneCenter] |- _] => first [eapply transSomeNoneCenter_inv1 in H2; [ | exact H]]
            | [H2 : context[transNoneNoneLeft] |- _] => first [eapply transNoneNoneLeft_inv1 in H2; [ | exact H]] 
            | [H2 : context[transNoneNoneRight] |- _] => first [eapply transNoneNoneRight_inv1 in H2; [ | exact H]]
            | [H2 : context[transNoneNoneCenter] |- _] => first [eapply transNoneNoneCenter_inv1 in H2; [ | exact H]]
    end 
  end;try (transRules_inv2_once;try congruence; solve [simp_eqn]).  


  (** ** Halting rules*)

  (** these are the rules that leave the configuration unchanged in a halting configuration *)
  Inductive haltRules : transRule := 
  | haltCenter q (m1 m2 : stateSigma) m p : halt q = true -> haltRules (inr (inr (p, m1))) (inl (q, m)) (inr (inr (p, m2))) (inr (inr (neutral, m1))) (inl (q, m)) (inr (inr (neutral, m2)))
  | haltRight q (m1 m2 m : stateSigma) p : halt q = true -> haltRules (inr (inr (p, m1))) (inr (inr (p, m2))) (inl (q, m)) (inr (inr (neutral, m1))) (inr (inr (neutral, m2))) (inl (q, m)) 
  | haltLeft q (m1 m2 m : stateSigma) p : halt q = true -> haltRules (inl (q, m)) (inr (inr (p, m1))) (inr (inr (p, m2))) (inl (q, m)) (inr (inr (neutral, m1))) (inr (inr (neutral, m2))).

  Hint Constructors haltRules : trans.

  Ltac haltRules_inv1 :=
    match goal with
           | [H : haltRules _ _ _ _ _ _ |- _] => inv H
    end. 

  (** ** Combined rules for the simulation of Turing machines *)

  Definition simRules γ1 γ2 γ3 γ4 γ5 γ6 := transRules γ1 γ2 γ3 γ4 γ5 γ6 \/ haltRules γ1 γ2 γ3 γ4 γ5 γ6 \/ tapeRules γ1 γ2 γ3 γ4 γ5 γ6.  
  Hint Unfold simRules : trans. 

  Notation covHeadSim := (coversHeadInd simRules). 
  Ltac covHeadSim_inv1 :=
    repeat match goal with
    | [H : covHeadSim _ _ |- _] => inv H
    | [H : simRules _ _ _ _ _ _ |- _] => destruct H as [H | [H | H]]
    | [H : transRules _ _ _ _ _ _ |- _] => inv H
    | [H : haltRules _ _ _ _ _ _ |- _] => inv H
    | [H : tapeRules _ _ _ _ _ _ |- _] => inv H
    end.

  Hint Constructors valid : trans. 

  (** tape strings do not contain state symbols *)
  Definition isStateSym (γ : Gamma) := exists η, γ = inl η. 
  Definition isSpecStateSym (q : states) (γ : Gamma) := exists m, γ = inl (q, m). 

  Hint Unfold isStateSym : core.
  Hint Unfold isSpecStateSym : core.

  Lemma isStateSym_isSpecStateSym γ: isStateSym γ <-> exists q, isSpecStateSym q γ. 
  Proof.  
    split.
    - intros ([q m] & ?). eauto. 
    - intros (q & []). eauto. 
  Qed. 
 
  Lemma E_alphabet a p w : a el (E p w) -> a = inr (inr (p, |_|)) \/ a = inr #. 
  Proof. 
    intros H. induction w.  
    - cbn in H. firstorder. 
    - cbn in H. destruct H as [H | H]; firstorder.
  Qed.

  Lemma reprTape_no_isStateSym u p w h e : e el h -> u ≃t(p, w) h -> not (isStateSym e). 
  Proof. 
    intros H H0. destruct H0 as (_ & ->). 
    apply in_app_or in H. destruct H as [H | H]. 
    - unfold mapPolarity in H. apply in_map_iff in H as (m & H & _). intros (? & ->). congruence. 
    - apply E_alphabet in H. intros (? & ->). destruct H; congruence. 
  Qed. 

  (** ** A few simple facts about applicability of rules *)
  Lemma covHead_tape_sim s s' : s ⇝{tapeRules} s' -> s ⇝{simRules} s'.  
  Proof. intros. induction H as [ | | ? ? ? ? H IH H0]; [ | | inv H0]; eauto 6 with trans. Qed.  

  (** exactly one of the symbols for transitions or halting coverings is a state symbol *) 
  Lemma transRules_statesym1 γ1 γ2 γ3 γ4 γ5 γ6 : transRules γ1 γ2 γ3 γ4 γ5 γ6 -> isStateSym γ1 -> not (isStateSym γ2) /\ not (isStateSym γ3). 
  Proof. unfold isStateSym. intros H H0. destruct H0; split; intros []; transRules_inv2;congruence. Qed.  

  Lemma transRules_statesym2 γ1 γ2 γ3 γ4 γ5 γ6 : transRules γ1 γ2 γ3 γ4 γ5 γ6 -> isStateSym γ2 -> not (isStateSym γ1) /\ not (isStateSym γ3). 
  Proof. unfold isStateSym. intros H H0. destruct H0; split; intros []; transRules_inv2; congruence. Qed. 

  Lemma transRules_statesym3 γ1 γ2 γ3 γ4 γ5 γ6 : transRules γ1 γ2 γ3 γ4 γ5 γ6 -> isStateSym γ3 -> not (isStateSym γ1) /\ not (isStateSym γ2). 
  Proof. unfold isStateSym. intros H H0. destruct H0; split; intros []; transRules_inv2; congruence. Qed. 

  Lemma haltRules_statesym1 γ1 γ2 γ3 γ4 γ5 γ6 : haltRules γ1 γ2 γ3 γ4 γ5 γ6 -> isStateSym γ1 -> not (isStateSym γ2) /\ not (isStateSym γ3). 
  Proof. unfold isStateSym. intros H H0. destruct H0; split; intros []; haltRules_inv1; congruence. Qed. 

  Lemma haltRules_statesym2 γ1 γ2 γ3 γ4 γ5 γ6 : haltRules γ1 γ2 γ3 γ4 γ5 γ6 -> isStateSym γ2 -> not (isStateSym γ1) /\ not (isStateSym γ3). 
  Proof. unfold isStateSym. intros H H0. destruct H0; split; intros []; haltRules_inv1; congruence. Qed. 

  Lemma haltRules_statesym3 γ1 γ2 γ3 γ4 γ5 γ6 : haltRules γ1 γ2 γ3 γ4 γ5 γ6 -> isStateSym γ3 -> not (isStateSym γ1) /\ not (isStateSym γ2). 
  Proof. unfold isStateSym. intros H H0. destruct H0; split; intros []; haltRules_inv1; congruence. Qed. 

  Lemma transRules_statesym γ1 γ2 γ3 γ4 γ5 γ6 : transRules γ1 γ2 γ3 γ4 γ5 γ6 -> exists q, halt q = false /\ (isSpecStateSym q γ1 \/ isSpecStateSym q γ2 \/ isSpecStateSym q γ3).  
  Proof. unfold isSpecStateSym. intros. transRules_inv2; exists q; eauto. Qed.  

  Lemma haltRules_statesym γ1 γ2 γ3 γ4 γ5 γ6 : haltRules γ1 γ2 γ3 γ4 γ5 γ6 -> exists q, halt q = true /\ (isSpecStateSym q γ1 \/ isSpecStateSym q γ2 \/ isSpecStateSym q γ3).  
  Proof. unfold isSpecStateSym. intros. haltRules_inv1; exists q; eauto. Qed.  

  (** A string representing a tape half can only be rewritten using the tape rules *) 
  Lemma covHeadTrans_tape' u h h' p w: u ≃t(p, w) h -> covHeadSim h h' -> covHeadTape h h'.  
  Proof.  
    intros H H0. inv H0.  
    specialize (tape_repr_inv12 H) as H2. 
    destruct H1 as [ H1 | H1 ]; [ | destruct H1].  
    + apply transRules_statesym in H1. 
      destruct H1 as (q & _ & [(x & -> ) | [(x & ->) | (x & ->)]]). 
      all: destruct (H2 (inl (q, x))); [ eauto | congruence]. 
    + apply haltRules_statesym in H0.  
      destruct H0 as (q & _ & [(x & ->) | [(x & ->) | (x & ->)]]).  
      all: destruct (H2 (inl (q, x))); [eauto | congruence].  
    + eauto.  
  Qed.  

  Lemma covHeadSim_tape u h h' p w : u ≃t(p, w) h -> h ⇝{simRules} h' -> h ⇝{tapeRules} h'.  
  Proof.  
    intros H H0. revert u w H. induction H0 as [ | ? ? ? ? H0 IH H | ? ? ? ? H0 IH H]; intros u w H1.  
    - eauto with trans.  
    - constructor 2. 2: assumption. clear IH. 
      do 2 (destruct a; destruct b; try now cbn in H; try now inv H0; eauto with trans). 
    - constructor 3. 
      + destruct_tape_in H1.   
        * specialize (string_reprTapeP_length H1) as H1'. 
          destruct H1 as (_ & H2). cbn in H2. inv H2. cbn in H1'; destruct w.   
          -- apply valid_length_inv in H0. 
             do 3 (destruct b; try now cbn in H0). repeat constructor. 
          -- apply IH with (u := []) (w0 := w). apply niltape_repr.  
        * apply tape_repr_step in H1. now apply IH with (u := u) (w := w). 
      + now eapply covHeadTrans_tape'. 
  Qed.  

  (**We would also like to obtain the other direction for this result, i.e. for polarityRev h.
    This is a bit more tricky because we cannot reverse h in the ≃t predicate - thus, a straightforward induction will not go through.
    Instead, we use the equivalent characterisation via coversAt 
  *)
  Lemma covHeadSim_tape_polarityRev u h h' p w : 
    u ≃t(p, w) h -> (polarityRev h) ⇝{simRules} (polarityRev h') 
    -> (polarityRev h) ⇝{tapeRules} (polarityRev h'). 
  Proof.  
    intros. apply valid_iff. apply valid_iff in H0 as (H1 & H2).   
    split. 
    { apply H1. } 
    intros. specialize (H2 i H0).  
    unfold coversAt in *.  
    rewrite <- (firstn_skipn (|h| - i) h) in H.  
    apply tape_repr_polarityFlip in H. rewrite map_app in H.  
    rewrite map_firstn, map_skipn in H. 

    assert (0 <= i < (|h|)) as H3 by (unfold polarityRev in H0; rewrite rev_length, map_length in H0; lia).  
    rewrite firstn_skipn_rev in H. 
    rewrite map_length in H. replace ((|h|) - (|h| - i)) with i in H by lia.  
    clear H3.  

    specialize (skipn_length i (polarityRev h) ) as H3.  
    specialize (skipn_length i (polarityRev h')) as H4.  

    remember (skipn i (polarityRev h)) as h1.  
    remember (skipn i (polarityRev h')) as h2. 
    do 3 (destruct h1 as [ | ? h1]; cbn in *; [lia | ]).  
    do 3 (destruct h2 as [ | ? h2]; cbn in *; [lia | ]). 
    unfold polarityRev in Heqh1, Heqh2. rewrite <- Heqh1 in H. clear Heqh1 Heqh2 H1 H0 H3 H4.  

    apply coversHeadInd_rem_tail in H2.   
    apply coversHeadInd_rem_tail. 
    inv H2. destruct H1 as [H1 | [H1 | H1]].   
    - apply transRules_statesym in H1 as (q & _ & [H1 | [H1 | H1]]).  
      all: match type of H1 with isSpecStateSym ?q ?s => assert (exists q, isSpecStateSym q s) as H2 by eauto; apply isStateSym_isSpecStateSym in H2;  
      eapply (reprTape_no_isStateSym) with (e := s) in H; [ congruence | ] end.  
      all: apply in_or_app; left; rewrite <- in_rev; eauto.  
    - apply haltRules_statesym in H1 as (q & _ & [H1 | [H1 | H1]]).  
      all: match type of H1 with isSpecStateSym ?q ?s => assert (exists q, isSpecStateSym q s) as H2 by eauto; apply isStateSym_isSpecStateSym in H2;  
      eapply (reprTape_no_isStateSym) with (e := s) in H; [ congruence | ] end.  
      all: apply in_or_app; left; rewrite <- in_rev; eauto. 
    - eauto.  
   Qed.  
     
  (** If we are not in a halting state, but have a state symbol, the step must be due to a transition rule *) 
  Lemma covHeadSim_trans q γ1 γ2 γ3 γ4 γ5 γ6 : 
    (isSpecStateSym q γ1 \/ isSpecStateSym q γ2 \/ isSpecStateSym q γ3) 
    -> halt q = false 
    -> simRules γ1 γ2 γ3 γ4 γ5 γ6 
    -> transRules γ1 γ2 γ3 γ4 γ5 γ6. 
  Proof.  
    intros [H1 | [H1 | H1]]; (intros H0 H; destruct H as [H | H]; [eauto | destruct H; [ | destruct H1; covHeadTape_inv2; congruence]]).   
    all: specialize (haltRules_statesym H) as (q' & H2 & [H3 | [H3 | H3]]).  
    all: try match goal with 
             | [ H : isSpecStateSym ?q1 ?g, H' : isSpecStateSym ?q2 ?g |- _ ] => destruct H, H'; congruence 
             | [H : haltRules ?g1 _ _ _ _ _, H1 : isSpecStateSym _ ?g1, H2 : isSpecStateSym _ ?g2 |- _] => 
               apply haltRules_statesym1 in H; [ rewrite !isStateSym_isSpecStateSym in H; destruct H; exfalso; eauto| apply isStateSym_isSpecStateSym; eauto ] 
             | [H : haltRules _ ?g1 _ _ _ _, H1 : isSpecStateSym _ ?g1, H2 : isSpecStateSym _ ?g2 |- _] => 
               apply haltRules_statesym2 in H; [ rewrite !isStateSym_isSpecStateSym in H; destruct H; exfalso; eauto| apply isStateSym_isSpecStateSym; eauto ] 
             | [H : haltRules _ _ ?g1 _ _ _, H1 : isSpecStateSym _ ?g1, H2 : isSpecStateSym _ ?g2 |- _] => 
               apply haltRules_statesym3 in H; [ rewrite !isStateSym_isSpecStateSym in H; destruct H; exfalso; eauto| apply isStateSym_isSpecStateSym; eauto ] 
              end.  
  Qed.  

  (** If we are in a halting state and have a state symbol, the step must be due to a halting rule *) 
  Lemma covHeadSim_halt q γ1 γ2 γ3 γ4 γ5 γ6 : 
    (isSpecStateSym q γ1 \/ isSpecStateSym q γ2 \/ isSpecStateSym q γ3) 
    -> halt q = true 
    -> simRules γ1 γ2 γ3 γ4 γ5 γ6 
    -> haltRules γ1 γ2 γ3 γ4 γ5 γ6. 
  Proof.  
    intros [H1 | [H1 | H1]]; (intros H0 H; destruct H as [H | H]; [ | destruct H; [ eauto | destruct H1; covHeadTape_inv2; congruence]]). 
    all: specialize (transRules_statesym H) as (q' & H2 & [H3 | [H3 | H3]]). 
    all: try match goal with 
             | [ H : isSpecStateSym ?q1 ?g, H' : isSpecStateSym ?q2 ?g |- _ ] => destruct H, H'; congruence 
             | [H : transRules ?g1 _ _ _ _ _, H1 : isSpecStateSym _ ?g1, H2 : isSpecStateSym _ ?g2 |- _] => 
               apply transRules_statesym1 in H; [ rewrite !isStateSym_isSpecStateSym in H; destruct H; exfalso; eauto| apply isStateSym_isSpecStateSym; eauto ] 
             | [H : transRules _ ?g1 _ _ _ _, H1 : isSpecStateSym _ ?g1, H2 : isSpecStateSym _ ?g2 |- _] => 
               apply transRules_statesym2 in H; [ rewrite !isStateSym_isSpecStateSym in H; destruct H; exfalso; eauto| apply isStateSym_isSpecStateSym; eauto ] 
             | [H : transRules _ _ ?g1 _ _ _, H1 : isSpecStateSym _ ?g1, H2 : isSpecStateSym _ ?g2 |- _] => 
               apply transRules_statesym3 in H; [ rewrite !isStateSym_isSpecStateSym in H; destruct H; exfalso; eauto| apply isStateSym_isSpecStateSym; eauto ] 
              end.  
  Qed.  

  (** ** A few more technical facts regarding coverings *) 

  Lemma valid_reprConfig_unfold pred s q tp : 
    (exists s', valid pred s s' /\ (forall s'', valid pred s s'' -> s'' = s') /\ (q, tp) ≃c s') 
    <-> (exists ls qm rs, valid pred s (rev ls ++ [qm] ++ rs) /\ 
          (forall s'', valid pred s s'' -> s'' = rev ls ++ [qm] ++ rs) /\ (q, tp) ≃c (ls, qm, rs)). 
  Proof.  
    unfold reprConfig.  
    split. 
    - intros (s' & H & H' & (ls & qm & rs & -> & H1)). exists ls, qm, rs. eauto.  
    - intros (ls & qm & rs & H1 & H2 & H3). exists (rev ls ++ [qm] ++ rs). split; [ | split]; eauto.  
  Qed.  

  Lemma coversHeadInd_single (X : Type) pred (x1 x2 x3 x4 x5 x6 : X) : 
    pred x1 x2 x3 x4 x5 x6 <-> coversHeadInd pred [x1; x2; x3] [x4; x5; x6].  
  Proof. 
    split. 
    - intros H; now constructor. 
    - intros H; now inv H.  
  Qed.  
    
  (** A somewhat ugly but necessary lemma...*) 
  (** This enables us to justify a configuration string rewrite by rewriting the two tape halves and then applying three rules at the center *) 
  Lemma valid_coversHeadInd_center (X : Type) (p : X -> X -> X -> X -> X -> X -> Prop) A B (c d e f g : X) A' B' (c' d' e' f' g' : X) : 
    (valid (coversHeadInd p) (A ++ [c; d; e; f; g] ++ B) (A' ++ [c'; d'; e'; f'; g'] ++ B') /\ |A| = |A'| /\ |B| = |B'|) 
    <-> (valid (coversHeadInd p) (A ++ [c; d]) (A' ++ [c'; d']) /\ valid (coversHeadInd p) (f :: g :: B) (f' :: g' :: B') /\ 
       p c d e c' d' e' /\ p d e f d' e' f' /\ p e f g e' f' g'). 
  Proof.  
    split; intros.  
    - destruct H as (H1 & H2 & H3). apply valid_iff in H1 as (H0 & H1). 
      repeat rewrite app_length in H0. cbn in H0.  
      repeat split. 
      + apply valid_iff. split; [rewrite !app_length; cbn; lia | ].   
        intros. eapply coversAt_coversHeadInd_rem_at_end.  
        1: rewrite <- !app_assoc; cbn; eapply H1.  
        1: repeat rewrite app_length in *; cbn in *; lia.  
        all: repeat rewrite app_length in *; cbn in *; lia.  
      + apply valid_iff. split; [cbn ; lia | ]. 
        intros. specialize (H1 (i + |A| + 3)). 
        rewrite !app_length in H1. replace (i + ((|A|) + 3)) with ((3 + |A|) + i) in H1 by lia. 
        replace (A ++ [c; d; e; f; g] ++ B) with (A ++ [c; d; e] ++ f :: g :: B) in H1 by auto.  
        replace (A' ++ [c'; d'; e'; f'; g'] ++ B') with (A' ++ [c'; d'; e'] ++ f' :: g' :: B') in H1 by auto.  
        unfold coversAt in H1.  
        rewrite !app_assoc in H1.  
        rewrite !skipn_add  in H1. 2, 3: rewrite app_length; cbn; lia.  
        apply H1. cbn in *; lia.  
      + specialize (H1 (|A|)). unfold coversAt in H1. rewrite !skipn_app in H1. 2, 3: lia.  
        cbn in H1. rewrite coversHeadInd_tail_invariant with (s1' := []) (s2' := []) in H1. 
        apply coversHeadInd_single, H1. rewrite app_length; cbn; lia.  
      + specialize (H1 (S (|A|))). unfold coversAt in H1. 
        replace (A ++ [c; d; e; f; g] ++ B) with ((A ++ [c]) ++ [d; e; f; g] ++ B) in H1 by (rewrite <- app_assoc; now cbn).  
        replace (A' ++ [c'; d'; e'; f'; g'] ++ B') with ((A' ++ [c']) ++ [d';e';f';g'] ++ B') in H1 by (rewrite <- app_assoc; now cbn).  
        rewrite !skipn_app in H1. 2, 3: rewrite app_length; cbn; lia. 
        cbn in H1. rewrite coversHeadInd_tail_invariant with (s1' := []) (s2' := []) in H1. 
        apply coversHeadInd_single, H1. rewrite !app_length; cbn; lia. 
      + specialize (H1 (S (S (|A|)))). unfold coversAt in H1. 
        replace (A ++ [c; d; e; f; g] ++ B) with ((A ++ [c;d]) ++ [e; f; g] ++ B) in H1 by (rewrite <- app_assoc; now cbn).  
        replace (A' ++ [c'; d'; e'; f'; g'] ++ B') with ((A' ++ [c'; d']) ++ [e';f';g'] ++ B') in H1 by (rewrite <- app_assoc; now cbn).  
        rewrite !skipn_app in H1. 2, 3: rewrite app_length; cbn; lia. 
        cbn in H1. rewrite coversHeadInd_tail_invariant with (s1' := []) (s2' := []) in H1. 
        apply coversHeadInd_single, H1. rewrite !app_length; cbn; lia. 
   - destruct H as (H1 & H2 & H3 & H4 & H5). 
     assert (|A| = |A'|). { apply valid_length_inv in H1. rewrite !app_length in H1; cbn in H1; lia. } 
     assert (|B| = |B'|). { apply valid_length_inv in H2. cbn in H2; lia. } 
     repeat split. 
     2, 3: assumption.  
     apply valid_iff. split.  
     + rewrite !app_length. cbn. lia.  
     + intros. rewrite !app_length in H6; cbn in H6. 
       destruct (le_lt_dec (|A|) i); [destruct (le_lt_dec (|A| + 3) i) | ]. 
       * (*rhs*) assert (exists j, i = (|A|) + 3 + j) as (j & ->) by (exists (i - (|A|) - 3); lia).  
          replace (A ++ [c; d; e; f; g] ++ B) with (A ++ [c; d; e] ++ [f; g] ++ B) by now cbn. 
          replace (A' ++ [c'; d'; e'; f'; g'] ++ B') with (A' ++ [c';d';e'] ++ [f';g'] ++ B') by now cbn.  
          unfold coversAt. rewrite app_assoc. setoid_rewrite app_assoc at 2. 
          rewrite !skipn_add. 
          2,3: rewrite app_length; now cbn. 
          cbn. apply valid_iff in H2 as (H2' & H2). apply H2. 
          cbn. lia.  
      * (* middle*) 
        destruct (nat_eq_dec i (|A|)); [ | destruct (nat_eq_dec i (S (|A|)))].  
        ++ unfold coversAt. rewrite !skipn_app. 2,3:lia.  
           cbn. now apply coversHeadInd_tail_invariant with (s1' := []) (s2' := []). 
        ++ replace (A ++ [c; d; e; f; g] ++ B) with (A ++ [c] ++ [d; e; f; g] ++ B) by now cbn. 
           replace (A' ++ [c'; d'; e'; f'; g'] ++ B') with (A' ++ [c'] ++ [d'; e'; f';g'] ++ B') by now cbn.  
           unfold coversAt. rewrite app_assoc. setoid_rewrite app_assoc at 2. 
           rewrite !skipn_app. 2, 3: rewrite app_length; now cbn.  
           now apply coversHeadInd_tail_invariant with (s1' := []) (s2' := []). 
       ++ assert (i = S (S (|A|))) by lia. clear n n0 l1 l0.  
          replace (A ++ [c; d; e; f; g] ++ B) with (A ++ [c; d] ++ [e; f; g] ++ B) by now cbn. 
           replace (A' ++ [c'; d'; e'; f'; g'] ++ B') with (A' ++ [c'; d'] ++ [e'; f';g'] ++ B') by now cbn.  
           unfold coversAt. rewrite app_assoc. setoid_rewrite app_assoc at 2. 
           rewrite !skipn_app. 2, 3: rewrite app_length; now cbn.  
           now apply coversHeadInd_tail_invariant with (s1' := []) (s2' := []). 
    * (*lhs*) 
      apply valid_iff in H1 as (H1' & H1). specialize (H1 i).  
      rewrite app_length in H1; cbn in H1. replace ((|A|) + 2 - 2) with (|A|) in H1 by lia.   
      replace (A ++ [c; d; e; f; g] ++ B) with (A ++ [c; d] ++ [e; f; g] ++ B) by now cbn. 
      replace (A' ++ [c'; d'; e'; f'; g'] ++ B') with (A' ++ [c'; d'] ++ [e'; f';g'] ++ B') by now cbn. 
      rewrite app_assoc. setoid_rewrite app_assoc at 2.  
      eapply coversAt_coversHeadInd_add_at_end.  
      now apply H1.  
  Qed.  

  (** if we start with a string of such a form, then the resulting string will also have this form *) 
  Lemma valid_conc_inv (X : Type) pred s' A B (a b c d e : X)  : 
    valid (X := X) pred (A ++ [a; b; c; d; e] ++ B) s' 
    -> exists A' B' (a' b' c' d' e' : X), s' = A' ++ [a'; b'; c'; d'; e'] ++ B' /\ |A| = |A'| /\ |B|= |B'|. 
  Proof.  
    intros. apply valid_length_inv in H. 
    rewrite <-  (firstn_skipn (|A|) s'). rewrite <- (firstn_skipn 5 (skipn (|A|) s')).  
    exists (firstn (|A|) s'). 
    specialize (skipn_length (|A|) s') as H1. specialize (firstn_length (|A|) s') as H2.  
    specialize (firstn_length (5) (skipn (|A|) s')) as H3. 
    specialize (skipn_length (5) (skipn (|A|) s')) as H4.  
    rewrite H1 in H3, H4. clear H1.  
    rewrite !app_length in H. cbn [Nat.add length] in H.  
    assert (Init.Nat.min 5 (|s'| - |A|) = 5)  by lia. rewrite H0 in H3. clear H0.  
    exists (skipn 5 (skipn (|A|) s')).  
    remember (firstn 5 (skipn (|A|) s')) as l.  
    do 5 (destruct l as [ | ? l]; [now cbn in H3 | ]). destruct l; [ | now cbn in H3].  
    exists x, x0, x1, x2, x3.  
    repeat split. 
    - rewrite H2. lia.   
    - rewrite H4. lia.  
  Qed.  

  Lemma app_fold5 (X : Type) (a b c d e: X) (l : list X) : a :: b :: c :: d :: e :: l = [a; b; c; d; e] ++ l.  
  Proof. now cbn. Qed.  

  (** ** Automation for the simulation proofs *) 

  (** brings the goal into a form in which valid_covHeadSim_center can be applied *) 
  (** precondition: the tape strings have been destructed such that there are at least two symbols available in each direction, both in premise and conclusion *) 
  Ltac normalise_conf_string H := cbn in H; 
    try match type of H with 
    | context[((_) ++ [_]) ++ (inl _) :: _] => do 2 (rewrite <- app_assoc in H); cbn in H 
    | context[((_) ++ [_]) ++ _ :: (inl _) :: _] => rewrite <- app_assoc in H; cbn in H 
    end. 

  Ltac normalise_conf_strings := match goal with 
    | [ |- ?h1 ⇝{simRules} ?h2 ] => let H1 := fresh in let H2 := fresh in 
                                        let H1' := fresh "Heqn" in let H2' := fresh "Heqn" in 
                                        remember h1 as H1 eqn:H1'; remember h2 as H2 eqn:H2'; 
                                        normalise_conf_string H1'; normalise_conf_string H2'; 
                                        subst H1 H2 
    end.  

  Ltac normalise_conf_strings_in H := match type of H with 
    | ?h1 ⇝{simRules} ?h2 => let H1 := fresh in let H2 := fresh in 
                                 let H1' := fresh "Heqn" in let H2' := fresh "Heqn" in 
                                 remember h1 as H1 eqn:H1'; remember h2 as H2 eqn:H2'; 
                                 normalise_conf_string H1'; normalise_conf_string H2'; 
                                 subst H1 H2 
    end.  

  (** try to eliminate variables from the goal in the context of niltapes, i.e. substitute eqns such as S n = z so that we have a z in the goal again *) 
  Ltac clear_niltape_eqns := repeat match goal with 
    | [ H : ?n = z |- context[?n]] => rewrite !H 
    | [ H : S ?n = z |- context[inr(inr (?p, |_|)) :: E ?p ?n]] => 
      replace (inr (inr (p, |_|)) :: E p n) with (E p (S n)) by (now cbn); rewrite !H 
    | [H : S (S ?n) = z |- context[inr(inr (?p, |_|)) :: inr (inr (?p, |_|)) :: E ?p ?n]] => 
      replace (inr (inr (p, |_|)) :: inr (inr (p, |_|)) :: E p n) with (E p (S (S n))) by (now cbn); rewrite !H 
    | [H : S ?n = z |- context[rev(E ?p ?n) ++ inr (inr (?p, |_|)) :: ?h]] => 
      replace (rev (E p n) ++ (inr (inr (p, |_|)) : Gamma) :: h) with (rev (E p (S n) ++ h)) by (cbn; try rewrite <- app_assoc; easy); rewrite !H 
    | [H : S ?n = z |- context[(rev (E ?p ?n)) ++ [inr (inr (?p, |_|))] ++ ?h]] => rewrite app_assoc 
    | [H : S ?n = z |- context[(rev (E ?p ?n) ++ [inr (inr (?p, |_|))]) ++ ?h]] => 
      replace (rev (E p n) ++ [inr (inr (p, |_|)) : Gamma]) with (rev (E p (S n))) by (cbn; try rewrite <- app_assoc; easy); rewrite !H 
  end. 

  (** determine if a tape half is blank *) 
  Ltac is_half_blank F := match type of F with [] ≃t(_,_) _ => constr:(true) |  _ => constr:(false) end. 

  (** get the next symbol which will be under the head *) 
  Ltac get_next_headsym' F := match type of F with [] ≃t(_, _) _ => constr:(|_| : stateSigma)  
                                             | ?σ :: _ ≃t(_, _) _ => constr:(Some σ : stateSigma) 
                                       end. 
  
  Ltac get_next_headsym F1 F2 csym wsym dir := match wsym with 
   | Some ?wsym => match dir with 
                     | Lmove => get_next_headsym' F1 
                     | Rmove => get_next_headsym' F2 
                     | Nmove => constr:(Some wsym : stateSigma) 
                   end 
   | None => match dir with 
                 | Lmove => match csym with Some ?csym => get_next_headsym' F1 
                                 | _ => match is_half_blank F2 with true => get_next_headsym' F1 
                                                               | false => constr:(|_| : stateSigma) 
                                       end 
                       end 
                 | Rmove => match csym with Some ?csym => get_next_headsym' F2 
                                 | _ => match is_half_blank F1 with true => get_next_headsym' F2 
                                                                 | false =>  constr:(|_| : stateSigma) 
                                       end 
                     end 
                 | Nmove => constr:(csym : stateSigma) 
               end 
     end.  

  (** find out the symbol which the TM writes*) 
  (** remember that we take the view that the TM also writes a symbol if it leaves it unchanged*) 
  (** csym = current symbol under head; wsym: symbol given by the transition function *) 
  Ltac get_written_sym csym wsym := match wsym with 
   | Some ?wsym => constr:(Some wsym : stateSigma) 
   | None => match csym with 
           | Some ?csym => constr:(Some csym : stateSigma) 
           | None => constr:(|_| : stateSigma) 
           end 
     end. 

  (** get the direction in which the tape must be shifted *) 
  (** wsym: written sym as computed by get_written_sym *) 
  Ltac get_shift_direction wsym dir F1 F2 := match dir with 
   | Lmove => match wsym with None => match is_half_blank F1 with true => constr:(neutral) 
                                                       | false => constr:(positive) 
                                 end 
                     | Some _ => constr:(positive) 
         end 
   | Rmove => match wsym with None => match is_half_blank F2 with true => constr:(neutral) 
                                                       | false => constr:(negative) 
                                 end 
                     | Some _ => constr:(negative) 
         end 
   | Nmove => constr:(neutral) 
   end.  

   Ltac simRulesAuto :=
    lazymatch goal with
    | H : halt ?q = false |- simRules ?x ?y ?z  _ _ _ =>
      lazymatch goal with
      | H' : trans (q, ?s) = (?q', (?s', ?dir)) |- _ => left;
        let numState := lazymatch x with inl _ => constr:(0) | _ => lazymatch y with inl _ => constr:(1) | _ => lazymatch z with inl _ => constr:(2) end end end in
        lazymatch s with
        | None =>
          lazymatch s' with
          | None => refine (transNoneNoneC H _);
            lazymatch numState with 0 => refine  (transNNLeft _) | 1 => refine  (transNNCenter _) | 2 => refine  (transNNRight _) end
          | Some _ =>  refine ( transNoneSomeC H _);
            lazymatch numState with 0 => refine  (transNSLeft _) | 1 => refine  (transNSCenter _) | 2 => refine  (transNSRight _) end
          end
        | Some _ =>
          lazymatch s' with
          | None =>  refine ( transSomeNoneC H _);
          lazymatch numState with 0 => refine  (transSNLeft _) | 1 => refine  (transSNCenter _) | 2 => refine  (transSNRight _) end            
          | Some _ =>  refine ( transSomeSomeC H _);
          lazymatch numState with 0 => refine  (transSSLeft _) | 1 => refine  (transSSCenter _) | 2 => refine  (transSSRight _) end            
          end
        end;[econstructor;[eassumption|solve[repeat (eassumption + econstructor)]]]
      | |- _ => right;right; solve [eauto 7 with trans nocore]
      end
    | H : halt ?q = true |- simRules _ _ _ _ _ _ => right;left;solve[ eauto 7 with trans nocore]
    end.

  (** solve the part of the goal where we have to prove that the covering is valid *) 
  Ltac solve_stepsim_cover_valid Z := apply covHead_tape_sim; revert Z; try clear_niltape_eqns; cbn; try rewrite <- !app_assoc; auto.
  Ltac solve_stepsim_covering Z1 W1 := 
    normalise_conf_strings; apply valid_coversHeadInd_center; repeat split; 
    [solve_stepsim_cover_valid Z1 | solve_stepsim_cover_valid W1 | | | ]; 
    lazymatch goal with 
    | [ |- simRules _ _ _ _ _ _ ] => solve [(*eauto 7 with trans nocore tmp;*)try simRulesAuto;shelve]
    end.
  Create HintDb tmp discriminated.
   Hint Variables Opaque : tmp.
  Hint Variables Opaque : trans. 
  (*  Hint Constants Opaque : tmp.
  Hint Constants Opaque : trans. *)

  Local Hint Constructors identityRules : tmp.
  Local Hint Constructors shiftRightRules : tmp.
  Local Hint Constructors tapeRules : tmp.
  Local Hint Constructors eq : tmp.
  Local Hint Constructors or : tmp.


  Ltac solve_stepsim_repr shiftdir Z2 W2 := exists shiftdir; cbn; (split; [now cbn | split; [apply Z2 | apply W2]]). 

  (** automation for the uniqueness part *) 
  Lemma rev_fold (X : Type) (A B : list X) b: rev A ++ (b::B) = rev (b :: A) ++ B.  
  Proof.  
    cbn. rewrite <- app_assoc. now cbn.  
  Qed.  

  Lemma rev_polarityRev A : rev A = polarityRev (map polarityFlipGamma A).  
  Proof.  
    unfold polarityRev. rewrite map_involution. reflexivity. involution_simpl.  
  Qed.  

  (*a rather technical statement which allows us to derive uniqueness for the reversed left tape string  *) 
  Lemma covHeadSim_unique_left A B A' a b a' b' u p w: valid covHeadSim (rev A ++ [b; a]) (A' ++ [b'; a']) -> u ≃t(p, w) a :: b :: A -> (forall s, valid covHeadTape (rev (a :: b :: A)) (rev (a' :: s)) -> s = B) -> b' :: rev A' = B. 
  Proof.  
    intros.  
    repeat rewrite rev_fold in H. rewrite app_nil_r in H.  
    setoid_rewrite <- polarityRev_involution in H at 5.  
    rewrite rev_polarityRev in H.  
    eapply covHeadSim_tape_polarityRev in H.  
    2: { cbn; apply tape_repr_polarityFlip in H0. cbn in H0. apply H0. } 
    rewrite <- rev_polarityRev in H. rewrite polarityRev_involution in H.  
    rewrite <- rev_involutive with (l := A') in H.  
    repeat rewrite rev_fold in H. rewrite app_nil_r in H.  
    apply H1 in H. easy.  
  Qed.  

  
Ltac transRules_semCases K H :=
    let K' := fresh "K" in
    let H' := fresh "H'" in
    lazymatch type of K with
    | transRules (inl _) _ _ _ _ _ => specialize (transRules_semCasesLeft) with (1:=K) (2:=H) as [H' K']
    | transRules _ (inl _) _ _ _ _ => specialize (transRules_semCasesCenter) with (1:=K) (2:=H) as K'
    | transRules _ _ (inl _)  _ _ _ => specialize (transRules_semCasesRight) with (1:=K) (2:=H) as [H' K']
  end;cbn beta iota zeta in K';inv_eqn K';try (specialize (H' eq_refl);injection H' as [= ->]).

Ltac solve_stepsim_uniqueness' H H2 F1 F2 Z3 W3 :=        
  cbn in H; rewrite <- !app_assoc in H; cbn in H;  
  rewrite app_fold5 in H;  
  let X1 := fresh "X1" in let X2 := fresh "X2" in  
  destruct (valid_conc_inv H) as (? & ? & ? & ? & ? & ? & ? & -> & X1 & X2); 
  normalise_conf_strings_in H;  
  let K1 := fresh "K1" in let K2 := fresh "K2" in let K3 := fresh "K3" in 
  let K4 := fresh "K4" in let K5 := fresh "K5" in 
  specialize (proj1 (valid_coversHeadInd_center simRules _  _ _ _ _ _ _ _ _ _ _ _ _ _) (conj H (conj X1 X2))) as (K1 & K2 & K3 & K4 & K5);  
  eapply covHeadSim_trans in K3; [ | eauto | eassumption];  
  eapply covHeadSim_trans in K4; [ | eauto | eassumption]; 
  eapply covHeadSim_trans in K5; [ | eauto | eassumption];
  transRules_semCases K3 H2; transRules_semCases K4 H2;transRules_semCases K5 H2;
  specialize (covHeadSim_unique_left K1 F1 Z3) as ?;
  simp_eqn; 
  eapply covHeadSim_tape in K2; [ | eapply F2]; apply W3 in K2;  
  simp_eqn;  
  cbn; try rewrite <- !app_assoc; cbn; foldAbbrevs;simp_eqn;reflexivity.

  Notation "s '⇝' s'" := (valid covHeadSim s s') (at level 40). 

  (** main simulation result: a single step of the Turing machine corresponds to a single step of the CC instance (if we are not in a halting state) *)
  (** proof takes roughly 35mins + 4 gigs of RAM... *)
  Lemma stepsim q tp s q' tp' :
    (q, tp) ≃c s
    -> (q, tp) ≻ (q', tp')
    -> (sizeOfTape tp) < z
    -> exists s', s ⇝ s' /\ (forall s'', s ⇝ s'' -> s'' = s') /\ (q', tp') ≃c s'.
  Proof. 
    Set Default Goal Selector "all".
    intros H (H0' &  H0) H1. cbn in H0'. unfold sstep in H0. destruct trans eqn:H2 in H0. inv H0. rename p into p'. 
    apply valid_reprConfig_unfold. 
    rewrite sizeOfTape_lcr in H1. 

    destruct H as (ls & qm & rs & -> & H). destruct H as (p & -> & F1 & F2). unfold embedState. 
    destruct p' as ([wsym | ] & []); destruct tp as [ | ? l1 | ? l0 | l0 ? l1]; cbn in *; destruct_tape_in_tidy F1; destruct_tape_in_tidy F2. 

    idtac "proving stepsim lemma - this may take a few minutes".

    time "case destinctions"
    try match type of F1 with ?l0 ≃t(_, _) _ => is_var l0; destruct l0 as [ | ? l0]; destruct_tape_in_tidy F1 end;
    try match type of F1 with _ :: ?l0 ≃t(_, _) _ => destruct l0 as [ | ? l0]; destruct_tape_in_tidy F1 end;
    try match type of F2 with ?l1 ≃t(_, _) _ => is_var l1; destruct l1 as [ | ? l1]; destruct_tape_in_tidy F2 end;
    try match type of F2 with _ :: ?l1 ≃t(_, _) _ => destruct l1 as [ | ? l1]; destruct_tape_in_tidy F2 end. 
    (* 84 goals *)

    cbn in H1.
    foldAbbrevs. 
    time "main proof except uniqueness"
    (*analyse what transition should be taken, instantiate the needed lemmas and solve all of the obligations except for uniqueness*)
    lazymatch type of H2 with 
      | trans (?q, ?csym) = (?q', (?wsym, ?dir)) => 
        let nextsym := get_next_headsym F1 F2 csym wsym dir in 
        let writesym := get_written_sym csym wsym in 
        let shiftdir := get_shift_direction writesym dir F1 F2 in 
        (*init next tape halves*)
        let Z1 := fresh "Z1" in let Z2 := fresh "Z2" in let Z3 := fresh "Z3" in 
        let W1 := fresh "W1" in let W2 := fresh "W2" in let W3 := fresh "W3" in 
        let h1 := fresh "h1" in let h2 := fresh "h2" in 
        cbn in F1 ; cbn in F2;
        lazymatch shiftdir with
        | Rmove => lazymatch type of F1 with 
              | [] ≃t(?p, ?w) _ => specialize (E_cover_blank_rev p shiftdir w) as [Z1 Z3]; 
                                  specialize (proj1 (@niltape_repr w shiftdir)) as Z2
              | _ => destruct (tape_repr_rem_left F1) as (h1 & Z1 & Z3 & Z2); 
                  (*need to have one more head symbol in that case*)
                    try match type of Z2 with _ :: ?l ≃t(_, _) _ => is_var l; 
                                                                  destruct l end; destruct_tape_in_tidy Z2 
              end; 
              lazymatch writesym with 
              | Some ?sym => (destruct (tape_repr_add_right sym F2) as (h2 & W1 & W3 & W2)); [cbn; lia | destruct_tape_in_tidy W2] 
              | None => 
                  match type of F2 with 
                  | [] ≃t(?p, ?w) _ => specialize (E_cover_blank p shiftdir w) as [W1 W3]; 
                                      specialize (proj1 (@niltape_repr w shiftdir)) as W2
                  end 
              end
        | Lmove => lazymatch type of F2 with 
              | [] ≃t(?p, ?w) _ => specialize (E_cover_blank p shiftdir w) as [W1 W3]; 
                                  specialize (proj1 (@niltape_repr w shiftdir)) as W2
                | _ => destruct (tape_repr_rem_right F2) as (h2 & W1 & W3 & W2); 
                    (*need to have one more head symbol in that case *)
                      try match type of W2 with _ :: ?l ≃t(_, _) _ => is_var l; 
                                                                    destruct l end; destruct_tape_in_tidy W2 
              end; 
              lazymatch writesym with 
                Some ?sym => destruct (tape_repr_add_left sym F1) as (h1 & Z1 & Z3 & Z2); [cbn; lia | destruct_tape_in_tidy Z2] 
              | None => match type of F1 with 
                      | [] ≃t(?p, ?w) _ => specialize (E_cover_blank_rev p shiftdir w) as [Z1 Z3]; 
                                          specialize (proj1 (@niltape_repr w shiftdir)) as Z2 
                  end 
            end
        | Nmove => destruct (tape_repr_stay_left F1) as (h1 & Z1 & Z3 & Z2); destruct_tape_in_tidy Z2; 
              destruct (tape_repr_stay_right F2) as (h2 & W1 & W3 & W2); destruct_tape_in_tidy W2 
        end;foldAbbrevs (*in *|- *); 

      (*instantiate existenials *)
      match type of Z2 with _ ≃t(_, _) ?h => exists h end; 
      exists (inl (q', nextsym) : Gamma); 
      match type of W2 with _ ≃t(_, _) ?h => exists h end; 

      (*solve goals, except for the uniqueness goal (factored out due to performance)*)
      (split; [ abstract (solve_stepsim_covering Z1 W1) | split; [  | abstract solve_stepsim_repr shiftdir Z2 W2]]) 
     end.
    (* 100 goals*)
    
    (*solve the uniqueness obligations - this is very expensive because of the needed inversions *)
    (*therefore abstract into opaque lemmas *)
    idtac "solving uniqueness".
    unfold wo; cbn [Nat.add]; clear_niltape_eqns; intros s H; clear Z1 W1 W2 Z2; clear H1;foldAbbrevs; 
    abstract (solve_stepsim_uniqueness' H H2 F1 F2 Z3 W3).
    idtac "stepsim - done".
  Qed.

  (** if we are in a halting state, we can only rewrite to the same string (identity), except for setting the polarity to neutral *)
  Lemma haltsim q tp s :
    (q, tp) ≃c s
    -> halt q = true
    -> exists s', s ⇝ s' /\ (forall s'', s ⇝ s'' -> s'' = s') /\ (q, tp) ≃c s'.
  Proof.
    Set Default Goal Selector "all". 
    intros. apply valid_reprConfig_unfold. 
    destruct H as (ls & qm & rs & H1 & H2). 
    destruct H2 as (p & F0 & F1 & F2). 
    unfold reprTape in F1, F2. unfold embedState in F0. 
    destruct tp as [ | ? l1 | ? l0 | l0 ? l1]; cbn in *. 
    destruct_tape_in F1; destruct_tape_in F2. 
    try match type of F1 with ?l0 ≃t(_, _) _ => is_var l0; destruct l0 as [ | ? l0]; destruct_tape_in_tidy F1 end. 
    try match type of F1 with _ :: ?l0 ≃t(_, _) _ => destruct l0 as [ | ? l0]; destruct_tape_in_tidy F1 end. 
    try match type of F2 with ?l1 ≃t(_, _) _ => is_var l1; destruct l1 as [ | ? l1]; destruct_tape_in_tidy F2 end. 
    try match type of F2 with _ :: ?l1 ≃t(_, _) _ => destruct l1 as [ | ? l1]; destruct_tape_in_tidy F2 end. 
    specialize (tape_repr_stay_left F1) as (h1 & Z1 & Z3 & Z2). 
    specialize (tape_repr_stay_right F2) as (h2 & W1 & W3 & W2). 
    destruct_tape_in_tidy W2; destruct_tape_in_tidy Z2. 
    match type of Z1 with valid _ _ (rev ?h) => exists h end. 
    exists qm. 
    match type of W1 with valid _ _ ?h => exists h end. 
    subst. 
    split; [abstract solve_stepsim_covering Z1 W1 | split; [ |abstract solve_stepsim_repr neutral Z2 W2 ] ]. 
    (*uniqueness *) 
    (*mostly matches the corresponding stepsim tactic above, but uses different inversions and needs some additional plumbing with app in Z3*) 
    abstract (intros s H; clear Z1 W1 W2 Z2;  
    cbn in H; rewrite <- !app_assoc in H; cbn in H;  
    rewrite app_fold5 in H;  
    let X1 := fresh "X1" in let X2 := fresh "X2" in  
    destruct (valid_conc_inv H) as (? & ? & ? & ? & ? & ? & ? & -> & X1 & X2); 
    normalise_conf_strings_in H;  
    let K1 := fresh "K" in let K2 := fresh "K" in let K3 := fresh "K" in 
    let K4 := fresh "K" in let K5 := fresh "K" in 
    specialize (proj1 (valid_coversHeadInd_center simRules _ _ _ _ _ _ _ _ _ _ _ _ _ _) (conj H (conj X1 X2))) as (K1 & K2 & K3 & K4 & K5);  
    eapply covHeadSim_halt in K3; [ | eauto | eauto];  
    eapply covHeadSim_halt in K4; [ | eauto | eauto]; 
    eapply covHeadSim_halt in K5; [ | eauto | eauto];  
    repeat haltRules_inv1; simp_eqn; 
    try rewrite <- app_assoc in Z3; cbn in Z3; try rewrite !rev_fold in Z3; try rewrite app_nil_r in Z3; 
    (specialize (covHeadSim_unique_left K1 F1 Z3) as ?; 
    simp_eqn; 
    eapply covHeadSim_tape in K2; [ | eapply F2]; apply W3 in K2;  
    simp_eqn;  
    cbn; try rewrite <- !app_assoc; cbn; reflexivity)). 
    Set Default Goal Selector "1".
  Qed. 


  Set Default Goal Selector "1". 

  (** ** multi-step simulation *)

  Notation "s '≻(' k ')' s'" := (relpower (@sstepRel Sigma fTM) k s s') (at level 40). 

  (** this is similar to what loopM does*)
  Notation "s '▷(' k ')' s'" := (s ≻(k) s' /\ halt (configState s') = true) (at level 40).

  Notation "s '▷(≤' k ')' s'" := (exists l, l <= k /\ s ▷(l) s') (at level 40).
  Notation "s '⇝(' k ')' s'" := (relpower (valid covHeadSim) k s s') (at level 40).

  Lemma step_inversion q tp s s' :
    (q, tp) ≃c s
    -> sizeOfTape tp < z
    -> halt q = false
    -> s ⇝ s'
    -> exists! q' tp', (q', tp') ≃c s' /\ (q, tp) ≻ (q', tp').
  Proof.
    intros. 
    destruct (sstep (q, tp)) as (q', tp') eqn:H3. 
    assert ((q, tp) ≻ (q', tp')) as H4 by auto. 
    specialize (stepsim H H4 H0) as (s'' & F1 & F2 & F3 ). 
    apply F2 in H2.  subst.
    exists q'. split.
    + exists tp'. split.
      * repeat split; [apply F3 | now cbn]. 
      * intros. destruct H2 as (_ & _ & H2); congruence. 
    + intros. destruct H2 as (? & (_ & _ & H2) & _).  congruence. 
  Qed. 

  (** same thing without the uniqueness because of the hassle of dealing with exists! if one doesn't need uniqueness *)
  Lemma step_inversion' q tp s s' :
    (q, tp) ≃c s
    -> sizeOfTape tp < z
    -> halt q = false
    -> s ⇝ s'
    -> exists q' tp', (q', tp') ≃c s' /\ (q, tp) ≻ (q', tp').
  Proof. 
    intros. specialize (step_inversion H H0 H1 H2). intros. rewrite <- !unique_existence in H3.
    destruct H3 as ((q' & tp' & (H3 & _ )) & _ ). eauto. 
  Qed. 

  Lemma halting_inversion q tp s s' : (q, tp) ≃c s -> halt q = true -> s ⇝ s' -> (q, tp) ≃c s'. 
  Proof. 
    intros. specialize (haltsim H H0 ) as (s'' & H2 & H3 & H4). 
    apply H3 in H1. subst. apply H4.  
  Qed. 

  Lemma multistep_simulation q tp q' tp' l s :
    (q, tp) ≃c s
    -> (q, tp) ≻(l) (q', tp')
    -> z >= l
    -> (sizeOfTape tp) <= z - l
    -> exists s', s ⇝(l) s' /\ (forall s'', s ⇝(l) s'' -> s'' = s') /\ (q', tp') ≃c s'.
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
    - destruct b as (q''& tp''). assert (z >= n) as X by lia. specialize (IH X q'' tp'' q' tp' eq_refl eq_refl). clear X.
      unfold sstepRel in H. 
      specialize (stepsim H1 H ltac:(lia)) as (s' & F1 & F2 & F3).
      specialize (IH s' F3) as (s'' & G1 & G2 & G3). 
      apply tm_step_size with (l := sizeOfTape tp)in H. 2: reflexivity. lia. 
      exists s''. repeat split. 
      + eauto.  
      + intros. inv H0. apply F2 in H6. rewrite H6 in *. clear H6. now apply G2. 
      + apply G3. 
  Qed.

  Lemma multistep_halt q tp s :
    (q, tp) ≃c s
    -> halt q = true
    -> forall l, exists s', s ⇝(l) s' /\ (forall s'', s ⇝(l) s'' -> s'' = s') /\ (q, tp) ≃c s'.
  Proof. 
    intros. 
    revert s H.
    induction l0 as [ | l0 IH]; intros s H.
    - exists s. repeat split; eauto. intros. now inv H1. 
    - specialize (haltsim H H0) as (s' & F1 & F2 & F3). 
      destruct (IH s' F3) as (s'' & G1 & G2 & G3). exists s''. repeat split.
      + eauto. 
      + intros. inv H1. apply F2 in H3. rewrite H3 in *; clear H3. now apply G2. 
      + apply G3. 
  Qed. 

  Lemma multistep_inversion q tp s s' j:
    (q, tp) ≃c s
    -> s ⇝(j) s'
    -> sizeOfTape tp <= z - j
    -> z >= j
    -> exists q' tp' j', (q', tp') ≃c s' /\ j' <= j /\ (q, tp) ≻(j') (q', tp') /\ sizeOfTape tp' <= sizeOfTape tp + j'.
  Proof. 
    intros. apply relpower_relpowerRev in H0.
    induction H0 as [ | s y y' j H0 IH].  
    - exists q, tp, 0. rewrite Nat.add_0_r. repeat split; eauto.  
    - specialize (IH H ltac:(lia) ltac:(lia)) as (q' & tp' & j' & F1 & F2 & F3 & F4). 
      destruct (halt q') eqn:H4. 
      + exists q', tp', j'.
        specialize (halting_inversion F1 H4 H3) as H5. eauto. 
      + specialize (step_inversion' F1 ltac:(lia) H4 H3) as (q'' & tp'' & G1 & G2). 
        exists q'', tp'', (S j'). repeat split; eauto. 
        * lia.  
        * apply relpower_relpowerRev. econstructor.
          -- apply relpower_relpowerRev in F3; eauto.
          -- apply G2.  
        * apply tm_step_size with (l := sizeOfTape tp') in G2; [lia | reflexivity ].  
  Qed. 

  (** Our final constraint. We don't use the definition via a list of final substrings from the TCC definition, but instead use this more specific form. *)
  (** We will later show that the two notions are equivalent for a suitable list of final substrings.*)
  Definition containsHaltingState s := exists q qs, halt q = true /\ isSpecStateSym q qs /\ qs el s.  

  Lemma finalCondition q tp s : (q, tp) ≃c s -> (halt q = true <-> containsHaltingState s). 
  Proof.
    intros; split; intros.
    - destruct H as (ls & qm & rs & -> & H2). exists q, qm. repeat split; eauto. 
      destruct H2 as (p & -> & H3 & H4). unfold isSpecStateSym. unfold embedState. eauto. 
    - destruct H0 as (q' & qs & H1 & H2 & H3). enough (q = q') by congruence. 
      destruct H as (ls & qm & rs & -> & H4). destruct H4 as (p & -> & H5 & H6).
      apply in_app_or in H3; destruct H3 as [ | H3]; [ | apply in_app_or in H3; destruct H3 as [ | H3 ] ].
      + clear H6. destruct H2 as (m & ->). 
        apply in_rev in H. destruct H5 as ( _ & ->). apply in_app_iff in H. destruct H as [H | H]. 
        * unfold mapPolarity in H. apply in_map_iff in H as (σ & H & _). congruence. 
        * apply E_alphabet in H. destruct H; congruence.
      + destruct H as [ <- | []]. destruct H2. unfold embedState in H. congruence. 
      + clear H5. destruct H2 as (m & ->).
        destruct H6 as ( _ & ->). apply in_app_iff in H3. destruct H3 as [H | H]. 
        * unfold mapPolarity in H. apply in_map_iff in H as (σ & H & _). congruence. 
        * apply E_alphabet in H. destruct H; congruence.
  Qed. 

  Theorem completeness q tp q' tp' s :
    sizeOfTape tp <= k
    -> (q, tp) ≃c s
    -> (q, tp) ▷(≤t) (q', tp')
    -> exists s', s ⇝(t) s' /\ (q', tp') ≃c s' /\ containsHaltingState s'.
  Proof. 
    intros. 
    destruct H1 as (t' & H1 & (H2 & H3)). cbn in H3. 
    assert (z >= t') as H4 by (unfold z; lia). 
    assert (sizeOfTape tp <= z - t') as H5 by (unfold z; lia). 
    specialize (multistep_simulation H0 H2 H4 H5) as (s' & F1 & _ & F3). 
    specialize (multistep_halt F3 H3 (t - t')) as (s'' & G1 & _ & G3).
    exists s''. repeat split. 
    + replace t with (t' + (t - t')) by lia. eauto using relpower_trans. 
    + apply G3. 
    + eapply finalCondition; eauto. 
  Qed. 

  Theorem soundness q tp s s' :
    (q, tp) ≃c s
    -> sizeOfTape tp <= k
    -> s ⇝(t) s'
    -> containsHaltingState s'
    -> exists q' tp', (q', tp') ≃c s' /\ (q, tp) ▷(≤t) (q', tp') /\ sizeOfTape (tp') <= z'.
  Proof.
    intros.
    assert (sizeOfTape tp <= z - t) as H3 by (unfold z; lia). 
    assert (z >= t) as H4 by (unfold z; lia). 
    specialize (multistep_inversion H H1 H3 H4) as (q' & tp' & t' & F1 & F2 & F3 & F4). 
    exists q', tp'. repeat split. 
    - apply F1. 
    - exists t'. apply (finalCondition F1) in H2. split; [apply F2 | ]. split; cbn; eauto. 
    - unfold z'. lia. 
  Qed. 


  (** initial strings *)
  Definition fullInput (c : list Sigma) := fixedInput ++ c.
  Definition initialString (c : list Sigma) := stringForConfig start (initTape_singleTapeTM (fullInput c)). 

  Definition isValidInitialString s := exists cert, isValidCert k' cert /\ s = initialString cert. 

  Lemma isValidCert_sizeOfTape cert: isValidCert k' cert -> sizeOfTape (initTape_singleTapeTM (fullInput cert)) <= k.
  Proof. 
    intros H. unfold fullInput. unfold isValidCert in H. 
    unfold z, k. 
    destruct fixedInput; [destruct cert | ]; cbn in *; [lia | lia | ]. 
    rewrite app_length. lia.
  Qed.

  Lemma initialString_reprConfig cert : isValidCert k' cert -> (start, initTape_singleTapeTM (fullInput cert)) ≃c initialString cert. 
  Proof. 
    intros. unfold initialString. apply stringForConfig_reprConfig.
    rewrite isValidCert_sizeOfTape by apply H. unfold z; lia.
  Qed. 

  (** final condition *)
  Definition haltingStates := filter (fun x => halt x) (elem states). 
  Definition finalSubstrings : list (list Gamma) := map (fun e => [inl e]) (prodLists haltingStates (elem (FinType (EqType (stateSigma))))). 

  Lemma finalSubstrings_correct s: (exists subs, subs el finalSubstrings /\ substring subs s) <-> containsHaltingState s. 
  Proof.
    split; intros.
    - destruct H as (subs & H1 & H2). unfold finalSubstrings in H1. 
      apply in_map_iff in H1 as (e & <- & H1). 
      destruct e as (q, m). apply in_prodLists_iff in H1 as (H1 & H3). 
      unfold containsHaltingState. 
      exists q, (inl (q, m)). 
      split.
      + unfold haltingStates in H1. apply in_filter_iff in H1 as (H1 & H4).
        auto. 
      + unfold substring in H2. destruct H2 as (? & ? & -> ). 
        split; [ | eauto]. eauto. 
   - destruct H as (q & qs & H1 & H2 & H3). 
     exists [qs]. split. 
     + unfold finalSubstrings. apply in_map_iff.
       destruct H2 as (m & ->).
       exists (q, m). split; [auto | ]. 
       apply in_prodLists_iff.
       unfold haltingStates. rewrite in_filter_iff. 
       repeat split.
       * apply elem_spec. 
       * auto. 
       * apply elem_spec. 
    + unfold substring. now apply In_explicit. 
  Qed.

  (** simulation lemma: for valid inputs, the CC instance does rewrite to a final string iff the Turing machine does accept *)
  Lemma simulation : forall cert,
      isValidCert k' cert 
      -> PTCCLang (Build_PTCC (initialString cert) simRules finalSubstrings  t) 
        <-> exists f, loopM (initc fTM ([|initTape_singleTapeTM (fullInput cert)|])) t = Some f.
  Proof. 
    intros. split; intros. 
    - destruct H0 as (wf & finalStr & H1 & H2). cbn [Psteps Pinit Pcards Pfinal ] in H1, H2.
      specialize (@soundness start (initTape_singleTapeTM (fullInput cert)) (initialString cert) finalStr) as H3. 
      edestruct H3 as (q' & tape' & F1 & ((l & F2 & F3 & F4) & F)). 
      + apply initialString_reprConfig, H. 
      + apply isValidCert_sizeOfTape, H.  
      + apply H1.
      + apply finalSubstrings_correct. apply H2. 
      + exists (mk_mconfig q' [|tape'|]). 
        clear H1 H2 H3. 
        apply loop_monotone with (k1 := l); [ | apply F2]. 
        clear F2. 
        unfold initc. 
        apply relpower_loop_agree; eauto. 
    - destruct H0 as ((q' & tape') & H0).  
      unfold TCCLang. 
      revert H0. 
      eapply VectorDef.caseS' with (v := tape').  
      clear tape'.  intros tape' t0.
      eapply VectorDef.case0 with (v := t0). 
      intros H0. clear t0. 
      cbn [cards steps init final].
      edestruct (@completeness start (initTape_singleTapeTM (fullInput cert)) q' tape' (initialString cert)) as (s' & F1 & F2 & F3). 
      + apply isValidCert_sizeOfTape, H.  
      + apply initialString_reprConfig, H. 
      + apply loop_relpower_agree, H0. 
      + split. 
        1: { unfold PTCC_wellformed. cbn. specialize (initialString_reprConfig H) as H1.  
            apply string_reprConfig_length in H1. unfold l in H1. lia. }
        exists s'.  split. 
        * apply F1.  
        * apply finalSubstrings_correct, F3. 
  Qed.  

  (** from this, we directly get a reduction to existential CC: does there exist an input string satisfying isValidInitialString for which the CC instance is a yes instance? *)
  Lemma TM_reduction_to_ExPTCC : @ExPTCC (FinType(EqType Gamma)) simRules finalSubstrings t isValidInitialString l <-> (exists cert, isValidCert k' cert /\ exists f, loopM (initc fTM ([|initTape_singleTapeTM (fullInput cert)|])) t = Some f). 
  Proof. 
    split; unfold ExPTCC.  
    - intros (x0 & H1 & (cert & H2 & H3) & H4). exists cert. split; [apply H2 | ]. subst; now apply simulation.
    - intros (s & H1 & H2%simulation). 2: apply H1. 
      exists (initialString s). split; [ | split; [unfold isValidInitialString; eauto | apply H2]]. 
      eapply string_reprConfig_length, initialString_reprConfig, H1. 
  Qed. 

  (** ** nondeterministic guessing of input *)
  (** We apply the procedure from PTCC_Preludes *)
  (** For that, a set of new rules is added which allow us to guess every allowed initial string using a single rewrite step *)

  Inductive preludeSig' := nblank | nstar | ndelimC | ninit | nsig σ. 
  Notation preludeSig := (sum Gamma preludeSig'). 

  Notation preludeRule := (preludeSig' -> preludeSig' -> preludeSig' -> preludeSig -> preludeSig -> preludeSig -> Prop). 

  Inductive preludeRules : preludeRule :=
  | bbbC : preludeRules nblank nblank nblank (inl $ inr $ inr (neutral, |_|)) (inl $ inr $ inr (neutral, |_|)) (inl $ inr $ inr (neutral, |_| ))
  | dbbC : preludeRules ndelimC nblank nblank (inl $ inr $ inl delimC) (inl $ inr $ inr (neutral, |_|)) (inl $ inr $ inr (neutral, |_|))
  | bbdC : preludeRules nblank nblank ndelimC (inl $ inr $ inr (neutral, |_|)) (inl $ inr $ inr (neutral, |_|)) (inl $ inr $ inl delimC)
  | bbiC : preludeRules nblank nblank ninit (inl $ inr $ inr (neutral, |_|)) (inl $ inr $ inr (neutral, |_|)) (inl $ inl (start, |_|))
  | bifC σ: preludeRules nblank ninit (nsig σ) (inl $ inr $ inr (neutral, |_|)) (inl $ inl (start, |_|)) (inl $ inr $ inr (∘ Some σ))
  | bisC m : preludeRules nblank ninit nstar (inl $ inr $ inr (neutral, |_|)) (inl $ inl (start, |_|)) (inl $ inr $ inr (neutral, m))
  | bibC : preludeRules nblank ninit nblank (inl $ inr $ inr (neutral, |_|)) (inl $ inl (start, |_|)) (inl $ inr $ inr (neutral, |_|))
  | ibbC : preludeRules ninit nblank nblank (inl $ inl (start, |_|)) (inl $ inr $ inr (neutral, |_|)) (inl $ inr $ inr (neutral, |_|))
  | ifsC σ1 m1: preludeRules ninit (nsig σ1) nstar (inl $ inl (start, |_|)) (inl $ inr $ inr (∘ Some σ1)) (inl $ inr $ inr (∘ m1))
  | ifbC σ1 : preludeRules ninit (nsig σ1) nblank (inl $ inl (start, |_|)) (inl $ inr $ inr (∘ Some σ1)) (inl $ inr $ inr (∘ |_|))
  | iffC σ1 σ2 : preludeRules ninit (nsig σ1) (nsig σ2) (inl $ inl (start, |_|)) (inl $ inr $ inr (∘ Some σ1)) (inl $ inr $ inr (∘ Some σ2))
  | isbC m : preludeRules ninit nstar nblank (inl $ inl (start, |_|)) (inl $ inr $ inr (neutral, m)) (inl $ inr $ inr (neutral, |_|))
  | issSC σ m : preludeRules ninit nstar nstar (inl $ inl (start, |_|)) (inl $ inr $ inr (neutral, Some σ)) (inl $ inr $ inr (neutral, m))
  | issBC : preludeRules ninit nstar nstar (inl $ inl (start, |_|)) (inl $ inr $ inr (neutral, |_|)) (inl $ inr $ inr (neutral, |_|))
  | fffC σ1 σ2 σ3 : preludeRules (nsig σ1) (nsig σ2) (nsig σ3) (inl $ inr $ inr (∘ Some σ1)) (inl $ inr $ inr (∘ Some σ2)) (inl $ inr $ inr (∘ Some σ3))
  | ffsC σ1 σ2 m1 : preludeRules (nsig σ1) (nsig σ2) nstar (inl $ inr $ inr (∘ Some σ1)) (inl $ inr $ inr (∘ Some σ2)) (inl $ inr $ inr (∘ m1))
  | fssSC σ1 σ2 m1 : preludeRules (nsig σ1) nstar nstar (inl $ inr $ inr (∘ Some σ1)) (inl $ inr $ inr (∘ Some σ2)) (inl $ inr $ inr (∘ m1))
  | fssBC σ1 : preludeRules (nsig σ1) nstar nstar (inl $ inr $ inr (∘ Some σ1)) (inl $ inr $ inr (∘ |_|)) (inl $ inr $ inr (∘ |_|)) 
  | fsbC σ1 m1 : preludeRules (nsig σ1) nstar nblank (inl $ inr $ inr (∘ Some σ1)) (inl $ inr $ inr (∘ m1)) (inl $ inr $ inr (∘ |_|))
  | ffbC σ1 σ2 : preludeRules (nsig σ1) (nsig σ2) nblank (inl $ inr $ inr (∘ Some σ1)) (inl $ inr $ inr (∘ Some σ2)) (inl $ inr $ inr (∘ |_|))
  | fbbC σ1 : preludeRules (nsig σ1) nblank nblank (inl $ inr $ inr (∘ Some σ1)) (inl $ inr $ inr (∘ |_|)) (inl $ inr $ inr (∘ |_|))
  | sssSSC σ1 σ2 m: preludeRules nstar nstar nstar (inl $ inr $ inr (neutral, Some σ1)) (inl $ inr $ inr (neutral, Some σ2)) (inl $ inr $ inr (neutral, m))
  | sssSBC σ : preludeRules nstar nstar nstar (inl $ inr $ inr (neutral, Some σ)) (inl $ inr $ inr (neutral, |_|)) (inl $ inr $ inr (neutral, |_|))
  | sssBC : preludeRules nstar nstar nstar (inl  $ inr $ inr (neutral, |_|)) (inl $ inr $ inr (neutral, |_|)) (inl $ inr $ inr (neutral, |_|))
  | ssbSC σ m : preludeRules nstar nstar nblank (inl $ inr $ inr (neutral, Some σ)) (inl $ inr $ inr (neutral, m)) (inl $ inr $ inr (neutral, |_|))
  | ssbBC : preludeRules nstar nstar nblank (inl $ inr $ inr (neutral, |_|))  (inl $ inr $ inr (neutral, |_|)) (inl $ inr $ inr (neutral, |_|))
  | sbbC m : preludeRules nstar nblank nblank (inl $ inr $ inr (neutral, m)) (inl $ inr $ inr (neutral, |_|)) (inl $ inr $ inr (neutral, |_|)). 

  Hint Constructors preludeRules : core.  

  Definition preludeInitialString : list preludeSig':=
    [ndelimC] ++ rev (repEl z' nblank) ++ [ninit] ++ map nsig fixedInput ++ repEl k' nstar ++ repEl (wo + t) nblank ++ [ndelimC]. 

  Lemma preludeInitialString_length : |preludeInitialString| = l. 
  Proof. unfold preludeInitialString. rewrite !app_length, rev_length, !repEl_length, map_length. unfold l, z', z, k, wo; cbn[length]. lia. Qed. 

  Lemma lifted_preludeInitialString : map (inr (A := Gamma)) preludeInitialString = 
    [inr ndelimC] ++ rev (repEl z' (inr nblank)) ++ [inr ninit] ++ map (fun σ => inr (nsig σ)) fixedInput ++ repEl k' (inr nstar) ++ repEl (wo + t) (inr nblank) ++ [inr ndelimC]. 
  Proof.  unfold preludeInitialString. rewrite !map_app, map_rev, !map_repEl, map_map. reflexivity. Qed. 

  (** we now use the method from PTCC_Preludes to derive that the prelude does in fact solve the problem of guessing an initial string *)

  (** different, more practical formulation of initial strings *)
  Definition stringForTapeHalf' n s := mapPolarity neutral s ++ E neutral n. 

  Lemma stringForTapeHalfP_eq s : stringForTapeHalf' (z' - |s|) s = stringForTapeHalf s. 
  Proof. unfold stringForTapeHalf', stringForTapeHalf; easy. Qed. 

  Lemma initialString_eq s : initialString s = rev (stringForTapeHalf []) ++ [inl (start, |_|)] ++ stringForTapeHalf (fullInput s). 
  Proof.  
    unfold initialString, fullInput. 
    destruct fixedInput; [destruct s | ]; cbn; eauto.  
  Qed. 

  Hint Constructors valid : core. 
  Hint Constructors coversHeadInd : core. 
  Hint Constructors liftPrelude : core. 
  Hint Constructors liftOrig : core. 

  (** a few helpful tactics *)

  (** resolve equations of the form l = map _ l', where l is not a variable *)
  Ltac inv_eqn_map := repeat match goal with 
    | [H : _ :: ?a = map _ ?s |- _] => is_var s; destruct s; cbn in H; [congruence | inv H]
    | [H : [] = map _ ?s |- _] => is_var s; destruct s; cbn in H; [ clear H| congruence]
    | [H : map _ _ = [] |- _] => symmetry in H
    | [H : map _ _ = _ :: _ |- _] => symmetry in H
  end.

  (** invert valid maximally - only use for constant cases, otherwise this will diverge *)
  Ltac prelude_inv_valid_constant := 
    repeat match goal with 
      | [H : (| _ :: _ :: _ |) < 2 |- _] => cbn in H; try lia
      | [H : _ = map _ _ |- _] => inv_eqn_map
      | [H : coversHeadInd _ _ _ |- _] => inv H
      | [H : liftPrelude _ _ _ _ _ _ _ |- _] => inv H
      | [H : preludeRules _ _ _ _ _ _ |- _ ] => inv H
      | [H : valid _ _ _ |- _] => inv H
    end.

  Notation lpreludeRules := (liftPrelude preludeRules).

  (** nblank symbols of the prelude do rewrite to blanks (right half of the string)*)
  Lemma prelude_blank_tape_covering_right n : 
    (repEl (S (S n)) (inr nblank) ++ [inr ndelimC]) ⇝{lpreludeRules} (map inl (E neutral (S (S n)))). 
  Proof.  induction n; cbn; eauto 10.  Qed. 

  (** in fact, nblanks do _only_ rewrite to blanks *)
  Lemma prelude_blank_tape_covering_right_unique n s: 
   (map inr (repEl (S (S n)) nblank ++ [ndelimC]))  ⇝{lpreludeRules} s 
    -> s = map inl (E neutral (S (S n))).
  Proof. 
    intros. revert s H. induction n as [ | n IH]; intros.
    - cbn in H. prelude_inv_valid_constant. now cbn. 
    - inv H. 
      + cbn in H4; lia.  
      + apply IH in H2 as ->. clear IH. prelude_inv_valid_constant. eauto. 
  Qed. 

  (** a string consisting of nstars followed by nblanks can be rewritten to the empty tape *)
  Lemma prelude_right_half_covering_blank n n' : 
    (repEl n (inr nstar) ++ repEl (S (S n')) (inr nblank) ++ [inr ndelimC]) ⇝{lpreludeRules} (map inl (E neutral (S (S (n + n'))))). 
  Proof. 
    induction n as [ | n IH]; cbn. 
    - apply prelude_blank_tape_covering_right. 
    - constructor 3.
      + apply IH. 
      + destruct n; [ | destruct n]; cbn; eauto 10. 
  Qed. 

  (** but it can also be rewritten to a string starting with symbols of the tape alphabet, followed by blanks *)
  (** we'll later instantiate this with |s| <= k and n = t + k - |s| *)
  Lemma prelude_right_half_covering_cert s n n' : 
    (repEl (|s|) (inr nstar) ++ repEl n (inr nstar) ++ repEl (S (S n')) (inr nblank) ++ [inr ndelimC]) 
      ⇝{lpreludeRules} (map inl (stringForTapeHalf' (S (S (n + n'))) s)). 
  Proof using t.
    induction s as [ | a s IH].  
    - cbn. 
      replace (inr nblank :: inr nblank :: repEl t (inr nblank) ++ [inr ndelimC]) with (repEl (S (S t)) (inr (A := Gamma) nblank) ++ [inr ndelimC]) by now cbn. 
      replace (inl (inr (inr (neutral, |_|))) :: inl (inr (inr (neutral, |_|))) :: map inl (E neutral (n + t))) with (map (inl (B := preludeSig')) (E neutral (S (S (n + t))))) by now cbn. 
      apply prelude_right_half_covering_blank. 
    - cbn. constructor 3. 
      + apply IH. 
      + destruct s; [ | destruct s; [ | cbn; solve[eauto 10] ]]; cbn. 
        * destruct n; cbn; [ | destruct n; cbn]; eauto 10. 
        * destruct n; cbn; eauto 10. 
  Qed. 

  (** a slightly different formulation of the same statement *)
  Lemma prelude_right_half_covering_cert' s n n': 
    (repEl (|s| + n) (inr nstar) ++ repEl (S (S n')) (inr nblank) ++ [inr ndelimC]) 
        ⇝{lpreludeRules} (map inl (stringForTapeHalf' (S (S (n + n'))) s)).
  Proof using t. 
    rewrite repEl_add. rewrite <- app_assoc. apply prelude_right_half_covering_cert. 
  Qed. 

  (** a string starting with nstars can *only* rewrite to a string starting with (possibly zero) symbols of the tape alphabet, followed by blanks *)
  Lemma prelude_right_half_covering_cert_unique j i s: 
    (map inr (repEl (S (S j)) nstar ++ repEl (S (S i)) nblank ++ [ndelimC])) ⇝{lpreludeRules} s 
    -> exists s', |s'| <= S(S j) /\ s = map inl (stringForTapeHalf' (S (S i) + (S (S j) - |s'|)) s'). 
  Proof. 
    revert s. induction j as [ | j IH]; cbn; intros. 
    - do 2(match goal with [H : valid _ _ _ |- _] => inv H end; try match goal with [H : _ < 2 |- _] => cbn in H; lia end). 
      apply prelude_blank_tape_covering_right_unique in H1 as ->. 
      prelude_inv_valid_constant. 
      + destruct m. 
        * exists [σ; e]. cbn; rewrite Nat.add_0_r. eauto. 
        * exists [σ]. cbn. rewrite Nat.add_comm; cbn. eauto. 
      + exists []. cbn. rewrite Nat.add_comm; cbn. eauto.
    - inv H; [cbn in H4; lia | ]. apply IH in H2 as (s' & H5 & ->). clear IH. 
      destruct s'; [ | destruct s']; cbn in *; prelude_inv_valid_constant. 
      + exists [σ]. cbn. split; [ lia |eauto ].  
      + exists []; cbn. rewrite !Nat.add_comm with (n := i). split; [lia | eauto]. 
      + exists [σ1; e]. cbn. rewrite !Nat.add_comm with (n := i).  split; [lia | eauto]. 
      + exists (σ1 :: e :: e0 :: s'). cbn. split; [lia | eauto]. 
  Qed. 

  Ltac inv_prelude := 
    repeat match goal with 
    | [H : coversHeadInd _ _ _ |- _] => inv H
    | [H : liftPrelude _ _ _ _ _ _ _ |- _] => inv H
    | [H : preludeRules _ _ _ _ _ _ |- _] => inv H
    end. 

  Lemma prelude_right_half_covering_cert_unique' j i s : 
    (map inr (repEl j nstar ++ repEl (S (S i)) nblank ++ [ndelimC])) ⇝{lpreludeRules} s 
    -> exists s', |s'| <= j /\ s = map inl (stringForTapeHalf' (S (S i) + j - (|s'|)) s'). 
  Proof. 
    intros H. 
    destruct j; [ | destruct j].
    - exists []. cbn in H. apply prelude_blank_tape_covering_right_unique in H. cbn; split; [lia | ]. 
      rewrite H. rewrite Nat.add_0_r; easy.
    - cbn in H. inv_valid. inv_prelude. apply prelude_blank_tape_covering_right_unique in H2.
      destruct m.
      + exists [e]. cbn; split; [ lia | ]. inv H2. rewrite Nat.add_comm. cbn. easy.
      + exists []. cbn; split; [ lia | ]. inv H2. rewrite Nat.add_comm. cbn. easy. 
    - apply prelude_right_half_covering_cert_unique in H as (s' & H1 & H2). 
      rewrite Nat.add_sub_assoc in H2 by lia. eauto.
  Qed. 

  (** now we add the fixed input at the start*)
  Lemma prelude_right_half_covering_input n finp s : 
   (map (fun σ => inr (nsig σ)) finp ++ repEl (|s| + n) (inr nstar) ++ repEl (wo+ t) (inr nblank) ++ [inr ndelimC]) 
    ⇝{lpreludeRules} (map inl (stringForTapeHalf' (wo+ n + t) (finp ++ s))). 
  Proof. 
    induction finp as [ | ? finp IH]. 
    - cbn [map app]. apply prelude_right_half_covering_cert'. 
    - cbn. constructor 3; [ apply IH | ]. 
      destruct finp; [ | destruct finp; [ | cbn; solve [eauto 10]]]. 
      + destruct s; [ | destruct s; [ | cbn; solve [eauto 10]]]. 
        * destruct n; [ | destruct n]; cbn; eauto 10. 
        * destruct n; cbn; eauto 10.
      + destruct s; [ | cbn; eauto 10]. destruct n; cbn; eauto 10.
  Qed. 

  (*and inversion *)
  Lemma prelude_right_half_covering_input_unique finp j i s : 
    (map inr (map nsig finp ++ repEl j nstar ++ repEl (wo + i) nblank ++ [ndelimC])) ⇝{lpreludeRules} s 
    -> exists s', |s'| <= j /\ s = map inl (stringForTapeHalf' (wo + i + j - (|s'|)) (finp ++ s')).
  Proof. 
    intros H. revert s H. induction finp as [ | ? finp IH]; intros.  
    - cbn in H. apply prelude_right_half_covering_cert_unique' in H. apply H. 
    - inv_valid.
      1: { destruct finp; [ destruct nstar | destruct finp]; (destruct j; [ | destruct j]); cbn in H4; try lia. }
      apply IH in H2 as (s' & H2 & ->). clear IH. 
      destruct finp; [ | destruct finp]; cbn in *. 
      + destruct j; [ | destruct j]; cbn in *. 
        * destruct s'; [ | cbn in H2; lia]. cbn in *. prelude_inv_valid_constant. 
          exists []. easy.
        * destruct s'; [ | destruct s']; cbn in *; prelude_inv_valid_constant. 
          -- exists []; easy.
          -- exists [e]; easy. 
        * destruct s' as [ | ? s']; [ | destruct s']; cbn in *; prelude_inv_valid_constant. 
          -- exists []; easy. 
          -- exists [e]; easy.
          -- exists (e :: e0 :: s') ; easy.
      + destruct j; [destruct s'; [ | cbn in H2; lia] | destruct s']; cbn in *; prelude_inv_valid_constant. 
        * exists []; easy. 
        * exists []; easy.
        * exists (e0 :: s'); easy.
      + prelude_inv_valid_constant. exists s'. easy.
  Qed. 

  Lemma prelude_right_half_covering_input_unique' s : 
    (map inr (map nsig fixedInput ++ repEl k' nstar ++ repEl (wo + t) nblank ++ [ndelimC])) ⇝{lpreludeRules} s 
    -> exists s', |s'| <= k' /\ s = map inl (stringForTapeHalf (fixedInput ++ s')).
  Proof. 
    intros H%prelude_right_half_covering_input_unique. 
    destruct H as (s' & H1 & H2). exists s'; split; [apply H1 | ]. 
    rewrite <- stringForTapeHalfP_eq. 
    rewrite H2. unfold z'. rewrite app_length. unfold z, k. 
    enough (wo + (t + ((|fixedInput|) + k')) - ((|fixedInput|) + (|s'|)) = wo + t + k' - (|s'|)) by easy.
    lia. 
  Qed.

  (** add the center state symbol *)
  Lemma prelude_center_covering_state finp s n : 
    ((inr ninit) :: map (fun σ => inr (nsig σ)) finp ++ repEl (|s| + n) (inr nstar) ++ repEl (wo+ t) (inr nblank) ++ [inr ndelimC]) 
      ⇝{lpreludeRules} (inl (inl (start, |_|)) :: map inl (stringForTapeHalf' (wo+ n + t) (finp ++ s))). 
  Proof. 
    econstructor 3. 
    - apply prelude_right_half_covering_input. 
    - destruct finp; cbn. 
      + destruct s; [ destruct n; [ | destruct n] | destruct s; [destruct n | ]]; cbn; eauto. 
      + destruct finp; [ cbn; destruct s; [ destruct n | ]; cbn; eauto | cbn;eauto ].
  Qed. 

  Lemma prelude_center_covering_state_unique finp j i s: 
    (map inr (ninit :: map nsig finp ++ repEl j nstar ++ repEl (wo + i) nblank ++ [ndelimC]))  ⇝{lpreludeRules} s 
    -> exists s', |s'| <= j /\ s = map inl (inl (start, |_|) :: stringForTapeHalf' (wo + i + j - (|s'|)) (finp ++ s')).
  Proof. 
    intros H. inv_valid. 
    1: { destruct finp; [destruct j; [ | destruct j] | destruct finp; [destruct j | ]]; cbn in H4; try lia. }
    apply prelude_right_half_covering_input_unique in H2 as (s' & F1 & F2). exists s'; split; [apply F1 | ]. 
    rewrite -> F2. inv_prelude; easy. 
  Qed.

  (** add the blanks of the left tape half *)
  Lemma prelude_left_covering_blank finp s n u: 
    (repEl u (inr nblank) ++ (inr ninit) :: map (fun σ => inr (nsig σ)) finp ++ repEl (|s| + n) (inr nstar) ++ repEl (wo+ t) (inr nblank) ++ [inr ndelimC]) 
    ⇝{lpreludeRules} (repEl u (inl (inr (inr (neutral, |_|)))) ++ inl (inl (start, |_|)) :: map inl (stringForTapeHalf' (wo+ n + t) (finp ++ s))). 
  Proof. 
    induction u as [ | u IH]; [cbn; apply prelude_center_covering_state | ]. 
    constructor 3. 
    - apply IH. 
    - destruct u; cbn; [ | destruct u; cbn; [eauto | eauto]].
      destruct finp; [destruct s; [destruct n | ] | ]; cbn; eauto.
  Qed.

  Lemma prelude_left_covering_blank_unique finp j i u s: 
    (map inr (repEl u nblank ++ ninit :: map nsig finp ++ repEl j nstar ++ repEl (wo + i) nblank ++ [ndelimC])) ⇝{lpreludeRules} s 
    -> exists s', |s'| <= j /\ s = map inl (repEl u (inr (inr (neutral, |_|))) ++ inl (start, |_|) :: stringForTapeHalf' (wo + i + j - (|s'|)) (finp ++ s')).
  Proof. 
    revert s. 
    induction u as [ | u IH]; cbn [repEl app]; intros s.
    - apply prelude_center_covering_state_unique. 
    - intros H. inv_valid. 
      1: { destruct u; cbn in H4; [ destruct finp; [destruct j | ]; cbn in H4; lia | destruct u; cbn in H4; lia]. }
      apply IH in H2. clear IH. destruct H2 as (s' & H2 & H3). exists s'; split; [apply H2 | ]. 
      rewrite H3. inv_prelude; easy.
  Qed.

  (** the left delimiter symbol *)
  Fact rev_E n p : rev (E p n) = inr (inl delimC) :: repEl n (inr (inr (p, |_|))). 
  Proof. 
    induction n as [ | n IH]; cbn; [easy | ]. 
    rewrite IH. cbn. replace (inr (inr (p, |_|)) :: repEl n (inr (inr (p, |_|)))) with (repEl (n + 1) (inr (inr (p, |_|)) : Gamma)). 
    2: { rewrite Nat.add_comm. cbn. easy. }
    rewrite repEl_add. cbn. easy.
  Qed.

  Lemma prelude_whole_string_covering finp s n u : 
    ((inr ndelimC) :: repEl (wo + u) (inr nblank) ++ (inr ninit) :: map (fun σ => inr (nsig σ)) finp ++ repEl (|s| + n) (inr nstar) ++ repEl (wo+ t) (inr nblank) ++ [inr ndelimC]) 
    ⇝{lpreludeRules} (rev (map inl (stringForTapeHalf' (wo + u) [])) ++ inl (inl (start, |_|)) :: map inl (stringForTapeHalf' (wo+ n + t) (finp ++ s))). 
  Proof. 
    unfold stringForTapeHalf'. cbn -[wo].  
    rewrite <- map_rev. rewrite rev_E. cbn [map].
    rewrite map_repEl. 
    constructor 3. 
    - apply prelude_left_covering_blank. 
    - cbn. eauto.
  Qed.

  Lemma prelude_whole_string_covering_unique finp j i u s: 
    (map inr (ndelimC :: repEl (wo + u) nblank ++ ninit :: map nsig finp ++ repEl j nstar ++ repEl (wo + i) nblank ++ [ndelimC])) ⇝{lpreludeRules} s 
    -> exists s', |s'| <= j /\ s = map inl (rev (stringForTapeHalf' (wo + u) []) ++ inl (start, |_|) :: stringForTapeHalf' (wo + i + j - (|s'|)) (finp ++ s')).
  Proof. 
    intros H.
    inv_valid. 
    apply (prelude_left_covering_blank_unique (u := S (S u))) in H2 as (s' & H2 & H3). 
    exists s'; split; [apply H2 | ]. rewrite H3. 
    inv_prelude. 
    unfold stringForTapeHalf'. cbn [mapPolarity map app]. rewrite rev_E. easy.
  Qed.

  (** we now put the above results together to obtain soundness and completeness. *)
  Fact rev_repEl (X : Type) (x : X) n : rev(repEl n x) = repEl n x. 
  Proof. 
    induction n as [ | n IH]; cbn; [easy | ]. 
    rewrite IH. clear IH. induction n as [ | n IH]; cbn; [easy | ]. now rewrite IH. 
  Qed.
  
  Lemma prelude_complete s : isValidInitialString s /\ |s| = l 
      -> (map inr preludeInitialString) ⇝{lpreludeRules} (map inl s). 
  Proof.
    intros [H1 H2]. unfold isValidInitialString in H1. 
    destruct H1 as (s' & H1 & ->). unfold isValidCert in H1. 
    rewrite initialString_eq. 
    unfold preludeInitialString.
    unfold initTape_singleTapeTM, fullInput.
    rewrite <- !stringForTapeHalfP_eq. cbn [length]; rewrite Nat.sub_0_r.
    unfold z'. 
    specialize (prelude_whole_string_covering fixedInput s' (k' - |s'|) z) as H3. 
    unfold z, k in *. rewrite app_length.
    replace (wo + (t + ((|fixedInput|) + k')) - ((|fixedInput|) + (|s'|))) with (wo + (k' - (|s'|)) + t)  by lia. 
    Unset Keyed Unification.
    rewrite !map_app. cbn -[stringForTapeHalf' repEl wo]. 
    rewrite !map_rev, !map_repEl. rewrite map_map. 
    replace ((|s'|) + (k' - (|s'|))) with k' in H3 by lia. 
    rewrite rev_repEl. apply H3. 
  Qed. 

  (** now the proof of soundness: the prelude can only generate valid initial strings *)
 
  Lemma prelude_sound s: 
    (map inr preludeInitialString) ⇝{lpreludeRules} s -> exists s', s = map inl s' /\ isValidInitialString s'. 
  Proof. 
    intros H. unfold preludeInitialString in H. cbn -[map rev repEl wo] in H. 
    rewrite rev_repEl in H. 
    apply (@prelude_whole_string_covering_unique fixedInput k' t z s) in H.
    destruct H as (s' & H1 & H2). 
    match type of H2 with s = map inl ?s1 => exists s1 end. split; [easy | ]. 
    unfold isValidInitialString. exists s'.
    split; [apply H1 | ]. rewrite initialString_eq. rewrite <- !stringForTapeHalfP_eq. 
    cbn [length]; rewrite Nat.sub_0_r. unfold z', z, k. 
    unfold fullInput. rewrite app_length. 
    enough (wo + (t + ((|fixedInput|) + k')) - ((|fixedInput|) + (|s'|)) = (wo + t + k' - (|s'|))).
    { rewrite H. easy. }
    lia. 
  Qed.

  Definition allRules := combP simRules preludeRules. 

  Global Instance preludeSigP_eqTypeC : eq_dec preludeSig'.
  Proof. unfold dec. decide equality. now destruct (eqType_dec σ σ0). Defined. 

  Global Instance preludeSigP_finTypeC : finTypeC (EqType preludeSig'). 
  Proof. 
    exists ([nblank; nstar; ndelimC; ninit] ++ (map nsig (elem Sigma))). 
    intros []; simpl; try match goal with [ |- S ?a = 1] => enough (a = 0) by easy end. 
    1-4: apply notInZero; intros (x & H1 & H2)%in_map_iff; congruence. 
    apply dupfreeCount.
    - apply dupfree_map; [intros; congruence | apply dupfree_elements]. 
    - apply in_map_iff. exists σ. split; easy. 
  Defined. 
  
  (** The reduction from ExPTCC to PTCC which is provided by the prelude*)
  Lemma prelude_reduction_from_ExPTCC : @ExPTCC (FinType (EqType Gamma)) simRules finalSubstrings t isValidInitialString l 
    <-> PTCCLang (@Build_PTCC (FinType (EqType preludeSig)) (map inr preludeInitialString) allRules (map (map inl) finalSubstrings) (1 + t)).  
  Proof. 
    eapply prelude_ok. 
    - unfold l. lia. 
    - intros. inv H. inv H2. apply prelude_sound in H1 as (s' & -> & H1). unfold isOrigString; eauto. 
    - intros. destruct k0; [ | lia]. clear H. inv H0. 
      unfold isPreludeString. eauto.
    - intros x0 (H1 & H2). econstructor; [ | constructor]. now apply prelude_complete.
    - intros. inv H. inv H2. now apply prelude_sound.  
    - apply preludeInitialString_length. 
  Qed. 

  (*reduction using the propositional rewrite rules: we put together the prelude and the deterministic simulation *)
  Lemma SingleTMGenNP_to_PTCC: 
    PTCCLang (@Build_PTCC (FinType (EqType preludeSig)) (map inr preludeInitialString) allRules (map (map inl) finalSubstrings) (1 + t))
    <-> SingleTMGenNP (existT _ Sigma (fTM, fixedInput, k', t)). 
  Proof. 
    rewrite <- prelude_reduction_from_ExPTCC. apply TM_reduction_to_ExPTCC.
  Qed. 

  (** ** list-based cards *)
  Notation Alphabet := ((Gamma + preludeSig')%type). 

  Hint Constructors preludeSig' : core. 

  Definition FGamma := finType_CS Gamma. 
  Definition FstateSigma := finType_CS stateSigma. 
  Definition Fpolarity := finType_CS polarity.

  (** *** list-based card infrastructure *)
  (** We use a abstract representation of elements of the alphabet Gamma with holes where the elements of the abstract TM alphabets Sigma and states need to be placed. 
  The follocardg development is centered around the goal of easily being able to instantiate the abstract fGamma elements with finTypes and with the flat representation using natural numbers. 
  *)
  Inductive fstateSigma := blank | someSigmaVar : nat -> fstateSigma | stateSigmaVar : nat -> fstateSigma. 
  Inductive fpolarity := polConst : polarity -> fpolarity | polVar : nat -> fpolarity.
  (*these are notations instead of definitions because extraction cannot deal with aliases *)
  Notation fpolSigma  := (prod fpolarity fstateSigma).
  Notation ftapeSigma := (sum delim fpolSigma).
  Notation fStates := (prod nat fstateSigma).
  Notation fGamma := (sum fStates ftapeSigma).
  Inductive fpreludeSig' := fnblank | fnstar | fndelimC | fninit | fnsigVar (n : nat). 
  Notation fAlphabet := (sum fGamma fpreludeSig'). 

  Inductive evalEnv X Y Z W := {
                              polarityEnv : list X;
                              sigmaEnv : list Y;
                              stateSigmaEnv : list Z;
                              stateEnv : list W
                      }.

  (** variables are bound to the elements at the corresponding index *)
  Definition boundVar (X : Type) (l : list X) (n : nat) := n < length l. 
  Section fixEnv. 
    Context {X Y Z W : Type}.
    Context (env : evalEnv X Y Z W). 

    Definition generateSigVar v := nth_error (sigmaEnv env) v.  
    Definition generatePolarityVar v := nth_error (polarityEnv env) v.
    Definition generateStateSigmaVar v := nth_error (stateSigmaEnv env) v.
    Definition generateStateVar v := nth_error (stateEnv env) v. 

    Definition bound_polarity (c : fpolarity) :=
      match c with
      | polConst _ => True
      | polVar v => boundVar (polarityEnv env) v
      end. 

    Definition bound_stateSigma (c : fstateSigma) :=
      match c with
      | blank => True
      | someSigmaVar v => boundVar (sigmaEnv env) v
      | stateSigmaVar v => boundVar (stateSigmaEnv env) v
      end.

    Definition bound_polSigma (c : fpolSigma) :=
      match c with (p, s) => bound_polarity p /\ bound_stateSigma s end. 

    Definition bound_tapeSigma (c : ftapeSigma) :=
      match c with
      | inl _ => True
      | inr s => bound_polSigma s
      end. 

    Definition bound_States (c : fStates) :=
      match c with (v, t) => boundVar (stateEnv env) v /\ bound_stateSigma t end. 

    Definition bound_Gamma (c : fGamma) :=
      match c with
      | inl s => bound_States s
      | inr s => bound_tapeSigma s
      end. 

    Definition bound_preludeSig' (c : fpreludeSig') := 
      match c with fnsigVar v => boundVar (sigmaEnv env) v | _ => True end. 

    Definition bound_Alphabet (c : fAlphabet) := 
      match c with 
        | inl s => bound_Gamma s
        | inr s => bound_preludeSig' s
      end. 
  End fixEnv. 

  Definition evalEnvFin := evalEnv Fpolarity Sigma FstateSigma states. 
  Definition evalEnvFlat := evalEnv nat nat nat nat.

  (** a generation procedure is canonical if it uses exactly the bound variables *)
  Definition generateCanonical {X Y Z W M : Type} (generate : evalEnv X Y Z W -> fAlphabet -> option M) := 
              forall (env : evalEnv X Y Z W) (c : fAlphabet), bound_Alphabet env c <-> exists e, generate env c = Some e. 


  (*generation to finite types *)
  Definition generatePolarityFin (env : evalEnvFin) (c : fpolarity) :=
    match c with
    | polConst c => Some c
    | polVar n => nth_error (polarityEnv env) n
    end. 
  Definition generateStateSigmaFin (env : evalEnvFin) (c : fstateSigma) :=
    match c with
    | blank => Some |_|
    | someSigmaVar v => option_map Some (nth_error (sigmaEnv env) v)
    | stateSigmaVar v => nth_error (stateSigmaEnv env) v
  end. 

  Definition generatePolSigmaFin (env : evalEnvFin) (c : fpolSigma) :=
    match c with
    | (p, s) => do p <- generatePolarityFin env p;
                do s <- generateStateSigmaFin env s;
                optReturn (p, s)
    end. 

  Definition generateTapeSigmaFin (env : evalEnvFin) (c : ftapeSigma) :=
    match c with
    | inl delimC => Some (inl delimC)
    | inr c => option_map inr (generatePolSigmaFin env c)
    end.

  Definition generateStatesFin (env : evalEnvFin) (c : fStates) :=
    match c with
    | (v, s) => do p <- nth_error (stateEnv env) v;
                do s <- generateStateSigmaFin env s;
                optReturn (p, s)
    end. 

  Definition generateGammaFin (env : evalEnvFin) (c : fGamma) :=
    match c with
    | inl s => option_map inl (generateStatesFin env s)
    | inr c => option_map inr (generateTapeSigmaFin env c)
    end. 

  Definition generatePreludeSigPFin (env : evalEnvFin) (c : fpreludeSig') := 
    match c with
    | fnsigVar v => do s <- nth_error (sigmaEnv env) v;
                    optReturn (nsig s)
    | fnstar => optReturn nstar
    | fnblank => optReturn nblank
    | fndelimC => optReturn ndelimC
    | fninit => optReturn ninit
  end. 

  Definition generateAlphabetFin (env : evalEnvFin) (c : fAlphabet) := 
    match c with 
    | inl s => option_map inl (generateGammaFin env s)
    | inr s => option_map inr (generatePreludeSigPFin env s)
    end. 

  Lemma generateAlphabetFin_canonical : generateCanonical generateAlphabetFin. 
  Proof. 
    unfold generateCanonical. intros; split; [intros | intros (e & H)] ;  
      repeat match goal with
              | [H : fAlphabet |- _] => destruct H; cbn in *
              | [H : fStates |- _ ] => destruct H; cbn in *
              | [H : fGamma |- _ ] => destruct H; cbn in *
              | [H : fpolarity |- _] => destruct H; cbn in *
              | [H : fpolSigma |- _] => destruct H; cbn in *
              | [H : fstateSigma |- _] => destruct H; cbn in *
              | [H : ftapeSigma |- _] => destruct H; cbn in *
              | [H : delim |- _ ] => destruct H; cbn in *
              | [H : fpreludeSig' |- _] => destruct H; cbn in *
              | [H : _ /\ _ |- _] => destruct H
              | [H : boundVar _ _ |- _ ] => apply nth_error_Some in H
              | [ |- context[nth_error ?a ?b ]] => destruct (nth_error a b) eqn:?; cbn in *
              | [ |- _ /\ _] => split 
              | _ => match type of H with context[nth_error ?a ?b ] => destruct (nth_error a b) eqn:?; cbn in * end 
              | [H : nth_error _ _ = Some _ |- _ ] => apply MoreBase.nth_error_Some_lt in H
      end; eauto; try congruence. 
  Qed. 

  (*generation to flat representation (natural numbers) *)
  Variable (flatTM : TMflat.flatTM). 
  Notation flatSigma := (TMflat.sig flatTM).
  Notation flatstates := (TMflat.states flatTM).
  Context (flatTM_TM_compat : TMflat.isFlatteningTMOf flatTM fTM). 

  Variable (flatFixedInput : list nat). 
  Context (flatFixedInput_compat : isFlatListOf flatFixedInput fixedInput).

  Definition flatPreludeSig' := 4 + flatSigma. 
  Definition flatPolarity := 3.
  Definition flatDelim := 1. 

  Definition flatDelimC := 0.

  Definition flatNblank := 0.
  Definition flatNstar := 1.
  Definition flatNdelimC := 2.
  Definition flatNinit := 3.
  Definition flatNsig n := 4 + n.

  Definition flattenPolarity (p : polarity) := index p. 
  (*this works because of the way we defined the list of values for the instance declaration*)
  Definition flattenPreludeSig' (p : preludeSig') := index p. 

  Definition flatStateSigma := (flatOption flatSigma).
  Definition flatPolSigma := (flatProd flatPolarity flatStateSigma).
  Definition flatTapeSigma := (flatSum flatDelim flatPolSigma).
  Definition flatStates := (flatProd flatstates flatStateSigma).
  Definition flatGamma := (flatSum flatStates flatTapeSigma). 
  Definition flatAlphabet := (flatSum flatGamma flatPreludeSig'). 

  Notation card := TCCCard.

  Definition generatePolarityFlat (env : evalEnvFlat) (c : fpolarity) :=
    match c with
    | polConst c => Some (flattenPolarity c)
    | polVar n => nth_error (polarityEnv env) n
    end. 
  Definition generateStateSigmaFlat (env : evalEnvFlat) (c : fstateSigma) :=
    match c with
    | blank => Some (flatNone)
    | someSigmaVar v => option_map flatSome (nth_error (sigmaEnv env) v)
    | stateSigmaVar v => nth_error (stateSigmaEnv env) v
  end. 

  Definition generatePolSigmaFlat (env : evalEnvFlat) (c : fpolSigma) :=
    match c with
    | (p, s) => do p <- generatePolarityFlat env p;
                do s <- generateStateSigmaFlat env s;
                optReturn (flatPair flatPolarity flatStateSigma p s)
    end. 

  Definition generateTapeSigmaFlat (env : evalEnvFlat) (c : ftapeSigma) :=
    match c with
    | inl delimC => Some (flatDelimC)
    | inr c => option_map (flatInr flatDelim) (generatePolSigmaFlat env c)
    end.

  Definition generateStatesFlat (env : evalEnvFlat) (c : fStates) :=
    match c with
    | (v, s) => do p <- nth_error (stateEnv env) v;
                do s <- generateStateSigmaFlat env s;
                optReturn (flatPair flatstates flatStateSigma p s)
    end. 

  Definition generateGammaFlat (env : evalEnvFlat) (c : fGamma) :=
    match c with
    | inl s => option_map (flatInl) (generateStatesFlat env s)
    | inr c => option_map (flatInr flatStates) (generateTapeSigmaFlat env c)
    end. 

  Definition generatePreludeSigPFlat (env : evalEnvFlat) (c : fpreludeSig') := 
    match c with
    | fnblank => optReturn flatNblank
    | fnstar => optReturn flatNstar
    | fninit => optReturn flatNinit
    | fndelimC => optReturn flatNdelimC
    | fnsigVar n => do s <- nth_error (sigmaEnv env) n;
                    optReturn (flatNsig s)
    end. 

  Definition generateAlphabetFlat (env : evalEnvFlat) (c : fAlphabet) := 
    match c with 
    | inl s => option_map (flatInl) (generateGammaFlat env s)
    | inr s => option_map (flatInr flatGamma) (generatePreludeSigPFlat env s) 
  end.  

  Ltac destruct_fAlphabet :=
    match goal with
      | [H : fAlphabet |- _] => destruct H
      | [H : preludeSig' |- _] => destruct H
      | [H : fStates |- _ ] => destruct H
      | [H : fGamma |- _ ] => destruct H
      | [H : fpolarity |- _] => destruct H
      | [H : fpolSigma |- _] => destruct H
      | [H : fstateSigma |- _] => destruct H
      | [H : ftapeSigma |- _] => destruct H
      | [H : delim |- _ ] => destruct H
      | [H : fpreludeSig' |- _] => destruct H
      end. 

  Lemma generateAlphabetFlat_canonical : generateCanonical generateAlphabetFlat.
  Proof.
    unfold generateCanonical.
    intros; split; [intros | intros (e & H)] ;
    repeat match goal with
      | _ => destruct_fAlphabet; cbn in *
      | [H : _ /\ _ |- _] => destruct H
      | [H : boundVar _ _ |- _ ] => apply nth_error_Some in H
      | [ |- context[nth_error ?a ?b ]] => destruct (nth_error a b) eqn:?; cbn in *
      | [ |- _ /\ _] => split 
      | _ => match type of H with context[nth_error ?a ?b ] => destruct (nth_error a b) eqn:?; cbn in * end 
      | [H : nth_error _ _ = Some _ |- _ ] => apply MoreBase.nth_error_Some_lt in H
      end; eauto; try congruence. 
  Qed.

  (** *** Proof that the outputs of both generation procedures are related via finReprEl *)

  Lemma flattenPolarity_reprEl p : finReprEl flatPolarity (flattenPolarity p) p. 
  Proof. 
    unfold finReprEl. split. 
    - unfold finRepr. unfold flatPolarity. unfold elem. now cbn.
    - destruct p; cbn; lia.
  Qed. 

  Lemma Sigma_finRepr : finRepr Sigma flatSigma. 
  Proof using flatTM_TM_compat. 
    destruct flatTM_TM_compat. rewrite eq__sig. unfold Cardinality. easy. 
  Qed. 

  Lemma states_finRepr : finRepr states flatstates. 
  Proof using flatTM_TM_compat. 
    destruct flatTM_TM_compat. rewrite eq__states. unfold Cardinality. easy. 
  Qed. 

  Lemma preludeSigP_finRepr : finRepr (FinType (EqType preludeSig')) flatPreludeSig'. 
  Proof using flatTM_TM_compat.
    unfold finRepr, flatPreludeSig', elem, enum. cbn. rewrite map_length. now rewrite Sigma_finRepr.
  Qed. 

  Lemma flattenPreludeSigP_reprEl x : finReprEl flatPreludeSig' (flattenPreludeSig' x) x. 
  Proof using flatTM_TM_compat.
    unfold finReprEl. split.
    - apply preludeSigP_finRepr.
    - destruct x; cbn; lia. 
  Qed. 

  Smpl Add (apply Sigma_finRepr) : finRepr.
  Smpl Add (apply states_finRepr) : finRepr.
  Smpl Add (apply flattenPolarity_reprEl) : finRepr. 
  Smpl Add (apply preludeSigP_finRepr) : finRepr.
  Smpl Add (apply flattenPreludeSigP_reprEl) : finRepr. 


  Lemma nsig_reprEl n σ: finReprEl flatSigma n σ -> finReprEl flatPreludeSig' (flatNsig n) (nsig σ).
  Proof using flatTM_TM_compat. 
    intros H. split; [finRepr_simpl | ]. 
    destruct H as (_ & H). cbn. 
    rewrite getPosition_map. 2: {unfold injective; intros; congruence. }
    unfold index in H. now rewrite H. 
  Qed. 
  Smpl Add (apply nsig_reprEl) : finRepr. 

  Lemma polarity_finRepr : finRepr Fpolarity flatPolarity. 
  Proof. 
    unfold finRepr. cbn. easy.
  Qed. 

  Smpl Add (apply polarity_finRepr) : finRepr.

  Lemma stateSigma_finRepr : finRepr FstateSigma flatStateSigma. 
  Proof using flatTM_TM_compat. 
    finRepr_simpl. 
  Qed. 

  Smpl Add (apply stateSigma_finRepr) : finRepr.

  Lemma delimC_reprEl : finReprEl flatDelim flatDelimC delimC.  
  Proof. 
    split. 
    - unfold finRepr. auto. 
    - auto. 
  Qed. 

  Smpl Add (apply delimC_reprEl) : finRepr. 

  Definition isFlatEnvOf (a : evalEnvFlat) (b : evalEnvFin) :=
    isFlatListOf (polarityEnv a) (polarityEnv b)
    /\ isFlatListOf (sigmaEnv a) (sigmaEnv b)
    /\ isFlatListOf (stateSigmaEnv a) (stateSigmaEnv b)
    /\ isFlatListOf (stateEnv a) (stateEnv b).

  (*only the number of elements in an environment is relevant for boundedness *)
  Lemma isFlatEnvOf_bound_Alphabet_transfer (envFlat : evalEnvFlat) (envFin : evalEnvFin) (c : fAlphabet) :
    isFlatEnvOf envFlat envFin -> bound_Alphabet envFin c <-> bound_Alphabet envFlat c. 
  Proof. 
    intros (H1 & H2 & H3 & H4). 
    destruct c as [f | f]; cbn in *. 
    - destruct f as [f | f]; cbn in *. 
      + destruct f; cbn. destruct f; cbn.
        * rewrite H4. unfold boundVar. rewrite map_length. tauto.
        * rewrite H4, H2; unfold boundVar. rewrite !map_length. tauto.
        * rewrite H4, H3; unfold boundVar. rewrite !map_length; tauto.
      + destruct f as [f | f]; cbn; [tauto | ]. 
        destruct f as [f f0]; cbn. destruct f, f0; cbn. 
        all: try rewrite H1; try rewrite H2; try rewrite H3; try rewrite H4.
        all: unfold boundVar; try rewrite !map_length; tauto.  
    - destruct f; cbn in *; try easy. unfold boundVar. now rewrite H2, map_length.  
  Qed. 

  Lemma generateAlphabet_reprEl a b d :
    isFlatEnvOf a b -> bound_Alphabet a d
    -> exists e1 e2, generateAlphabetFin b d = Some e1 /\ generateAlphabetFlat a d = Some e2 /\ finReprEl flatAlphabet e2 e1. 
  Proof using flatTM_TM_compat.
    intros.
    specialize (proj1 (generateAlphabetFlat_canonical _ _ ) H0 ) as (e1 & H1). 
    eapply (isFlatEnvOf_bound_Alphabet_transfer ) in H0. 2: apply H. 
    specialize (proj1 (generateAlphabetFin_canonical _ _ ) H0) as (e2 & H2). 
    exists e2, e1. split; [apply H2 | split; [ apply H1 | ]]. 
    destruct H as (F1 & F2 & F3 & F4).
    repeat match goal with
      | _ => destruct_fAlphabet; cbn -[Nat.mul Nat.add flatSum flatGamma flatAlphabet index] in *
      | _ => match type of H1 with context[nth_error ?a ?b ] =>
            let Heqn := fresh "H" "eqn" in 
            let Heqn2 := fresh "H" "eqn" in 
            destruct (nth_error a b) eqn:Heqn; cbn -[Nat.mul Nat.add flatSum flatGamma flatAlphabet index] in *;
              try (eapply isFlatListOf_Some1 in Heqn as (? & Heqn2 & ?);
                    [ | | eauto ];
                    [ setoid_rewrite Heqn2 in H2; cbn -[Nat.mul Nat.add flatSum flatGamma flatAlphabet index] in *
                    | finRepr_simpl]
                  )
            end
      | [H : Some _ = Some _ |- _] => apply Some_injective in H; subst (*we do not use inversion as inversion does reduce finType wrappers, which breaks finRepr_simpl *)
    end; try congruence. 
    all: try finRepr_simpl; eauto. (* TODO: maybe smpl database is missing patterns to only try lemmas if they match syntactically? *)
  Qed. 

  (** *** Generation of covering cards *)

  Definition generateCard (X Y Z W M: Type) (r : evalEnv X Y Z W -> fAlphabet -> option M) (env : evalEnv X Y Z W) rule :=
    match rule with {a, b, c} / {d, e, f} =>
                      do a <- r env a;
                      do b <- r env b;
                      do c <- r env c;
                      do d <- r env d;
                      do e <- r env e;
                      do f <- r env f;
                      optReturn ({a, b, c} / {d, e, f})
    end.

  Definition bound_CardP {X Y Z W : Type} (env : evalEnv X Y Z W) (c : TCCCardP fAlphabet) :=
    bound_Alphabet env (cardEl1 c) /\ bound_Alphabet env (cardEl2 c) /\ bound_Alphabet env (cardEl3 c). 
  Definition bound_card {X Y Z W : Type} (env : evalEnv X Y Z W) (c : card fAlphabet) :=
    bound_CardP env (prem c) /\ bound_CardP env (conc c).

  Lemma isFlatEnvOf_bound_card_transfer (envFlat : evalEnvFlat) (envFin : evalEnvFin) (c : card fAlphabet) :
    isFlatEnvOf envFlat envFin -> (bound_card envFlat c <-> bound_card envFin c). 
  Proof. 
    intros H. destruct c, prem, conc; cbn. unfold bound_card, bound_CardP; cbn.  
    split; intros ((F1 & F2 & F3) & (F4 & F5 & F6)); repeat split.
    all: now apply (isFlatEnvOf_bound_Alphabet_transfer _ H). 
  Qed.


  (** for canonical generation procedures, generateCard works as intended *)
  Lemma generateCard_Some (X Y Z W M : Type) (r : evalEnv X Y Z W -> fAlphabet -> option M) (env : evalEnv X Y Z W) rule :
    generateCanonical r
    -> (bound_card env rule <-> exists w, generateCard r env rule = Some w). 
  Proof.
    intros. split.
    + intros ((H1 & H2 & H3) & (H4 & H5 & H6)).
      unfold generateCard. 
      destruct rule, prem, conc; cbn in *. 
      apply H in H1 as (? & ->).
      apply H in H2 as (? & ->).
      apply H in H3 as (? & ->).
      apply H in H4 as (? & ->).
      apply H in H5 as (? & ->).
      apply H in H6 as (? & ->).
      cbn. eauto.
    + intros (w & H1). 
      unfold bound_card, bound_CardP.
      destruct rule, prem, conc. cbn in *.
      repeat match type of H1 with
              | context[r ?h0 ?h1] => let H := fresh "H" in destruct (r h0 h1) eqn:H
      end; cbn in *; try congruence. 
      repeat split; apply H; eauto. 
  Qed. 


  (** the output of generateCard is related via isFlatCardOf for the two generation procedures *)
  Lemma generateCard_isFlatCardOf envFlat envFin rule :
    bound_card envFlat rule -> isFlatEnvOf envFlat envFin -> exists e1 e2, generateCard generateAlphabetFlat envFlat rule = Some e1 /\ generateCard generateAlphabetFin envFin rule = Some e2 /\ isFlatTCCCardOf e1 e2. 
  Proof using flatTM_TM_compat.
    intros.
    specialize (proj1 (isFlatEnvOf_bound_card_transfer _ H0) H) as H'.
    destruct (proj1 (generateCard_Some _ _ generateAlphabetFin_canonical) H') as (card & H1).  
    clear H'. 
    destruct (proj1 (generateCard_Some _ _ generateAlphabetFlat_canonical) H) as (card' & H2).
    exists card', card. split; [apply H2 | split; [apply H1 | ]]. 
    destruct rule, prem, conc.
    cbn in H1, H2. 
    destruct H as ((F1 & F2 & F3) & (F4 & F5 & F6)); cbn in *. 
    repeat match goal with
    | [H : bound_Alphabet _ _ |- _] =>
      let H1 := fresh "H" in let H2 := fresh "H" in
        destruct (generateAlphabet_reprEl H0 H) as (? & ? & H1 & H2 & ?);
        rewrite H1 in *; rewrite H2 in *;
        clear H1 H2 H
    end. 
    cbn in *. inv H1. inv H2. 
    split; constructor; cbn; eapply finReprEl_finReprEl'; eauto.
  Qed. 

  (** list_prod: cons every element of the first list to every element of the second list*)
  Definition list_prod (X : Type) := fix rec (l : list X) (l' : list (list X)) : list (list X) :=
    match l with [] => []
            | (h :: l) => map (@cons X h) l' ++ rec l l'
    end. 

  Lemma in_list_prod_iff (X : Type) (l : list X) (l' : list (list X)) l0:
    l0 el list_prod l l' <-> exists h l1, l0 = h :: l1 /\ h el l /\ l1 el l'. 
  Proof. 
    induction l; cbn. 
    - split; [auto | intros (? & ? & _ & [] & _)].
    - rewrite in_app_iff. split; intros. 
      + destruct H as [H | H].
        * apply in_map_iff in H as (? & <- & H2). eauto 10.
        * apply IHl in H as (? & ? & -> & H1 & H2). eauto 10.
      + destruct H as (? & ? & -> & [-> | H] & H2).
        * left. apply in_map_iff. eauto 10.
        * right. apply IHl; eauto 10.
  Qed. 

  (** an environment containing all combinations of n elements is created by iterating list_prod*)
  Definition mkVarEnv (X : Type) (l : list X) (n : nat) :=
    it (fun acc => list_prod l acc ++ acc) n [[]].

  Lemma in_mkVarEnv_iff (X : Type) (l : list X) (n : nat) (l' : list X) :
    l' el mkVarEnv l n <-> |l'| <= n /\ l' <<= l. 
  Proof.
    revert l'. 
    induction n as [ | n IH]; intros l'; cbn. 
    - split.
      + intros [<- | []]. eauto.
      + intros (H1 & H2); destruct l'; [eauto | cbn in H1; lia]. 
    - rewrite in_app_iff. rewrite in_list_prod_iff. split.
      + intros [(? & ? & -> & H1 & H2) | H1].
        * unfold mkVarEnv in IH. apply IH in H2 as (H2 & H3).
          split; [now cbn | cbn; intros a [-> | H4]; eauto ].  
        * apply IH in H1 as (H1 & H2). split; eauto. 
      + intros (H1 & H2).
        destruct (nat_eq_dec (|l'|) (S n)). 
        * destruct l'; cbn in *; [congruence | ].
          apply incl_lcons in H2 as (H2 & H3).
          assert (|l'| <= n) as H1' by lia. clear H1. 
          specialize (proj2 (IH l') (conj H1' H3)) as H4.
          left. exists x, l'. eauto. 
        * right. apply IH. split; [lia | eauto]. 
  Qed. 

  Definition tupToEvalEnv (X Y Z W : Type) (t : (list X) * (list Y) * (list Z) * (list W)) :=
    match t with
    | (t1, t2, t3, t4) => Build_evalEnv t1 t2 t3 t4
    end.

  (** this is now lifted to evalEnv *)
  Definition makeAllEvalEnv (X Y Z W : Type) (l1 : list X) (l2 : list Y) (l3 : list Z) (l4 : list W) (n1 n2 n3 n4 : nat) :=
    let allenv := prodLists (prodLists (prodLists (mkVarEnv l1 n1) (mkVarEnv l2 n2)) (mkVarEnv l3 n3)) (mkVarEnv l4 n4) in
    map (@tupToEvalEnv X Y Z W) allenv. 

  Lemma in_makeAllEvalEnv_iff (X Y Z W : Type) (l1 : list X) (l2 : list Y) (l3 : list Z) (l4 : list W) n1 n2 n3 n4 :
    forall a b (c : list Z) d, Build_evalEnv a b c d el makeAllEvalEnv l1 l2 l3 l4 n1 n2 n3 n4 <->
      (|a| <= n1 /\ a <<= l1)
      /\ (|b| <= n2 /\ b <<= l2)
      /\ (|c| <= n3 /\ c <<= l3)
      /\ (|d| <= n4 /\ d <<= l4). 
  Proof. 
    intros. unfold makeAllEvalEnv. rewrite in_map_iff.
    split.
    - intros ([[[]]] & H1 & H2). 
      cbn in H1. inv H1.  
      repeat match type of H2 with
              | _ el prodLists _ _ => apply in_prodLists_iff in H2 as (H2 & ?%in_mkVarEnv_iff)
              end. 
      apply in_mkVarEnv_iff in H2. eauto 10.
    - intros (H1 & H2 & H3 & H4). 
      exists (a, b, c, d). split; [now cbn | ]. 
      repeat match goal with
            | [ |- _ el prodLists _ _ ]=> apply in_prodLists_iff; split
            end. 
      all: apply in_mkVarEnv_iff; eauto. 
  Qed. 

  Definition list_isFlatEnvOf (envFlatList : list evalEnvFlat) (envFinList : list evalEnvFin) :=
    (forall envFlat, envFlat el envFlatList -> exists envFin, isFlatEnvOf envFlat envFin /\ envFin el envFinList)
    /\ (forall envFin, envFin el envFinList -> exists envFlat, isFlatEnvOf envFlat envFin /\ envFlat el envFlatList).

  Lemma makeAllEvalEnv_isFlatEnvOf (Afin : list polarity) (Bfin : list Sigma) (Cfin : list stateSigma) (Dfin : list states) (Aflat Bflat Cflat Dflat : list nat) n1 n2 n3 n4:
    isFlatListOf Aflat Afin 
    -> isFlatListOf Bflat Bfin
    -> isFlatListOf Cflat Cfin
    -> isFlatListOf Dflat Dfin
    -> list_isFlatEnvOf (makeAllEvalEnv Aflat Bflat Cflat Dflat n1 n2 n3 n4) (makeAllEvalEnv Afin Bfin Cfin Dfin n1 n2 n3 n4).
  Proof. 
    intros. split; intros []; intros. 
    - apply in_makeAllEvalEnv_iff in H3 as ((G1 & F1) & (G2 & F2) & (G3 & F3) & (G4 & F4)).
      apply (isFlatListOf_incl1 H) in F1 as (polarityEnv0' & M1 & N1).    
      apply (isFlatListOf_incl1 H0) in F2 as (sigmaEnv0' & M2 & N2). 
      apply (isFlatListOf_incl1 H1) in F3 as (stateSigmaEnv0' & M3 & N3). 
      apply (isFlatListOf_incl1 H2) in F4 as (stateEnv0' & M4 & N4). 
      exists (Build_evalEnv polarityEnv0' sigmaEnv0' stateSigmaEnv0' stateEnv0').
      split; [unfold isFlatEnvOf; cbn; eauto | ]. 
      apply in_makeAllEvalEnv_iff.
      rewrite M1, map_length in G1.
      rewrite M2, map_length in G2.
      rewrite M3, map_length in G3.
      rewrite M4, map_length in G4.
      eauto 10.
  - apply in_makeAllEvalEnv_iff in H3 as ((G1 & F1) & (G2 & F2) & (G3 & F3) & (G4 & F4)).
    apply (isFlatListOf_incl2 H) in F1 as (polarityEnv0' & M1 & N1).    
    apply (isFlatListOf_incl2 H0) in F2 as (sigmaEnv0' & M2 & N2). 
    apply (isFlatListOf_incl2 H1) in F3 as (stateSigmaEnv0' & M3 & N3). 
    apply (isFlatListOf_incl2 H2) in F4 as (stateEnv0' & M4 & N4). 
    exists (Build_evalEnv polarityEnv0' sigmaEnv0' stateSigmaEnv0' stateEnv0').
    split; [unfold isFlatEnvOf; cbn; eauto | ]. 
    apply in_makeAllEvalEnv_iff.
    rewrite M1, M2, M3, M4 at 1. rewrite !map_length.
    eauto 10.
  Qed. 

  Definition makeAllEvalEnvFin := makeAllEvalEnv (elem Fpolarity) (elem Sigma) (elem FstateSigma) (elem states).
  Definition makeAllEvalEnvFlat := makeAllEvalEnv (seq 0 flatPolarity) (seq 0 flatSigma) (seq 0 flatStateSigma) (seq 0 flatstates).

  Lemma makeAllEvalEnv_isFlatEnvOf' n1 n2 n3 n4 : list_isFlatEnvOf (makeAllEvalEnvFlat n1 n2 n3 n4) (makeAllEvalEnvFin n1 n2 n3 n4). 
  Proof using flatTM_TM_compat. 
    apply makeAllEvalEnv_isFlatEnvOf. 
    - apply seq_isFlatListOf.
    - rewrite Sigma_finRepr. apply seq_isFlatListOf.
    - assert (flatStateSigma = |elem FstateSigma|) as ->. 
      { cbn. rewrite map_length. rewrite <- Sigma_finRepr. now cbn. }
      apply seq_isFlatListOf. 
    - rewrite states_finRepr. apply seq_isFlatListOf.
  Qed. 

  (** instantiate all rules - the resulting list is ordered by rules *)

  Definition makeCards' (X Y Z W M : Type) (generate : evalEnv X Y Z W -> fAlphabet -> option M)  (l : list (evalEnv X Y Z W)) rule :=
    filterSome (map (fun env => generateCard generate env rule) l).

  Definition makeCards (X Y Z W M : Type) (generate : evalEnv X Y Z W -> fAlphabet -> option M) (allEnv : list (evalEnv X Y Z W)) (rules : list (card fAlphabet)) :=
    concat (map (makeCards' generate allEnv) rules).

  Lemma in_makeCardsP_iff (X Y Z W M : Type) (generate : evalEnv X Y Z W -> fAlphabet -> option M) (l : list (evalEnv X Y Z W)) rule card :
    card el makeCards' generate l rule <-> exists env, env el l /\ Some card = generateCard generate env rule. 
  Proof.
    unfold makeCards'. rewrite in_filterSome_iff. rewrite in_map_iff. split.
    - intros (? & H1 & H2). exists x. now rewrite H1. 
    - intros (env & H1 & ->). now exists env. 
  Qed. 

  Lemma in_makeCards_iff (X Y Z W M : Type) (generate : evalEnv X Y Z W -> fAlphabet -> option M) allEnv rules card :
    card el makeCards generate allEnv rules <-> exists env rule, rule el rules /\ env el allEnv /\ Some card = generateCard generate env rule. 
  Proof.
    unfold makeCards. rewrite in_concat_iff. split.
    - intros (l' & H1 & (rule & <- & H2)%in_map_iff). 
      apply in_makeCardsP_iff in H1 as (env & H3 & H4).
      exists env, rule. eauto.
    - intros (env & rule & H1 & H2 & H3).
      setoid_rewrite in_map_iff.
      exists (makeCards' generate allEnv rule). 
      split.
      + apply in_makeCardsP_iff. eauto.
      + eauto.  
  Qed. 

  Definition makeCardsFin := makeCards generateAlphabetFin.  
  Definition makeCardsFlat := makeCards generateAlphabetFlat.

  Definition list_finReprEl (X : finType) (x : nat) (A : list nat) (B : list X)  :=
    (forall n, n el A -> exists a, finReprEl x n a /\ a el B) /\ (forall b, b el B -> exists n, finReprEl x n b /\ n el A). 

  Lemma isFlatListOf_list_finReprEl (X : finType) (x : nat) (A : list nat) (B : list X) :
    finRepr X x
    -> isFlatListOf A B
    -> list_finReprEl x A B. 
  Proof.
    intros. rewrite H0; clear H0. unfold list_finReprEl. split.
    - intros. apply in_map_iff in H0 as (x' & <- & H0).
      exists x'. split; [ repeat split | apply H0]. apply H.
    - intros. exists (index b). split; [ | apply in_map_iff; eauto]. 
      split; [ apply H| reflexivity]. 
  Qed.  

  Lemma makeCardsP_isFlatTCardsOf  (envFlatList : list evalEnvFlat) (envFinList : list evalEnvFin) rule :
    list_isFlatEnvOf envFlatList envFinList ->
    isFlatTCardsOf (makeCards' generateAlphabetFlat envFlatList rule) (makeCards' generateAlphabetFin envFinList rule).
  Proof using flatTM_TM_compat. 
    intros. split; intros. 
    - apply in_makeCardsP_iff in H0 as (env & H1 & H2).
      symmetry in H2.
      apply H in H1 as (env' & H3 & H4). 
      assert (exists w, generateCard generateAlphabetFlat env rule = Some w) by eauto.
      eapply (generateCard_Some env rule generateAlphabetFlat_canonical) in H0. 
      eapply isFlatEnvOf_bound_card_transfer  in H0 as H0'. 
      2: apply H3. 
      specialize (proj1 (generateCard_Some env' rule generateAlphabetFin_canonical) H0') as (w' & H1). 
      exists w'. split.
      + apply in_makeCardsP_iff. exists env'. eauto.
      + destruct (generateCard_isFlatCardOf H0 H3) as (? & ? & F1 & F2 & F3).  
        rewrite F1 in H2. rewrite F2 in H1. inv H2. inv H1. apply F3. 
  - apply in_makeCardsP_iff in H0 as (env & H1 & H2). 
    symmetry in H2.
      apply H in H1 as (env' & H3 & H4). 
      assert (exists w, generateCard generateAlphabetFin env rule = Some w) by eauto.
      eapply (generateCard_Some env rule generateAlphabetFin_canonical) in H0. 
      eapply isFlatEnvOf_bound_card_transfer  in H0 as H0'. 
      2: apply H3. 
      specialize (proj1 (generateCard_Some env' rule generateAlphabetFlat_canonical) H0') as (w & H1). 
      exists w. split.
      + apply in_makeCardsP_iff. exists env'. eauto.
      + destruct (generateCard_isFlatCardOf H0' H3) as (? & ? & F1 & F2 & F3).  
        rewrite F1 in H1. rewrite F2 in H2. inv H2. inv H1. apply F3. 
  Qed. 

  Lemma makeCards_isFlatCardOf finenv flatenv rules :
    list_isFlatEnvOf flatenv finenv
    -> isFlatTCardsOf (makeCardsFlat flatenv rules) (makeCardsFin finenv rules).
  Proof using flatTM_TM_compat. 
    intros H0. split. 
    - intros card H. unfold makeCardsFlat, makeCardsFin, makeCards in H. 
      apply in_concat_iff in H as (cards & H & H1). 
      apply in_map_iff in H1 as (rule & <- & H2). 
      apply (makeCardsP_isFlatTCardsOf rule) in H0.
      apply H0 in H as (w' & F1 & F2). exists w'.  
      split; [  | apply F2 ]. 
      unfold makeCardsFin, makeCards. apply in_concat_iff. 
      eauto 10.
    - intros. unfold makeCardsFin, makeCards in H. 
      apply in_concat_iff in H as (cards & H & H1). 
      apply in_map_iff in H1 as (rule & <- & H2). 
      apply (makeCardsP_isFlatTCardsOf rule) in H0.
      apply H0 in H as (w & F1 & F2). exists w.  
      split; [ |apply F2 ]. 
      unfold makeCardsFin, makeCardsFlat, makeCards. apply in_concat_iff. 
      eauto 10. 
  Qed. 
 
  Lemma finType_enum_list_finReprEl (T : finType) : list_finReprEl (length (elem T)) (seq 0 (length (elem T))) (elem T). 
  Proof. 
    unfold list_finReprEl. split.
    - intros. apply in_seq in H. destruct (nth_error (elem T) n ) eqn:H1.  
      + exists e. split; [ | now apply nth_error_In in H1 ].
        split.
        * easy. 
        * unshelve eapply nth_error_nth in H1; [ apply e | rewrite <- H1]. apply getPosition_nth. 2: easy.
          apply dupfree_elements.   
      + destruct H. cbn in H0. apply nth_error_Some in H0. congruence. 
    - intros. exists (getPosition (elem T) b). apply In_nth with (d := b) in H as (n & H1 & <-). split.
      + split. 
        * easy. 
        * reflexivity.
      + rewrite getPosition_nth; [ | | assumption].
        * apply in_seq.  lia. 
        * apply dupfree_elements. 
  Qed. 

  Notation "f $ x" := (f x) (at level 60, right associativity, only parsing).

  (** *** Definition of list-based rules *)
  Definition mtrRules : list (card fAlphabet):=
    [
      {inl $ inr $ inr (polVar 0, someSigmaVar 0), inl $ inr (inr (polVar 0, someSigmaVar 1)), inl $ inr (inr (polVar 0, someSigmaVar 2))} / {inl $ inr (inr (polConst positive, someSigmaVar 3)), inl $ inr (inr (polConst positive, someSigmaVar 0)), inl $ inr (inr (polConst positive, someSigmaVar 1))};
      {inl $ inr (inr (polVar 0, blank)), inl $ inr (inr (polVar 0, blank)), inl $ inr (inr (polVar 0, blank))} / {inl $ inr (inr (polConst positive, someSigmaVar 0)), inl $ inr (inr (polConst positive, blank)), inl $ inr (inr (polConst positive, blank))};
      { inl $ inr (inr (polVar 0, someSigmaVar 0)), inl $ inr (inr (polVar 0, blank)), inl $ inr (inr (polVar 0, blank))} / {inl $ inr (inr (polConst positive, someSigmaVar 1)), inl $ inr (inr (polConst positive, someSigmaVar 0)), inl $ inr (inr (polConst positive, blank))};
      { inl $ inr (inr (polVar 0, blank)), inl $ inr (inr (polVar 0, blank)), inl $ inr (inr (polVar 0, blank))} / {inl $ inr (inr (polConst positive, blank)), inl $ inr (inr (polConst positive, blank)), inl $ inr (inr (polConst positive, blank))};
      { inl $ inr (inr (polVar 0, someSigmaVar 0)), inl $ inr (inr (polVar 0, someSigmaVar 1)), inl $ inr (inr (polVar 0, blank)) } / {inl $ inr (inr (polConst positive, someSigmaVar 2)), inl $ inr (inr (polConst positive, someSigmaVar 0)), inl $ inr (inr (polConst positive, someSigmaVar 1))};
      { inl $ inr (inr (polVar 0, blank)), inl $ inr (inr (polVar 0, blank)), inl $ inr (inr (polVar 0, someSigmaVar 0))} / { inl $ inr (inr (polConst positive, blank)), inl $ inr (inr (polConst positive, blank)), inl $ inr (inr (polConst positive, blank))};
      { inl $ inr (inr (polVar 0, blank)), inl $ inr (inr (polVar 0, someSigmaVar 0)), inl $ inr (inr (polVar 0, someSigmaVar 1))} / { inl $ inr (inr (polConst positive, blank)), inl $ inr (inr (polConst positive, blank)), inl $ inr (inr (polConst positive, someSigmaVar 0))};
      { inl $ inr (inr (polVar 0, someSigmaVar 0)), inl $ inr (inr (polVar 0, someSigmaVar 1)), inl $ inr (inr (polVar 0, someSigmaVar 2))} / {inl $ inr (inr (polConst positive, blank)), inl $ inr (inr (polConst positive, someSigmaVar 0)), inl $ inr (inr (polConst positive, someSigmaVar 1))}
    ].

  (** In principle, we could define the instantiated cards for shifting the tape to the left as the polarity reversion of the cards for shifting to the right (as it is done by the inductive predicate) *)
  (** the problem with that is that we would also need to do that for the flat cards encoding natural numbers: but then we would need destructors for the encoding of finite types, using division, ... *)
  (** that would be unpleasant for the running time analysis *)
  (** instead, we explicitly define the rules again *)
  Definition mtlRules : list (card fAlphabet):=
    [
      {inl $ inr $ inr (polVar 0, someSigmaVar 0), inl $ inr $ inr (polVar 0, someSigmaVar 1), inl $ inr $ inr (polVar 0, someSigmaVar 2)} / {inl $ inr $ inr (polConst negative, someSigmaVar 1), inl $ inr $ inr (polConst negative, someSigmaVar 2), inl $ inr $ inr (polConst negative, someSigmaVar 3)}; 
      {inl $ inr $ inr (polVar 0, blank), inl $ inr $ inr (polVar 0, blank), inl $ inr $ inr (polVar 0, blank)} / {inl $ inr $ inr (polConst negative, blank), inl $ inr $ inr (polConst negative, blank), inl $ inr $ inr (polConst negative, someSigmaVar 0)}; 
      {inl $ inr $ inr (polVar 0, blank), inl $ inr $ inr (polVar 0, blank), inl $ inr $ inr (polVar 0, someSigmaVar 0)} / {inl $ inr $ inr (polConst negative, blank), inl $ inr $ inr (polConst negative, someSigmaVar 0), inl $ inr $ inr (polConst negative, someSigmaVar 1)};
      {inl $ inr $ inr (polVar 0, blank), inl $ inr $ inr (polVar 0, blank), inl $ inr $ inr (polVar 0, blank)} / {inl $ inr $ inr (polConst negative, blank), inl $ inr $ inr (polConst negative, blank), inl $ inr $ inr (polConst negative, blank)};
      {inl $ inr $ inr (polVar 0, blank), inl $ inr $ inr (polVar 0, someSigmaVar 0), inl $ inr $ inr (polVar 0, someSigmaVar 1)} / {inl $ inr $ inr (polConst negative, someSigmaVar 0), inl $ inr $ inr (polConst negative, someSigmaVar 1), inl $ inr $ inr (polConst negative, someSigmaVar 2)};
      {inl $ inr $ inr (polVar 0, someSigmaVar 0), inl $ inr $ inr (polVar 0, blank), inl $ inr $ inr (polVar 0, blank)}/ {inl $ inr $ inr (polConst negative, blank), inl $ inr $ inr (polConst negative, blank), inl $ inr $ inr (polConst negative, blank)};
      {inl $ inr $ inr (polVar 0, someSigmaVar 0), inl $ inr $ inr (polVar 0, someSigmaVar 1), inl $ inr $ inr (polVar 0, blank)} / {inl $ inr $ inr (polConst negative, someSigmaVar 1), inl $ inr $ inr (polConst negative, blank), inl $ inr $ inr (polConst negative, blank)};
      {inl $ inr $ inr (polVar 0, someSigmaVar 0), inl $ inr $ inr (polVar 0, someSigmaVar 1), inl $ inr $ inr (polVar 0, someSigmaVar 2)} / {inl $ inr $ inr (polConst negative, someSigmaVar 1), inl $ inr $ inr (polConst negative, someSigmaVar 2), inl $ inr $ inr (polConst negative, blank)} 
    ].

  Definition mtiRules : list (card fAlphabet) :=
    [
      {inl $ inr (inr (polVar 0, stateSigmaVar 0)), inl $ inr (inr (polVar 0, stateSigmaVar 1)), inl $ inr (inr (polVar 0, stateSigmaVar 2))} / {inl $ inr (inr (polConst neutral, stateSigmaVar 0)), inl $ inr (inr (polConst neutral, stateSigmaVar 1)), inl $ inr (inr (polConst neutral, stateSigmaVar 2))};
        {inl $ inr (inl (delimC)), inl $ inr (inr (polVar 0, blank)), inl $ inr (inr (polVar 0, blank))} / {inl $ inr (inl (delimC)), inl $ inr (inr (polVar 1, blank)), inl $ inr (inr (polVar 1, blank))};
        {inl $ inr (inr (polVar 0, blank)), inl $ inr (inr (polVar 0, blank)), inl $ inr (inl delimC)} / {inl $ inr (inr (polVar 1, blank)), inl $ inr (inr (polVar 1, blank)), inl $ inr (inl delimC)}
    ].

  (*we instantiate the rules for appropriate numbers of variables*)
  Definition finMTRCards := makeCardsFin (makeAllEvalEnvFin 1 4 0 0) mtrRules. 
  Definition finMTICards := makeCardsFin (makeAllEvalEnvFin 2 0 4 0) mtiRules.
  Definition finMTLCards := makeCardsFin (makeAllEvalEnvFin 1 4 0 0) mtlRules. 

  Definition finTapeCards := finMTRCards ++ finMTICards ++ finMTLCards. 

  Lemma duoton_incl (X : Type) (a b : X) (h : list X) : 
    [a; b] <<= h <-> a el h /\ b el h.
  Proof. 
    split; intros.
    - split; now apply H. 
    - destruct H. now intros a' [-> | [-> | []]]. 
  Qed.

  Lemma stateSigma_incl (l : list stateSigma) : l <<= elem (FstateSigma). 
  Proof. 
    unfold elem. cbn. 
    intros [] _.
    - right. eauto.  
    - now left. 
  Qed. 

  (*various tactics used for the proof of agreement *)
  Ltac force_In := lazymatch goal with
                  | [ |- ?a el ?a :: ?h] => left; reflexivity
                  | [ |- ?a el ?b :: ?h] => right; force_In
                  | [ |- [?a] <<= ?h] => apply singleton_incl; force_In
                  end. 


  Ltac solve_agreement_incl :=
    match goal with
      | [ |- [] <<= _] => intros ? [] 
      | [ |- ?a <<= elem Sigma] => intros ? ?; solve [apply elem_spec]
      | [ |- [?p] <<= [negative; positive; neutral]] => destruct p; force_In
      | [ |- ?p el [negative; positive; neutral]] => destruct p; force_In
      | [ |- [?a; ?b] <<= ?h] => apply duoton_incl; split; solve_agreement_incl 
      | [ |- ?a <<= elem FstateSigma] => apply stateSigma_incl 
      | [ |- ?a <<= toOptionList (elem Sigma)] => apply stateSigma_incl
      | [ |- _ <= _] => lia
    end. 

  Ltac solve_agreement_in_env :=
    split; [force_In | split; [ apply in_makeAllEvalEnv_iff; cbn; repeat split; solve_agreement_incl| reflexivity] ]. 

  Ltac destruct_var_env H :=
    repeat match type of H with
      | |?h| <= 0 => is_var h; destruct h; cbn in H; [clear H | now apply Nat.nle_succ_0 in H]
      | |?h| <= S ?n => is_var h; destruct h; cbn in H; [clear H | apply le_S_n in H]; destruct_var_env H
      end. 

  (*solve: an existential goal *)
  (*given a list of elements l, try to instantiate the existential with an element of l and then solve the remaining goal with cont *)
  Ltac rec_exists l out cont:=
    match l with
    | [] => fail
    | ?a :: ?l => exists a; cont(*;idtac "was" out*)
    | ?a :: ?l => rec_exists l constr:(S out)cont
    end. 

  Ltac solve_agreement_tape := unfold mtrRules, mtiRules, mtlRules; 
        match goal with
        | [ |- ex (fun r => r el ?h /\ _) ] => rec_exists h 0 ltac:(solve_agreement_in_env)
        end.

  Hint Extern 2 => exfalso; assumption : tmp.
  Lemma agreement_mtr: cards_list_ind_agree (@liftOrig Gamma shiftRightRules preludeSig') finMTRCards. 
  Proof.
    unfold cards_list_ind_agree; intros; split. 
    - intros. inv H. covHeadTape_inv2; apply in_makeCards_iff. 
      + exists (Build_evalEnv [p] [σ1; σ2; σ3; σ4] [] []). abstract solve_agreement_tape.
      + exists (Build_evalEnv [p] [σ1; σ1; σ1; σ1] [] []). abstract solve_agreement_tape. 
      + exists (Build_evalEnv [p] [] [] []). abstract solve_agreement_tape. 
      + exists (Build_evalEnv [p] [σ1; σ2] [] []). abstract solve_agreement_tape. 
      + exists (Build_evalEnv [p] [σ1; σ2; σ3] [] []). abstract solve_agreement_tape. 
      + exists (Build_evalEnv [p] [σ1] [] []). abstract solve_agreement_tape. 
      + exists (Build_evalEnv [p] [σ1; σ2] [] []). abstract solve_agreement_tape. 
      + exists (Build_evalEnv [p] [σ1; σ2; σ3] [] []). abstract solve_agreement_tape. 
    - intros. apply in_makeCards_iff in H as (env & rule & H1 & H2 & H3).  
      destruct env. apply in_makeAllEvalEnv_iff in H2. 
      destruct H2 as ((F1 & _) & (F2 & _) & (F3 & _) & (F4 & _)). 
      destruct_var_env F1; destruct_var_env F3; destruct_var_env F4; destruct_var_env F2.  
      all: cbn in H1; destruct_or H1; subst; cbn in H3; inv H3; eauto using liftOrig with tmp nocore.
  Qed. 

  Definition pFlipAlphabet (a : Alphabet) := 
    match a with 
      | inl s => inl (~s)
      | inr s => inr s
    end. 

  Lemma pFlipAlphabet_pFlipGamma_eqn γ x: inl γ = pFlipAlphabet x -> x = inl (~γ). 
  Proof. 
    destruct x; cbn; intros.  
    - inv H. now rewrite polarityFlipGamma_involution. 
    - congruence. 
  Qed. 

  Lemma agreement_mtl x1 x2 x3 x4 x5 x6 :
    @liftOrig Gamma shiftRightRules preludeSig' (pFlipAlphabet x1) (pFlipAlphabet x2) (pFlipAlphabet x3) (pFlipAlphabet x4) (pFlipAlphabet x5) (pFlipAlphabet x6) <-> {x3, x2, x1} / {x6, x5, x4} el finMTLCards.
  Proof. 
    split; intros. 
    - inv H. repeat match goal with [H : inl _ = pFlipAlphabet _ |- _] => apply pFlipAlphabet_pFlipGamma_eqn in H end.
      subst. covHeadTape_inv2; apply in_makeCards_iff. 
      + exists (Build_evalEnv [polarityFlip p] [σ3; σ2; σ1; σ4] [] []). abstract solve_agreement_tape.       
      + exists (Build_evalEnv [polarityFlip p] [σ1; σ1; σ1; σ1] [] []). abstract solve_agreement_tape. 
      + exists (Build_evalEnv [polarityFlip p] [] [] []). abstract solve_agreement_tape. 
      + exists (Build_evalEnv [polarityFlip p] [σ1; σ2] [] []). abstract solve_agreement_tape. 
      + exists (Build_evalEnv [polarityFlip p] [σ2; σ1; σ3] [] []). abstract solve_agreement_tape. 
      + exists (Build_evalEnv [polarityFlip p] [σ1] [] []). abstract solve_agreement_tape. 
      + exists (Build_evalEnv [polarityFlip p] [σ2; σ1] [] []). abstract solve_agreement_tape. 
      + exists (Build_evalEnv [polarityFlip p] [σ3; σ2; σ1] [] []). abstract solve_agreement_tape. 
    - intros. apply in_makeCards_iff in H as (env & rule & H1 & H2 & H3).  
      destruct env. apply in_makeAllEvalEnv_iff in H2. 
      destruct H2 as ((F1 & _) & (F2 & _) & (F3 & _) & (F4 & _)). 
      destruct_var_env F1; destruct_var_env F3; destruct_var_env F4; destruct_var_env F2.  
      all: cbn in H1; destruct_or H1; subst; cbn in H3; inv H3; cbn; eauto using liftOrig with tmp nocore. 
  Qed. 

  Lemma agreement_mti: cards_list_ind_agree (@liftOrig Gamma identityRules preludeSig') finMTICards. 
  Proof. 
    unfold cards_list_ind_agree; intros. split.
    - intros. inv H. covHeadTape_inv2; apply in_makeCards_iff. 
      + exists (Build_evalEnv [p] [] [m1; m2; m3] []). abstract solve_agreement_tape. 
      + exists (Build_evalEnv [p; p'] [] [] []). abstract solve_agreement_tape. 
      + exists (Build_evalEnv [p; p'] [] [] []). abstract solve_agreement_tape. 
    - intros. apply in_makeCards_iff in H as (env & rule & H1 & H2 & H3).  
      destruct env. apply in_makeAllEvalEnv_iff in H2. 
      destruct H2 as ((F1 & _) & (F2 & _) & (F3 & _) & (F4 & _)). 
      destruct_var_env F1; destruct_var_env F3; destruct_var_env F4; destruct_var_env F2.  
      all: cbn in H1; destruct_or H1; subst; cbn in H3; inv H3; eauto using liftOrig with tmp nocore.
  Qed. 

  Lemma agreement_tape : cards_list_ind_agree (@liftOrig Gamma tapeRules preludeSig') finTapeCards.  
  Proof. 
    split; intros. 
    - unfold finTapeCards. rewrite !in_app_iff. inv H. inv H0. 
      + right; right. apply agreement_mtl. cbn. eauto. 
      + left. apply agreement_mtr. eauto. 
      + right; left. apply agreement_mti. eauto. 
    - unfold finTapeCards in H. rewrite !in_app_iff in H. destruct_or H. 
      + apply agreement_mtr in H. inv H. eauto.  
      + apply agreement_mti in H; inv H; eauto. 
      + apply agreement_mtl in H. inv H. 
        repeat match goal with [H : inl _ = pFlipAlphabet _ |- _] => apply pFlipAlphabet_pFlipGamma_eqn in H end. 
        subst. constructor. constructor 1. now rewrite !polarityFlipGamma_involution.  
  Qed. 

  (** ** agreement for transitions *)
  (** For the transition rules, the current and next state as well the read and written symbols are fixed. *)
  (** Still, we model them as variables, but do not instantiate them with all possible environments, but only with environments where these variables are fixed. *)
  (** For that, we first generate the environments and then add the values of the constant variables.  *)

  Section fixAbstractTypes.
    Variable (X Y Z W M : Type). 
    (**add states and read/written symbols *)
    Definition envAddState (q : W) (env : evalEnv X Y Z W) := Build_evalEnv (polarityEnv env) (sigmaEnv env) (stateSigmaEnv env) (q :: stateEnv env). 
    Definition envAddSSigma (m : Z) (env : evalEnv X Y Z W) := Build_evalEnv (polarityEnv env) (sigmaEnv env) (m :: stateSigmaEnv env) (stateEnv env).

    (** only add states (used for the None/None case) *)
    Definition transEnvAddS (q q' : W) (env : evalEnv X Y Z W) := envAddState q $ envAddState q' env.

    Definition transEnvAddSM (q q' : W) (m m' : Z) (env : evalEnv X Y Z W) := envAddSSigma m $ envAddSSigma m' $ transEnvAddS q q' env.

    (**we define the transition generation functions over abstract makeCards instantiations *)
    Definition makeCardsT := list (evalEnv X Y Z W) -> list (card fAlphabet) -> list (card M).
  
    (** the environments in envList should contain q, q'; m, m' at the head *)
    Definition makeSome_base (ruleList : list (card fAlphabet)) (q q' : W) (m m' : Z) (r : makeCardsT) (envList : list (evalEnv X Y Z W)) :=
      r (map (transEnvAddSM q q' m m') envList) ruleList. 

    Definition makeSomeRight_rules : list (card fAlphabet):= 
      [{inl $ inr $ inr (polVar 0, stateSigmaVar 2), inl $ inl (0, stateSigmaVar 0), inl $ inr $ inr (polVar 0, stateSigmaVar 3)} / {inl $ inr $ inr (polConst positive, stateSigmaVar 4), inl $ inl (1, stateSigmaVar 2), inl $ inr $ inr (polConst positive, stateSigmaVar 1)};
       {inl $ inr $ inr (polVar 0, stateSigmaVar 2), inl $ inr $ inr (polVar 0, stateSigmaVar 3), inl $ inl (0, stateSigmaVar 0)} / {inl $ inr $ inr (polConst positive, stateSigmaVar 4), inl $ inr $ inr (polConst positive, stateSigmaVar 2), inl $ inl (1, stateSigmaVar 3)};
       {inl $ inl (0, stateSigmaVar 0), inl $ inr $ inr (polVar 0, stateSigmaVar 2), inl $ inr $ inr (polVar 0, stateSigmaVar 3)} / {inl $ inl (1, stateSigmaVar 4), inl $ inr $ inr (polConst positive, stateSigmaVar 1), inl $ inr $ inr (polConst positive, stateSigmaVar 2)}].

    Definition makeSomeRight := makeSome_base makeSomeRight_rules. 

    Definition makeSomeLeft_rules : list (card fAlphabet) := 
      [{inl $ inr $ inr (polVar 0, stateSigmaVar 2), inl $ inl (0, stateSigmaVar 0), inl $ inr $ inr (polVar 0, stateSigmaVar 3)} / {inl $ inr $ inr (polConst negative, stateSigmaVar 1), inl $ inl (1, stateSigmaVar 3), inl $ inr $ inr (polConst negative, stateSigmaVar 4)}; 
       {inl $ inl (0, stateSigmaVar 0), inl $ inr $ inr (polVar 0, stateSigmaVar 2), inl $ inr $ inr (polVar 0, stateSigmaVar 3)} / {inl $ inl (1, stateSigmaVar 2), inl $ inr $ inr (polConst negative, stateSigmaVar 3), inl $ inr $ inr (polConst negative, stateSigmaVar 4)};
       {inl $ inr $ inr (polVar 0, stateSigmaVar 2), inl $ inr $ inr (polVar 0, stateSigmaVar 3), inl $ inl (0, stateSigmaVar 0)} / {inl $ inr $ inr (polConst negative, stateSigmaVar 3), inl $ inr $ inr (polConst negative, stateSigmaVar 1), inl $ inl (1, stateSigmaVar 4)}].
    
    Definition makeSomeLeft := makeSome_base makeSomeLeft_rules. 

    Definition makeSomeStay_rules : list (card fAlphabet) := 
      [{inl $ inr $ inr (polVar 0, stateSigmaVar 2), inl $ inl (0, stateSigmaVar 0), inl $ inr $ inr (polVar 0, stateSigmaVar 3)} / {inl $ inr $ inr (polConst neutral, stateSigmaVar 2), inl $ inl (1, stateSigmaVar 1), inl $ inr $ inr (polConst neutral, stateSigmaVar 3)};
       {inl $ inl (0, stateSigmaVar 0), inl $ inr $ inr (polVar 0, stateSigmaVar 2), inl $ inr $ inr (polVar 0, stateSigmaVar 3)} / {inl $ inl (1, stateSigmaVar 1), inl $ inr $ inr (polConst neutral, stateSigmaVar 2), inl $ inr $ inr (polConst neutral, stateSigmaVar 3)};
       {inl $ inr $ inr (polVar 0, stateSigmaVar 2), inl $ inr $ inr (polVar 0, stateSigmaVar 3), inl $ inl (0, stateSigmaVar 0)} / {inl $ inr $ inr (polConst neutral, stateSigmaVar 2), inl $ inr $ inr (polConst neutral, stateSigmaVar 3), inl $ inl (1, stateSigmaVar 1)}].

    Definition makeSomeStay := makeSome_base makeSomeStay_rules.

    (** the none rules are a bit more complicated again *)
    Definition makeNone_base (ruleList : list (card fAlphabet)) (q q' : W) (r : makeCardsT) (envList : list (evalEnv X Y Z W))  := 
      r (map (transEnvAddS q q') envList) ruleList.

    Definition makeNoneRight_rules : list (card fAlphabet) := 
      [
        {inl $ inr $ inr (polVar 0, blank), inl $ inl (0, blank), inl $ inr $ inr (polVar 0, stateSigmaVar 0)} / {inl $ inr $ inr (polConst neutral, blank), inl $ inl (1, blank), inl $ inr $ inr (polConst neutral, stateSigmaVar 0)};
        {inl $ inr $ inr (polVar 0, someSigmaVar 0), inl $ inl (0, blank), inl $ inr $ inr (polVar 0, blank)} / {inl $ inr $ inr (polConst positive, stateSigmaVar 0), inl $ inl (1, someSigmaVar 0), inl $ inr $ inr (polConst positive, blank)};
        {inl $ inr $ inr (polVar 0, blank), inl $ inr $ inr (polVar 0, blank), inl $ inl (0, blank)} / {inl $ inr $ inr (polVar 1, blank), inl $ inr $ inr (polVar 1, blank), inl $ inl (1, blank)};
        {inl $ inr $ inr (polVar 0, blank), inl $ inr $ inr (polVar 0, someSigmaVar 0), inl $ inl (0, blank)} / {inl $ inr $ inr (polVar 1, blank), inl $ inr $ inr (polVar 1, blank), inl $ inl (1, someSigmaVar 0)};
        {inl $ inr $ inr (polVar 0, someSigmaVar 0), inl $ inr $ inr (polVar 0, someSigmaVar 1), inl $ inl (0, blank)} / {inl $ inr $ inr (polConst positive, stateSigmaVar 0), inl $ inr $ inr (polConst positive, someSigmaVar 0), inl $ inl (1, someSigmaVar 1)};
        {inl $ inl (0, blank), inl $ inr $ inr (polVar 0, blank), inl $ inr $ inr (polVar 0, blank)} / {inl $ inl (1, stateSigmaVar 0), inl $ inr $ inr (polVar 1, blank), inl $ inr $ inr (polVar 1, blank)};
        {inl $ inl (0, blank), inl $ inr $ inr (polVar 0, someSigmaVar 0), inl $ inr $ inr (polVar 0, stateSigmaVar 0)} / {inl $ inl (1, blank), inl $ inr $ inr (polVar 1, someSigmaVar 0), inl $ inr $ inr (polVar 1, stateSigmaVar 0)}
      ].

    Definition makeNoneRight := makeNone_base makeNoneRight_rules. 

    Definition makeNoneLeft_rules : list (card fAlphabet) := 
     [
        {inl $ inr $ inr (polVar 0, stateSigmaVar 0), inl $ inl (0, blank), inl $ inr $ inr (polVar 0, blank)} / {inl $ inr $ inr (polConst neutral, stateSigmaVar 0), inl $ inl (1, blank), inl $ inr $ inr (polConst neutral, blank)};
        {inl $ inr $ inr (polVar 0, blank), inl $ inl (0, blank), inl $ inr $ inr (polVar 0, someSigmaVar 0)} / {inl $ inr $ inr (polConst negative, blank), inl $ inl (1, someSigmaVar 0), inl $ inr $ inr (polConst negative, stateSigmaVar 0)};
        {inl $ inl (0, blank), inl $ inr $ inr (polVar 0, blank), inl $ inr $ inr (polVar 0, blank)} / {inl $ inl (1, blank), inl $ inr $ inr (polVar 1, blank), inl $ inr $ inr (polVar 1, blank)};
        {inl $ inl (0, blank), inl $ inr $ inr (polVar 0, someSigmaVar 0), inl $ inr $ inr (polVar 0, blank)} / {inl $ inl (1, someSigmaVar 0), inl $ inr $ inr (polVar 1, blank), inl $ inr $ inr (polVar 1, blank)};
        {inl $ inl (0, blank), inl $ inr $ inr (polVar 0, someSigmaVar 0), inl $ inr $ inr (polVar 0, someSigmaVar 1)} / {inl $ inl (1, someSigmaVar 0), inl $ inr $ inr (polConst negative, someSigmaVar 1), inl $ inr $ inr (polConst negative, stateSigmaVar 0)};
        {inl $ inr $ inr (polVar 0, blank), inl $ inr $ inr (polVar 0, blank), inl $ inl (0, blank)} / {inl $ inr $ inr (polVar 1, blank), inl $ inr $ inr (polVar 1, blank), inl $ inl (1, stateSigmaVar 0)};
        {inl $ inr $ inr (polVar 0, stateSigmaVar 0), inl $ inr $ inr (polVar 0, someSigmaVar 0), inl $ inl (0, blank)} / {inl $ inr $ inr (polConst neutral, stateSigmaVar 0), inl $ inr $ inr (polConst neutral, someSigmaVar 0), inl $ inl (1, blank)}
      ].

    Definition makeNoneLeft := makeNone_base makeNoneLeft_rules. 

    Definition makeNoneStay_rules : list (card fAlphabet) := 
      [
        {inl $ inr $ inr (polVar 0, stateSigmaVar 0), inl $ inl (0, blank), inl $ inr $ inr (polVar 0, blank)} / {inl $ inr $ inr (polConst neutral, stateSigmaVar 0), inl $ inl (1, blank), inl $ inr $ inr (polConst neutral, blank)};
        {inl $ inr $ inr (polVar 0, blank), inl $ inl (0, blank), inl $ inr $ inr (polVar 0, stateSigmaVar 0)} / {inl $ inr $ inr (polConst neutral, blank), inl $ inl (1, blank), inl $ inr $ inr (polConst neutral, stateSigmaVar 0)};
        {inl $ inl (0, blank), inl $ inr $ inr (polVar 0, someSigmaVar 0), inl $ inr $ inr (polVar 0, stateSigmaVar 0)} / {inl $ inl (1, blank), inl $ inr $ inr (polConst neutral, someSigmaVar 0), inl $ inr $ inr (polConst neutral, stateSigmaVar 0)};
        {inl $ inl (0, blank), inl $ inr $ inr (polVar 0, blank), inl $ inr $ inr (polVar 0, blank)} / {inl $ inl (1, blank), inl $ inr $ inr (polConst neutral, blank), inl $ inr $ inr (polConst neutral, blank)};
        {inl $ inr $ inr (polVar 0, stateSigmaVar 0), inl $ inr $ inr (polVar 0, someSigmaVar 0), inl $ inl (0, blank)} / {inl $ inr $ inr (polConst neutral, stateSigmaVar 0), inl $ inr $ inr (polConst neutral, someSigmaVar 0), inl $ inl (1, blank)};
        {inl $ inr $ inr (polVar 0, blank), inl $ inr $ inr (polVar 0, blank), inl $ inl (0, blank)} / {inl $ inr $ inr (polConst neutral, blank), inl $ inr $ inr (polConst neutral, blank), inl $ inl (1, blank)}
     ].

    Definition makeNoneStay := makeNone_base makeNoneStay_rules. 

    Definition makeHalt_rules : list (card fAlphabet) := 
      [
        {inl $ inr $ inr (polVar 0, stateSigmaVar 0), inl $ inl (0, stateSigmaVar 1), inl $ inr $ inr (polVar 0, stateSigmaVar 2)} / {inl $ inr $ inr (polConst neutral, stateSigmaVar 0), inl $ inl (0, stateSigmaVar 1), inl $ inr $ inr (polConst neutral, stateSigmaVar 2)};
        {inl $ inr $ inr (polVar 0, stateSigmaVar 0), inl $ inr $ inr (polVar 0, stateSigmaVar 1), inl $ inl (0, stateSigmaVar 2)} / {inl $ inr $ inr (polConst neutral, stateSigmaVar 0), inl $ inr $ inr (polConst neutral, stateSigmaVar 1), inl $ inl (0, stateSigmaVar 2)};
        {inl $ inl (0, stateSigmaVar 0), inl $ inr $ inr (polVar 0, stateSigmaVar 1), inl $ inr $ inr (polVar 0, stateSigmaVar 2)} / {inl $ inl (0, stateSigmaVar 0), inl $ inr $ inr (polConst neutral, stateSigmaVar 1), inl $ inr $ inr (polConst neutral, stateSigmaVar 2)}
      ].

    Definition makeHalt (q : W) (r : makeCardsT) (envList : list (evalEnv X Y Z W)) := r (map (envAddState q) envList) makeHalt_rules. 
  End fixAbstractTypes.

  (**The environments which assign values to the non-constant variables of the transition rules *)
  Definition fin_baseEnv := makeAllEvalEnvFin 1 0 3 0. 
  Definition fin_baseEnvNone := makeAllEvalEnvFin 2 2 2 0. 
  Definition fin_baseEnvHalt := makeAllEvalEnvFin 1 0 3 0. 

  (**Given a state and a current symbol, generate the rules for the corresponding transition *)
  Definition generateCardsForFinNonHalt (q : states) (m : stateSigma) :=
    match m, (trans (q, m)) with
    | _, (q', (Some σ, Lmove)) => makeSomeRight q q' m (Some σ) makeCardsFin fin_baseEnv
    | _, (q', (Some σ, Rmove)) => makeSomeLeft q q' m (Some σ) makeCardsFin fin_baseEnv
    | _, (q', (Some σ, Nmove)) => makeSomeStay q q' m (Some σ) makeCardsFin fin_baseEnv
    | Some σ, (q', (None, Lmove)) => makeSomeRight q q' (Some σ) (Some σ) makeCardsFin fin_baseEnv
    | Some σ, (q', (None, Rmove)) => makeSomeLeft q q' (Some σ) (Some σ) makeCardsFin fin_baseEnv
    | Some σ, (q', (None, Nmove)) => makeSomeStay q q' (Some σ) (Some σ) makeCardsFin fin_baseEnv
    | None, (q', (None, Lmove)) => makeNoneRight q q' makeCardsFin fin_baseEnvNone
    | None, (q', (None, Rmove)) => makeNoneLeft q q' makeCardsFin fin_baseEnvNone
    | None, (q', (None, Nmove)) => makeNoneStay q q' makeCardsFin fin_baseEnvNone
    end.

  (**Given a state, generate the cards needed for halting states *)
  Definition generateCardsForFinHalt (q : states) := makeHalt q makeCardsFin fin_baseEnvHalt. 
  (**given a state, generate either transition cards or halting cards for it *)
  Definition generateCardsForFin (q : states) :=
    if halt q then generateCardsForFinHalt q else
      concat (map (fun m => generateCardsForFinNonHalt q m) (elem FstateSigma)). 
  (**generate cards for all states*)
  Definition finStateCards := concat (map generateCardsForFin (elem states)).  

  (** *** Proof of transition agreement *)
  (**We first define the inductive rules structured in a different way, in order for it to resemble the structure of the list-based rules.
    (writing the list-based rules in a way which resembles the inductive predicates is not possible in an elegant way)
  *)

  (** bundling predicates *)
  (**we first group together according to the shift direction: left/right/stay *)

  Create HintDb etrans discriminated. 
  Hint Variables Opaque : etrans.
  Hint Constants Opaque : etrans.
  Inductive etransSomeLeft : states -> states -> stateSigma -> stateSigma -> transRule :=
  | etransSomeLeftLeftC q q' (a b : stateSigma)  γ1 γ2 γ3 γ4 γ5 γ6: transSomeLeftLeft q q' a γ1 γ2 γ3 γ4 γ5 γ6 -> etransSomeLeft q q' a b γ1 γ2 γ3 γ4 γ5 γ6
  | etransSomeLeftRightC q q' (a b : stateSigma)  γ1 γ2 γ3 γ4 γ5 γ6 : transSomeLeftRight q q' a b γ1 γ2 γ3 γ4 γ5 γ6 -> etransSomeLeft q q' a b γ1 γ2 γ3 γ4 γ5 γ6
  | etransSomeLeftCenterC q q' (a b : stateSigma)  γ1 γ2 γ3 γ4 γ5 γ6 : transSomeLeftCenter q q' a b γ1 γ2 γ3 γ4 γ5 γ6 -> etransSomeLeft q q' a b γ1 γ2 γ3 γ4 γ5 γ6. 

  Hint Constructors etransSomeLeft : etrans. 

  Inductive etransSomeRight : states -> states -> stateSigma -> stateSigma -> transRule :=
  | etransSomeRightLeftC q q' (a b: stateSigma)  γ1 γ2 γ3 γ4 γ5 γ6: transSomeRightLeft q q' a b γ1 γ2 γ3 γ4 γ5 γ6 -> etransSomeRight q q' a b γ1 γ2 γ3 γ4 γ5 γ6
  | etransSomeRightRightC q q' (a b : stateSigma)  γ1 γ2 γ3 γ4 γ5 γ6 : transSomeRightRight q q' a γ1 γ2 γ3 γ4 γ5 γ6 -> etransSomeRight q q' a b γ1 γ2 γ3 γ4 γ5 γ6
  | etransSomeRightCenterC q q' (a b : stateSigma)  γ1 γ2 γ3 γ4 γ5 γ6 : transSomeRightCenter q q' a b γ1 γ2 γ3 γ4 γ5 γ6 -> etransSomeRight q q' a b γ1 γ2 γ3 γ4 γ5 γ6. 

  Hint Constructors etransSomeRight : etrans. 

  Inductive etransSomeStay : states -> states -> stateSigma -> stateSigma -> transRule :=
  | etransSomeStayLeftC q q' (a b: stateSigma) γ1 γ2 γ3 γ4 γ5 γ6: transSomeStayLeft q q' a b γ1 γ2 γ3 γ4 γ5 γ6 -> etransSomeStay q q' a b γ1 γ2 γ3 γ4 γ5 γ6
  | etransSomeStayRightC q q' (a b: stateSigma) γ1 γ2 γ3 γ4 γ5 γ6 : transSomeStayRight q q' a b γ1 γ2 γ3 γ4 γ5 γ6 -> etransSomeStay q q' a b γ1 γ2 γ3 γ4 γ5 γ6
  | etransSomeStayCenterC q q' (a b: stateSigma) γ1 γ2 γ3 γ4 γ5 γ6 : transSomeStayCenter q q' a b γ1 γ2 γ3 γ4 γ5 γ6 -> etransSomeStay q q' a b γ1 γ2 γ3 γ4 γ5 γ6. 

  Hint Constructors etransSomeStay : etrans.


  Inductive etransNoneLeft : states -> states -> transRule :=
  | etransNoneLeftLeftC q q' γ1 γ2 γ3 γ4 γ5 γ6: transNoneLeftLeft q q' γ1 γ2 γ3 γ4 γ5 γ6 -> etransNoneLeft q q' γ1 γ2 γ3 γ4 γ5 γ6
  | etransNoneLeftRightC q q' γ1 γ2 γ3 γ4 γ5 γ6 : transNoneLeftRight q q' γ1 γ2 γ3 γ4 γ5 γ6 -> etransNoneLeft q q' γ1 γ2 γ3 γ4 γ5 γ6
  | etransNoneLeftCenterC q q' γ1 γ2 γ3 γ4 γ5 γ6 : transNoneLeftCenter q q' γ1 γ2 γ3 γ4 γ5 γ6 -> etransNoneLeft q q' γ1 γ2 γ3 γ4 γ5 γ6. 

  Hint Constructors etransNoneLeft : etrans. 

  Inductive etransNoneRight : states -> states -> transRule :=
  | etransNoneRightLeftC q q' γ1 γ2 γ3 γ4 γ5 γ6: transNoneRightLeft q q' γ1 γ2 γ3 γ4 γ5 γ6 -> etransNoneRight q q' γ1 γ2 γ3 γ4 γ5 γ6
  | etransNoneRightRightC q q' γ1 γ2 γ3 γ4 γ5 γ6 : transNoneRightRight q q' γ1 γ2 γ3 γ4 γ5 γ6 -> etransNoneRight q q' γ1 γ2 γ3 γ4 γ5 γ6
  | etransNoneRightCenterC q q' γ1 γ2 γ3 γ4 γ5 γ6 : transNoneRightCenter q q' γ1 γ2 γ3 γ4 γ5 γ6 -> etransNoneRight q q' γ1 γ2 γ3 γ4 γ5 γ6. 

  Hint Constructors etransNoneRight : etrans. 

  Inductive etransNoneStay : states -> states -> transRule :=
  | etransNoneStayLeftC q q'  γ1 γ2 γ3 γ4 γ5 γ6: transNoneStayLeft q q' γ1 γ2 γ3 γ4 γ5 γ6 -> etransNoneStay q q' γ1 γ2 γ3 γ4 γ5 γ6
  | etransNoneStayRightC q q' γ1 γ2 γ3 γ4 γ5 γ6 : transNoneStayRight q q' γ1 γ2 γ3 γ4 γ5 γ6 -> etransNoneStay q q' γ1 γ2 γ3 γ4 γ5 γ6
  | etransNoneStayCenterC q q' γ1 γ2 γ3 γ4 γ5 γ6 : transNoneStayCenter q q' γ1 γ2 γ3 γ4 γ5 γ6 -> etransNoneStay q q' γ1 γ2 γ3 γ4 γ5 γ6.

  Hint Constructors etransNoneStay : etrans. 

  Inductive etransRules : states -> stateSigma -> transRule :=
  | etransXSomeStay q m σ q' γ1 γ2 γ3 γ4 γ5 γ6: trans (q, m) = (q', (Some σ, Nmove)) -> etransSomeStay q q' m (Some σ) γ1 γ2 γ3 γ4 γ5 γ6 -> etransRules q m γ1 γ2 γ3 γ4 γ5 γ6
  | etransXSomeLeft q m σ q' γ1 γ2 γ3 γ4 γ5 γ6: trans (q, m) = (q', (Some σ, Rmove)) -> etransSomeLeft q q' m (Some σ) γ1 γ2 γ3 γ4 γ5 γ6 -> etransRules q m γ1 γ2 γ3 γ4 γ5 γ6
  | etransXSomeRight q m σ q' γ1 γ2 γ3 γ4 γ5 γ6: trans (q, m) = (q', (Some σ, Lmove)) -> etransSomeRight q q' m (Some σ) γ1 γ2 γ3 γ4 γ5 γ6 -> etransRules q m γ1 γ2 γ3 γ4 γ5 γ6
  | etransSomeNoneStay q σ q' γ1 γ2 γ3 γ4 γ5 γ6: trans (q, Some σ) = (q', (None, Nmove)) -> etransSomeStay q q' (Some σ) (Some σ) γ1 γ2 γ3 γ4 γ5 γ6 -> etransRules q (Some σ) γ1 γ2 γ3 γ4 γ5 γ6
  | etransSomeNoneLeft q σ q' γ1 γ2 γ3 γ4 γ5 γ6: trans (q, Some σ) = (q', (None, Rmove)) -> etransSomeLeft q q' (Some σ) (Some σ) γ1 γ2 γ3 γ4 γ5 γ6 -> etransRules q (Some σ) γ1 γ2 γ3 γ4 γ5 γ6
  | etransSomeNoneRight q σ q' γ1 γ2 γ3 γ4 γ5 γ6: trans (q, Some σ) = (q', (None, Lmove)) -> etransSomeRight q q' (Some σ) (Some σ) γ1 γ2 γ3 γ4 γ5 γ6 -> etransRules q (Some σ) γ1 γ2 γ3 γ4 γ5 γ6
  | etransNoneNoneStay q q' γ1 γ2 γ3 γ4 γ5 γ6: trans (q, None) = (q', (None, Nmove)) -> etransNoneStay q q' γ1 γ2 γ3 γ4 γ5 γ6 -> etransRules q None γ1 γ2 γ3 γ4 γ5 γ6
  | etransNoneNoneLeft q q' γ1 γ2 γ3 γ4 γ5 γ6: trans (q, None) = (q', (None, Rmove)) -> etransNoneLeft q q' γ1 γ2 γ3 γ4 γ5 γ6 -> etransRules q None γ1 γ2 γ3 γ4 γ5 γ6
  | etransNoneNoneRight q q' γ1 γ2 γ3 γ4 γ5 γ6: trans (q, None) = (q', (None, Lmove)) -> etransNoneRight q q' γ1 γ2 γ3 γ4 γ5 γ6 -> etransRules q None γ1 γ2 γ3 γ4 γ5 γ6.

  Hint Constructors etransRules : etrans.

  Inductive ehaltRules : states -> transRule :=
  | ehaltCenter q (m1 m2 : stateSigma) m p : ehaltRules q (inr (inr (p, m1))) (inl (q, m)) (inr (inr (p, m2))) (inr (inr (neutral, m1))) (inl (q, m)) (inr (inr (neutral, m2)))
  | ehaltRight q (m1 m2 m : stateSigma) p : ehaltRules q (inr (inr (p, m1))) (inr (inr (p, m2))) (inl (q, m)) (inr (inr (neutral, m1))) (inr (inr (neutral, m2))) (inl (q, m)) 
  | ehaltLeft q (m1 m2 m : stateSigma) p : ehaltRules q (inl (q, m)) (inr (inr (p, m1))) (inr (inr (p, m2))) (inl (q, m)) (inr (inr (neutral, m1))) (inr (inr (neutral, m2))).
  Hint Constructors ehaltRules : etrans. 

  Inductive estateRules : transRule :=
  | etransNonHaltC q m γ1 γ2 γ3 γ4 γ5 γ6 : halt q = false -> etransRules q m γ1 γ2 γ3 γ4 γ5 γ6 -> estateRules γ1 γ2 γ3 γ4 γ5 γ6
  | etransHaltC q γ1 γ2 γ3 γ4 γ5 γ6 : halt q = true -> ehaltRules q γ1 γ2 γ3 γ4 γ5 γ6 -> estateRules γ1 γ2 γ3 γ4 γ5 γ6. 

  Hint Constructors estateRules : etrans. 

  Definition esimRules γ1 γ2 γ3 γ4 γ5 γ6 := estateRules γ1 γ2 γ3 γ4 γ5 γ6 \/ tapeRules γ1 γ2 γ3 γ4 γ5 γ6. 
  Hint Unfold esimRules : etrans. 

  Hint Constructors transSomeStayLeft transSomeStayRight transSomeStayCenter 
    transSomeRightLeft transSomeRightRight transSomeRightCenter
    transSomeLeftLeft transSomeLeftRight transSomeLeftCenter
    : etrans. 
  Hint Constructors transNoneStayLeft transNoneStayRight transNoneStayCenter 
    transNoneRightLeft transNoneRightRight transNoneRightCenter
    transNoneLeftLeft transNoneLeftRight transNoneLeftCenter
    : etrans. 

  Notation ecovHeadSim := (coversHeadInd esimRules).   


  Ltac ecovHeadSim_inv := 
    repeat match goal with
             | [H : esimRules _ _ _ _ _ _ |- _] => inv H
             | [H : ecovHeadSim _ _ |- _ ] => inv H
             | [H : etransRules _ _ _ _ _ _ _ _ |- _] => inv H
             | [H : ehaltRules _ _ _ _ _ _ _ |- _] => inv H
             | [H : estateRules _ _ _ _ _ _ |- _] => inv H
             | [H : context[etransNoneStay] |- _] => inv H
             | [H : context[etransNoneLeft] |- _] => inv H
             | [H : context[etransNoneRight] |- _] => inv H
             | [H : context[etransSomeLeft] |- _] => inv H
             | [H : context[etransSomeRight] |- _] => inv H
             | [H : context[etransSomeStay] |- _] => inv H
               end; transRules_inv2.

  Lemma esim_sim_agree x1 x2 x3 x4 x5 x6: simRules x1 x2 x3 x4 x5 x6 <-> esimRules x1 x2 x3 x4 x5 x6. 
  Proof. 
     split. 
     - intros. destruct H as [H | [H | H]].  
       + left. once transRules_inv2; (eapply etransNonHaltC;[eassumption|]);once (econstructor;[eassumption|]); once [>constructor;constructor..]. 
       + haltRules_inv1; eauto 7 with etrans nocore tmp. 
       + eauto 3 with etrans nocore tmp.
     - intros. ecovHeadSim_inv; try destruct m. 
     all: first [simRulesAuto |right;right;assumption].
   Qed.   

  Section listDestructLength.
    Context {X : Type}.

    Lemma list_length_le0 (l : list X) : |l| <= 0 -> l = []. 
    Proof. destruct l; cbn; intros; [congruence | lia]. Qed. 

    Lemma list_length_le1 (l : list X): |l| <= 1 -> l = [] \/ exists x0, l = [x0].
    Proof.
      destruct l as [ | x0 l]; cbn; intros; [now left | right ].
      apply Peano.le_S_n in H. apply list_length_le0 in H as ->. eauto.  
    Qed.

    Lemma list_length_le2 (l : list X) : |l| <= 2 -> l = [] \/ (exists x0, l = [x0]) \/ (exists x0 x1, l = [x0; x1]). 
    Proof. 
      destruct l as [ | x0 l]; cbn; intros; [now left | right ].
      apply Peano.le_S_n in H. apply list_length_le1 in H as [-> | H]; eauto.
      right. destruct H as [x1 ->]. eauto.
    Qed. 

    Lemma list_length_le3 (l : list X) : |l| <= 3 -> l = [] \/ (exists x0, l = [x0]) \/ (exists x0 x1, l = [x0; x1]) \/ (exists x0 x1 x2, l = [x0; x1; x2]). 
    Proof. 
      destruct l as [ | x0 l]; cbn; intros; [now left | right]. 
      apply Peano.le_S_n in H. apply list_length_le2 in H as [-> | [(x1 & ->) | (x1 & x2 & ->) ]]; eauto 10.
    Qed. 
  End listDestructLength.

  Ltac list_destruct_length :=
    repeat match goal with
            | [H : |?l| <= 0 |- _] => apply list_length_le0 in H as ->
            | [H : |?l| <= 1 |- _] => apply list_length_le1 in H as [-> | (? & ->)]
            | [H : |?l| <= 2 |- _] => apply list_length_le2 in H as [-> | [ (? & ->) | (? & ? & ->) ]]
            | [H : |?l| <= 3 |- _] => apply list_length_le3 in H as [-> | [ (? & ->) | [(? & ? & ->) | (? & ? & ? & ->)]]]
      end. 

  Lemma agreement_trans_unfold_env (X Y Z W M: Type) l (envList : list (evalEnv X Y Z W)) card' (f : evalEnv X Y Z W -> evalEnv X Y Z W) r : 
    (exists env rule, rule el l /\ env el map f envList /\ Some card' = generateCard r env rule) 
    <-> (exists env rule, rule el l /\ env el envList /\ Some card' = generateCard (M:=M) r (f env) rule).
  Proof. 
    split; intros (env & rule & H1 & H2 & H3).
    - apply in_map_iff in H2 as (env' & <- & H2). eauto. 
    - exists (f env), rule. rewrite in_map_iff. eauto.
  Qed. 

  (*solve: an existential goal *)
  (*given a list of elements l, try to instantiate the existential with an element of l and then solve the remaining goal with cont *)
  Ltac rec_existsAt l k cont:=
    lazymatch constr:((l , k)) with
    | (?a :: ?l,0) => exists a; cont
    | (?a :: ?l,S ?k) => rec_existsAt l k cont
    end. 
  
  Ltac solve_agreement_transAt k :=
    match goal with
      | [ |- ex (fun x => (x el ?h /\ _))] => rec_existsAt h k ltac:(split; [ force_In | split; [ | reflexivity]])
    end;
    apply in_makeAllEvalEnv_iff; repeat split; cbn; solve_agreement_incl.

  Ltac solve_agreement_trans :=
    match goal with
      | [ |- ex (fun x => (x el ?h /\ _))] => rec_exists h 0 ltac:(split; [ force_In | split; [ | reflexivity]])
    end;
    apply in_makeAllEvalEnv_iff; repeat split; cbn; solve_agreement_incl.

  Lemma TCCCard_inj sig (p1 p2 c1 c2 : TCCCardP sig) : p1 / c1 = p2 / c2 -> p1 = p2 /\ c1 = c2. 
  Proof. 
    intros H. inv H. tauto. 
  Qed.
  Lemma TCCCardP_inj sig (s1 s2 s3 t1 t2 t3 : sig) : {s1, s2, s3} = {t1, t2, t3} -> s1 = t1 /\ s2 = t2 /\ s3 = t3. 
  Proof. 
    intros H. inv H. tauto. 
  Qed.

  Lemma agreement_nonhalt q m: cards_list_ind_agree (@liftOrig Gamma (etransRules q m) preludeSig') (generateCardsForFinNonHalt q m).
  Proof. 
    split; intros. 
    - inv H. ecovHeadSim_inv; unfold generateCardsForFinNonHalt.
      1-18: try destruct m.
      all: foldAbbrevs;rewrite H; apply in_makeCards_iff, agreement_trans_unfold_env.
      all: unfold makeSomeStay_rules, makeSomeLeft_rules, makeSomeRight_rules, makeNoneLeft_rules, makeNoneRight_rules, makeNoneStay_rules;foldAbbrevs. 
      (*some things are easy to automate, some aren't... *)
      * exists (Build_evalEnv [p] [] [m1; m2] []). abstract solve_agreement_transAt 1.
      * exists (Build_evalEnv [p] [] [m1; m2] []). abstract solve_agreement_transAt 1. 
      * exists (Build_evalEnv [p] [] [m1; m2] []). abstract solve_agreement_transAt 2.
      * exists (Build_evalEnv [p] [] [m1; m2] []). abstract solve_agreement_transAt 2. 
      * exists (Build_evalEnv [p] [] [m1; m2] []). abstract solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2] []). abstract solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2; m3] []). abstract solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2; m3] []). abstract solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2; m3] []). abstract solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2; m3] []). abstract solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2; m3] []). abstract solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2; m3] []). abstract solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2; m3] []). abstract solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2; m3] []). abstract solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2; m3] []). abstract solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2; m3] []). abstract solve_agreement_trans.
      * exists (Build_evalEnv [p] [] [m1; m2; m3] []). abstract solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2; m3] []). abstract solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2] []). abstract solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2] []). abstract solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2] []). abstract solve_agreement_trans.
      * exists (Build_evalEnv [p] [] [m1; m2; m3] []). abstract solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2; m3] []). abstract solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2; m3] []). abstract solve_agreement_trans.
      * exists (Build_evalEnv [p] [] [m1; m2; m3] []). abstract solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2; m3] []). abstract solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2; m3] []). abstract solve_agreement_trans.
      * exists (Build_evalEnv [p] [σ] [m] []). abstract solve_agreement_trans.
      * exists (Build_evalEnv [p] [] [] []). abstract solve_agreement_trans. 
      * exists (Build_evalEnv [p] [σ] [m] []). abstract solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [] []). abstract solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m] []). abstract solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m] []). abstract solve_agreement_trans. 
      * exists (Build_evalEnv [p; p'] [] [] []). abstract solve_agreement_trans. 
      * exists (Build_evalEnv [p; p'] [σ] [] []). abstract solve_agreement_trans. 
      * exists (Build_evalEnv [p] [σ1; σ2] [m] []). abstract solve_agreement_trans. 
      * exists (Build_evalEnv [p; p'] [] [m] []). abstract solve_agreement_trans. 
      * exists (Build_evalEnv [p] [σ] [m1] []). abstract solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m] []). abstract solve_agreement_trans. 
      * exists (Build_evalEnv [p] [σ] [m] []). abstract solve_agreement_trans. 
      * exists (Build_evalEnv [p; p'] [] [m] []). abstract solve_agreement_trans. 
      * exists (Build_evalEnv [p; p'] [σ] [m] []). abstract solve_agreement_trans. 
      * exists (Build_evalEnv [p; p'] [] [] []). abstract solve_agreement_trans. 
      * exists (Build_evalEnv [p; p'] [σ] [] []). abstract solve_agreement_trans. 
      * exists (Build_evalEnv [p] [σ1; σ2] [m1] []). abstract solve_agreement_trans.
      * exists (Build_evalEnv [p] [] [m] []). abstract solve_agreement_trans. 
      * exists (Build_evalEnv [p] [σ] [m] []). abstract solve_agreement_trans.
    - unfold generateCardsForFinNonHalt in H. 
      destruct m; destruct trans eqn:H0; destruct p, o;
      destruct m; apply in_makeCards_iff in H as (rule & env & H1 & H2 & H3);
      apply in_map_iff in H2 as ([] & <- & H2);
      apply in_makeAllEvalEnv_iff in H2 as ((F1 & _) & (F2 & _) & (F3 & _) & (F4 & _));
      cbn in H1; destruct_or H1; try rewrite <- H1 in *; 
      list_destruct_length; cbn in *.
      all: try lazymatch goal with
      | [H : Some _ = None |- _] => discriminate H
      | [H : Some _ = optReturn _ |- _] => foldAbbrevs;apply Some_injective in H; apply TCCCard_inj in H as [(?&?&?)%TCCCardP_inj (?&?&?)%TCCCardP_inj]; subst
      | [H : False |- _] => destruct H
      end. 
      all:constructor;once (econstructor;[eassumption|]); once [>constructor;constructor..]. 
   Qed.  
          
  Lemma agreement_halt q: cards_list_ind_agree (@liftOrig Gamma (ehaltRules q) preludeSig') (generateCardsForFinHalt q). 
  Proof.
    split; intros. 
    - inv H. ecovHeadSim_inv; unfold generateCardsForFinHalt, makeHalt, makeHalt_rules.
      all: apply in_makeCards_iff, agreement_trans_unfold_env.
      + exists (Build_evalEnv [p] [] [m1; m; m2] []). abstract solve_agreement_trans. 
      + exists (Build_evalEnv [p] [] [m1; m2; m] []). abstract solve_agreement_trans. 
      + exists (Build_evalEnv [p] [] [m; m1; m2] []). abstract solve_agreement_trans. 
    - unfold generateCardsForFinNonHalt in H. 
      apply in_makeCards_iff in H as (rule & env & H1 & H2 & H3);
      apply in_map_iff in H2 as ([] & <- & H2);
      apply in_makeAllEvalEnv_iff in H2 as ((F1 & _) & (F2 & _) & (F3 & _) & (F4 & _));
      cbn in H1; destruct_or H1; try rewrite <- H1 in *; 
      list_destruct_length; cbn in *. 
      all: try match goal with
      | [H : Some _ = None |- _] => discriminate H
      | [H : Some _ = optReturn _ |- _] => apply Some_injective in H; apply TCCCard_inj in H as [(?&?&?)%TCCCardP_inj (?&?&?)%TCCCardP_inj]; subst
      | [H : False |- _] => destruct H
      end. 
      all: constructor;constructor.
  Qed. 

  Lemma agreement_transition: cards_list_ind_agree (@liftOrig Gamma estateRules preludeSig') finStateCards. 
  Proof. 
    split. 
    - intros. unfold finStateCards. apply in_concat_map_iff.
      inv H. inv H0. 
      + exists q. split; [ apply elem_spec | ]. 
        unfold generateCardsForFin. rewrite H. apply in_concat_map_iff. 
        exists m; split; [apply elem_spec | ]. 
        apply agreement_nonhalt; eauto.
      + exists q; split; [apply elem_spec | ]. 
        unfold generateCardsForFin. rewrite H. 
        apply agreement_halt; eauto. 
    - intros. unfold finStateCards in H.
      apply in_concat_map_iff in H as (q & _ & H). 
      unfold generateCardsForFin in H.
      destruct halt eqn:H1. 
      + apply agreement_halt in H. inv H. eauto using liftOrig with etrans. 
      + apply in_concat_map_iff in H as (m & _ & H).
        apply agreement_nonhalt in H. inv H. eauto using liftOrig with etrans.
  Qed. 

  Definition allFinSimCards := finTapeCards ++ finStateCards.

  Lemma agreement_sim: cards_list_ind_agree (@liftOrig Gamma simRules preludeSig') allFinSimCards. 
  Proof. 
    unfold cards_list_ind_agree. intros. split; intros. 
    - unfold allFinSimCards;  apply in_app_iff. inv H. 
      apply esim_sim_agree in H0. inv H0. 
      + right. apply agreement_transition. eauto. 
      + left. apply agreement_tape. eauto.
    - unfold allFinSimCards in H; apply in_app_iff in H. inv H. 
      + apply agreement_tape in H0. inv H0. eauto using liftOrig with trans.  
      + apply agreement_transition in H0. inv H0. constructor. apply esim_sim_agree. eauto using liftOrig with etrans. 
  Qed. 

  (**now the agreement of the prelude cards *)
  (**the start state is expected to reside in state variable 0 *)
  (**the star rules use state sigma variable 0 *)
  (**for the nsig and star rules, sigma variables 0-2 are needed *)
  Definition listPreludeRules : list (card fAlphabet) :=
    [
      {inr fnblank, inr fnblank, inr fnblank} / {inl $ inr $ inr (polConst neutral, blank), inl $ inr $ inr (polConst neutral, blank), inl $ inr $ inr (polConst neutral, blank)}; 
      {inr fndelimC, inr fnblank, inr fnblank} / {inl $ inr $ inl delimC, inl $ inr $ inr (polConst neutral, blank), inl $ inr $ inr (polConst neutral, blank)}; 
      {inr fnblank, inr fnblank, inr fndelimC} / {inl $ inr $ inr (polConst neutral, blank), inl $ inr $ inr (polConst neutral, blank), inl $ inr $ inl delimC}; 
      {inr fnblank, inr fnblank, inr fninit} / {inl $ inr $ inr (polConst neutral, blank), inl $ inr $ inr (polConst neutral, blank), inl $ inl ( 0, blank)}; (*the start state is expected to reside in variable 0 *)
      {inr fnblank, inr fninit, inr $ fnsigVar 0} / {inl $ inr $ inr (polConst neutral, blank), inl $ inl (0, blank), inl $ inr $ inr (polConst neutral, someSigmaVar 0)};
      {inr fnblank, inr fninit, inr fnstar} / {inl $ inr $ inr (polConst neutral, blank), inl $ inl (0, blank), inl $ inr $ inr (polConst neutral, stateSigmaVar 0)};
      {inr fnblank, inr fninit, inr fnblank} / {inl $ inr $ inr (polConst neutral, blank), inl $ inl (0, blank), inl $ inr $ inr (polConst neutral, blank)};
      {inr fninit, inr fnblank, inr fnblank} / {inl $ inl (0, blank), inl $ inr $ inr (polConst neutral, blank), inl $ inr $ inr (polConst neutral, blank)}; 
      {inr fninit, inr $ fnsigVar 0, inr fnstar} / {inl $ inl (0, blank), inl $ inr $ inr (polConst neutral, someSigmaVar 0), inl $ inr $ inr (polConst neutral, stateSigmaVar 0)};
      {inr fninit, inr $ fnsigVar 0, inr fnblank} / {inl $ inl (0, blank), inl $ inr $ inr (polConst neutral, someSigmaVar 0), inl $ inr $ inr (polConst neutral, blank)};
      {inr fninit, inr $ fnsigVar 0, inr $ fnsigVar 1} / { inl $ inl (0, blank), inl $ inr $ inr (polConst neutral, someSigmaVar 0), inl $ inr $ inr (polConst neutral, someSigmaVar 1)};
      {inr fninit, inr fnstar, inr fnblank} / {inl $ inl (0, blank), inl $ inr $ inr (polConst neutral, stateSigmaVar 0), inl $ inr $ inr (polConst neutral, blank)};
      {inr fninit, inr fnstar, inr fnstar} / {inl $ inl (0, blank), inl $ inr $ inr (polConst neutral, someSigmaVar 0), inl $ inr $ inr (polConst neutral, stateSigmaVar 0)}; 
      {inr fninit, inr fnstar, inr fnstar} / {inl $ inl (0, blank), inl $ inr $ inr (polConst neutral, blank), inl $ inr $ inr (polConst neutral, blank)};
      {inr $ fnsigVar 0, inr $ fnsigVar 1, inr $ fnsigVar 2 } / {inl $ inr $ inr (polConst neutral, someSigmaVar 0), inl $ inr $ inr (polConst neutral, someSigmaVar 1), inl $ inr $ inr (polConst neutral, someSigmaVar 2)};
      {inr $ fnsigVar 0, inr $ fnsigVar 1, inr fnstar} / {inl $ inr $ inr (polConst neutral, someSigmaVar 0), inl $ inr $ inr (polConst neutral, someSigmaVar 1), inl $ inr $ inr (polConst neutral, stateSigmaVar 0)};
      {inr $ fnsigVar 0, inr fnstar, inr fnstar} / {inl $ inr $ inr (polConst neutral, someSigmaVar 0), inl $ inr $ inr (polConst neutral, someSigmaVar 1), inl $ inr $ inr (polConst neutral, stateSigmaVar 0)}; 
      {inr $ fnsigVar 0, inr fnstar, inr fnstar} / {inl $ inr $ inr (polConst neutral, someSigmaVar 0), inl $ inr $ inr (polConst neutral, blank), inl $ inr $ inr (polConst neutral, blank)};
      {inr $ fnsigVar 0, inr fnstar, inr fnblank} / {inl $ inr $ inr (polConst neutral, someSigmaVar 0), inl $ inr $ inr (polConst neutral, stateSigmaVar 0), inl $ inr $ inr (polConst neutral, blank)};
      {inr $ fnsigVar 0, inr $ fnsigVar 1, inr fnblank} / {inl $ inr $ inr (polConst neutral, someSigmaVar 0), inl $ inr $ inr (polConst neutral, someSigmaVar 1), inl $ inr $ inr (polConst neutral, blank)};
      {inr $ fnsigVar 0, inr fnblank, inr fnblank } / {inl $ inr $ inr (polConst neutral, someSigmaVar 0), inl $ inr $ inr (polConst neutral, blank), inl $ inr $ inr (polConst neutral, blank)};
      {inr fnstar, inr fnstar, inr fnstar} / {inl $ inr $ inr (polConst neutral, someSigmaVar 0), inl $ inr $ inr (polConst neutral, someSigmaVar 1), inl $ inr $ inr (polConst neutral, stateSigmaVar 0)}; 
      {inr fnstar, inr fnstar, inr fnstar} / {inl $ inr $ inr (polConst neutral, someSigmaVar 0), inl $ inr $ inr (polConst neutral, blank), inl $ inr $ inr (polConst neutral, blank)}; 
      {inr fnstar, inr fnstar, inr fnstar} / {inl $ inr $ inr (polConst neutral, blank), inl $ inr $ inr (polConst neutral, blank), inl $ inr $ inr (polConst neutral, blank)};
      {inr fnstar, inr fnstar, inr fnblank} / {inl $ inr $ inr (polConst neutral, someSigmaVar 0), inl $ inr $ inr (polConst neutral, stateSigmaVar 0), inl $ inr $ inr (polConst neutral, blank)}; 
      {inr fnstar, inr fnstar, inr fnblank} / {inl $ inr $ inr (polConst neutral, blank), inl $ inr $ inr (polConst neutral, blank), inl $ inr $ inr (polConst neutral, blank)}; 
      {inr fnstar, inr fnblank, inr fnblank} / {inl $ inr $ inr (polConst neutral, stateSigmaVar 0), inl $ inr $ inr (polConst neutral, blank), inl $ inr $ inr (polConst neutral, blank)}
    ]. 


  Definition makePreludeCards (X Y Z W M : Type) (q : W) (r : makeCardsT X Y Z W M) (envList : list (evalEnv X Y Z W)) :=
    r (map (envAddState q) envList) listPreludeRules.

  Definition fin_baseEnvPrelude := makeAllEvalEnvFin 0 3 1 0. 

  Definition finPreludeCards := makePreludeCards start makeCardsFin fin_baseEnvPrelude.

  Ltac solve_agreement_prelude := 
    match goal with
      | [ |- ex (fun x => (x el ?h /\ _))] => rec_exists h 0 ltac:(split; [ force_In | split; [ | cbn; reflexivity]])
    end;
    apply in_makeAllEvalEnv_iff; repeat split; cbn; solve_agreement_incl.


  Ltac solve_agreement_preludeAt k := 
    match goal with
      | [ |- ex (fun x => (x el ?h /\ _))] => rec_existsAt h k ltac:(split; [ force_In | split; [ | cbn; reflexivity]])
    end;
    apply in_makeAllEvalEnv_iff; repeat split; cbn; solve_agreement_incl.

  Lemma agreement_prelude : cards_list_ind_agree (@liftPrelude Gamma preludeSig' preludeRules) finPreludeCards.
  Proof with abstract solve_agreement_prelude. 
    split; intros. 
    - inv H. inv H0. 
      all: apply in_makeCards_iff, agreement_trans_unfold_env; unfold listPreludeRules.
      +abstract (solve [exists (Build_evalEnv [] [] [] []); solve_agreement_preludeAt 0]). 
      +abstract (solve [exists (Build_evalEnv [] [] [] []); solve_agreement_preludeAt 1]). 
      +abstract (solve [exists (Build_evalEnv [] [] [] []); solve_agreement_preludeAt 2]). 
      +abstract (solve [exists (Build_evalEnv [] [] [] []); solve_agreement_preludeAt 3]). 
      + exists (Build_evalEnv [] [σ] [] []);abstract solve_agreement_preludeAt 4. 
      + exists (Build_evalEnv [] [] [m] []);abstract solve_agreement_preludeAt 5. 
      +abstract (solve [exists (Build_evalEnv [] [] [] []); solve_agreement_preludeAt 6]). 
      +abstract (solve [exists (Build_evalEnv [] [] [] []); solve_agreement_preludeAt 7]). 
      + exists (Build_evalEnv [] [σ1] [m1] []);abstract solve_agreement_preludeAt 8. 
      + exists (Build_evalEnv [] [σ1] [] []);abstract solve_agreement_preludeAt 9. 
      + exists (Build_evalEnv [] [σ1; σ2] [] []);abstract solve_agreement_preludeAt 10. 
      + exists (Build_evalEnv [] [] [m] []);abstract solve_agreement_preludeAt 11. 
      + exists (Build_evalEnv [] [σ] [m] []);abstract solve_agreement_preludeAt 12. 
      +abstract (solve [exists (Build_evalEnv [] [] [] []); solve_agreement_preludeAt 13]). 
      + exists (Build_evalEnv [] [σ1; σ2; σ3] [] []);abstract solve_agreement_preludeAt 14. 
      + exists (Build_evalEnv [] [σ1; σ2] [m1] []);abstract solve_agreement_preludeAt 15. 
      + exists (Build_evalEnv [] [σ1; σ2] [m1] []);abstract solve_agreement_preludeAt 16. 
      + exists (Build_evalEnv [] [σ1] [] []);abstract solve_agreement_preludeAt 17. 
      + exists (Build_evalEnv [] [σ1] [m1] []);abstract solve_agreement_preludeAt 18. 
      + exists (Build_evalEnv [] [σ1; σ2] [] []);abstract solve_agreement_preludeAt 19. 
      + exists (Build_evalEnv [] [σ1] [] []);abstract solve_agreement_preludeAt 20. 
      + exists (Build_evalEnv [] [σ1; σ2] [m] []);abstract solve_agreement_preludeAt 21. 
      + exists (Build_evalEnv [] [σ] [] []);abstract solve_agreement_preludeAt 22.
      +abstract (solve [exists (Build_evalEnv [] [] [] []); solve_agreement_preludeAt 23]).  
      + exists (Build_evalEnv [] [σ] [m] []);abstract solve_agreement_preludeAt 24.
      +abstract (solve [exists (Build_evalEnv [] [] [] []); solve_agreement_preludeAt 25]).  
      + (exists (Build_evalEnv [] [] [m] []);abstract solve_agreement_preludeAt 26). 
    - unfold finPreludeCards in H. 
      apply in_makeCards_iff in H as (rule & env & H1 & H2 & H3);
      apply in_map_iff in H2 as ([] & <- & H2);
      apply in_makeAllEvalEnv_iff in H2 as ((F1 & _) & (F2 & _) & (F3 & _) & (F4 & _));
      cbn in H1; destruct_or H1; try rewrite <- H1 in *; 
      list_destruct_length; cbn in *. 
      all: try match goal with
      | [H : Some _ = None |- _] => discriminate H
      | [H : Some _ = optReturn _ |- _] => apply Some_injective in H; apply TCCCard_inj in H as [(?&?&?)%TCCCardP_inj (?&?&?)%TCCCardP_inj]; subst
      | [H : False |- _] => destruct H
      end. 
      par: auto 5 using liftPrelude with core.
  Qed. 

  Definition allFinCards := finPreludeCards ++ allFinSimCards. 

  Lemma fin_agreement : cards_list_ind_agree allRules allFinCards. 
  Proof. 
    split; intros. 
    + inv H. 
      * apply agreement_prelude in H0. unfold allFinCards. eauto.  
      * apply agreement_sim in H0. unfold allFinCards. eauto. 
    + unfold allFinCards in H. apply in_app_iff in H. destruct_or H. 
      * apply agreement_prelude in H. constructor. assumption.
      * apply agreement_sim in H. constructor 2. assumption. 
  Qed. 

  (** the reduction using the list-based cards *)
  Lemma SingleTMGenNP_to_TCC : 
    TCCLang (@Build_TCC (FinType (EqType preludeSig)) (map inr preludeInitialString) allFinCards (map (map inl) finalSubstrings) (1 + t))
    <-> SingleTMGenNP (existT _ Sigma (fTM, fixedInput, k', t)). 
  Proof. 
    rewrite tpr_ptpr_agree. 
    * apply SingleTMGenNP_to_PTCC. 
    * apply fin_agreement. 
  Qed.

  (** *** Generation of flat list-based cards *)
  (** tape cards *)
  Definition flatMTRCards := makeCardsFlat (makeAllEvalEnvFlat 1 4 0 0) mtrRules.
  Definition flatMTICards := makeCardsFlat (makeAllEvalEnvFlat 2 0 4 0) mtiRules.
  Definition flatMTLCards := makeCardsFlat (makeAllEvalEnvFlat 1 4 0 0) mtlRules.
  Definition flatTapeCards := flatMTRCards ++ flatMTICards ++ flatMTLCards. 

  Lemma isFlatTCardsOf_concat (X : finType) flat1 flat2 (fin1 fin2 : list (card X)): isFlatTCardsOf flat1 fin1 -> isFlatTCardsOf flat2 fin2 -> isFlatTCardsOf (flat1 ++ flat2) (fin1 ++ fin2). 
  Proof using flatTM_TM_compat.
    intros; split; intros. 
    - apply in_app_iff in H1 as [H1 | H1]; [apply H in H1 | apply H0 in H1]; firstorder.
    - apply in_app_iff in H1 as [H1 | H1]; [apply H in H1 | apply H0 in H1]; firstorder. 
  Qed. 
  
  Lemma fin_flat_tapeCards_agree : isFlatTCardsOf flatTapeCards finTapeCards. 
  Proof using flatTM_TM_compat. 
    unfold flatTapeCards, finTapeCards. 
    apply isFlatTCardsOf_concat; [ | apply isFlatTCardsOf_concat]. 
    all: apply makeCards_isFlatCardOf, makeAllEvalEnv_isFlatEnvOf; 
    match goal with 
    | [ |- context[flatStateSigma]] => rewrite stateSigma_finRepr
    | [ |- context[flatPolarity]] => rewrite polarity_finRepr
    | [ |- context[flatSigma]] => rewrite Sigma_finRepr
    | [ |- context[flatstates]] => rewrite states_finRepr 
    end. 
    all: apply seq_isFlatListOf. 
  Qed. 

  (** transition cards *)
  Definition opt_finReprEl' (X : finType) (a : option nat) (b : option X) := a = option_map index b. 
  Lemma opt_finReprElP_case (X : finType) (a : option nat) (b : option X) : opt_finReprEl' a b ->
    match a with 
    | None => b = None
    | Some a' => exists b', b = Some b' /\ finReprEl' a' b'
    end. 
  Proof. 
    unfold opt_finReprEl'. destruct a. 
    - destruct b; cbn; intros H; inv H. exists e; split; unfold finReprEl'; eauto.
    - destruct b; cbn; intros H; inv H. easy.
  Qed. 

  Lemma opt_finReprElP_Some (X : finType) a (a' : X) : finReprEl' a a' -> opt_finReprEl' (Some a) (Some a'). 
  Proof. 
    intros. unfold opt_finReprEl'. rewrite <- H. easy.
  Qed. 

  Lemma opt_finReprElP_None (X : finType) : @opt_finReprEl' X None None. 
  Proof. unfold opt_finReprEl'. easy. Qed.

  Notation flatTrans := (TMflat.trans flatTM). 
  Notation flatHalt := (TMflat.halt flatTM).
  Notation flatStart := (TMflat.start flatTM).

  Definition flat_baseEnv := makeAllEvalEnvFlat 1 0 3 0.
  Definition flat_baseEnvNone := makeAllEvalEnvFlat 2 2 2 0.
  Definition flat_baseEnvHalt := makeAllEvalEnvFlat 1 0 3 0.

  Definition fOpt a := match a with None => 0 | Some a => S a end. 

  (** given a state and a current symbol, generate the cards for the corresponding transition *)
  Definition opt_generateCardsForFlatNonHalt (q : nat) (m : option nat) transt:=
    match m, transt with
    | _, (q', (Some x, Lmove)) => makeSomeRight q q' (fOpt m) (fOpt $ Some x) makeCardsFlat flat_baseEnv
    | _, (q', (Some x, Rmove)) => makeSomeLeft q q' (fOpt m) (fOpt $ Some x) makeCardsFlat flat_baseEnv
    | _, (q', (Some x, Nmove)) => makeSomeStay q q' (fOpt m) (fOpt $ Some x) makeCardsFlat flat_baseEnv
    | Some x, (q', (None, Lmove)) => makeSomeRight q q' (fOpt $ Some x) (fOpt $ Some x) makeCardsFlat flat_baseEnv
    | Some x, (q', (None, Rmove)) => makeSomeLeft q q' (fOpt $ Some x) (fOpt $ Some x) makeCardsFlat flat_baseEnv
    | Some x, (q', (None, Nmove)) => makeSomeStay q q' (fOpt $ Some x) (fOpt $ Some x) makeCardsFlat flat_baseEnv
    | None, (q', (None, Lmove)) => makeNoneRight q q' makeCardsFlat flat_baseEnvNone
    | None, (q', (None, Rmove)) => makeNoneLeft q q' makeCardsFlat flat_baseEnvNone
    | None, (q', (None, Nmove)) => makeNoneStay q q' makeCardsFlat flat_baseEnvNone
    end.

  (** given a state, generate the cards needed for halting states *)
  Definition generateCardsForFlatHalt (q : nat) := makeHalt q makeCardsFlat flat_baseEnvHalt. 

  (** we need to use the Boolean version of lookup for it to be extractable *)
  Import Undecidability.L.Functions.FinTypeLookup Undecidability.L.Functions.EqBool.
  Definition inp_eqb := LProd.prod_eqb Nat.eqb (List_eqb.list_eqb (LOptions.option_eqb Nat.eqb)).
  Instance eqBool_inp_eqb : eqbClass inp_eqb. 
  Proof. 
    apply LProd.eqbProd. 
    - apply LNat.eqbNat_inst. 
    - apply List_eqb.eqbList. apply LOptions.eqbOption. apply LNat.eqbNat_inst. 
  Qed. 

  (** generate cards for all states*)
  Definition generateCardsForFlatNonHalt (q : nat) (m : option nat) : (list (card nat)) :=
    match lookup (q, [m]) flatTrans (q, [(None, Nmove)]) with 
      | (q', [succ]) => opt_generateCardsForFlatNonHalt q m (q', succ)
      | _ => []
    end. 

  (**given a state, generate either transition cards or halting cards for it *)
  Definition generateCardsForFlat (q : nat) :=
    if nth q flatHalt false then generateCardsForFlatHalt q else
      generateCardsForFlatNonHalt q None ++ concat (map (fun (m : nat) => generateCardsForFlatNonHalt q (Some m)) (seq 0 flatSigma)).

  Definition flatStateCards := concat (map generateCardsForFlat (seq 0 flatstates)).  

  (** agreement with finType cards *)
  Lemma envAddState_isFlatEnvOf a' finEnv flatEnv a : 
    finReprEl' a a' -> isFlatEnvOf flatEnv finEnv -> isFlatEnvOf (envAddState a flatEnv) (envAddState a' finEnv). 
  Proof using flatTM_TM_compat. 
    intros. destruct flatEnv, finEnv. unfold envAddState. cbn. unfold isFlatEnvOf in *; cbn in *.
    unfold finReprEl' in H. repeat split; try easy. 
    unfold isFlatListOf in *. rewrite <- H. cbn.  firstorder congruence. 
  Qed. 

  Lemma envAddSSigma_isFlatEnvOf finEnv flatEnv a a' : 
    opt_finReprEl' a a' -> isFlatEnvOf flatEnv finEnv -> isFlatEnvOf (envAddSSigma (fOpt a) flatEnv) (envAddSSigma a' finEnv). 
  Proof using flatTM_TM_compat. 
    intros. destruct flatEnv, finEnv. unfold envAddSSigma. cbn. unfold isFlatEnvOf in *; cbn in *.
    unfold opt_finReprEl' in H. repeat split; try easy. 
    unfold isFlatListOf in *. rewrite H. destruct a'; cbn [option_map map]; 
    cbn [fOpt index]. 
    - cbn. rewrite getPosition_map; [ | unfold injective; intros; now apply Some_injective]. f_equal;firstorder. 
    - unfold index. cbn. f_equal;firstorder. 
  Qed. 

  Lemma list_isFlatEnvOf_map flatL finL f1 f2: 
    list_isFlatEnvOf flatL finL -> (forall flatEnv finEnv, isFlatEnvOf flatEnv finEnv -> isFlatEnvOf (f1 flatEnv) (f2 finEnv)) 
    -> list_isFlatEnvOf (map f1 flatL) (map f2 finL). 
  Proof. 
    intros. unfold list_isFlatEnvOf. split; intros ? H1%in_map_iff. 
    - destruct H1 as (env & <- & (envFin & H2 & H3)%H). 
      exists (f2 envFin). split; [ now apply H0 | apply in_map_iff; eauto]. 
    - destruct H1 as (env & <- & (envFlat & H2 & H3)%H). 
      exists (f1 envFlat). split; [ now apply H0 | apply in_map_iff; eauto]. 
  Qed. 

  (** applies to goals of the form list_isFlatEnvOf (map (_ q q) flat_baseEnvHalt) ?finenv *)
  Ltac fin_flat_find_env := 
    eapply list_isFlatEnvOf_map; [apply makeAllEvalEnv_isFlatEnvOf' | ]; 
    intros; 
    repeat match goal with 
      | [ |- isFlatEnvOf (envAddSSigma _ _) _ ] => apply envAddSSigma_isFlatEnvOf
      | [ |- isFlatEnvOf (envAddState _ _) _] => apply envAddState_isFlatEnvOf
      | [ |- finReprEl' (index _) _ ] => reflexivity 
      | [ |- opt_finReprEl' (Some _) _] => apply opt_finReprElP_Some
      | [ |- opt_finReprEl' None _] => apply opt_finReprElP_None
    end; try easy.

  (** the corresponding tactic for the other direction *)
  Ltac flat_fin_find_env := 
    eapply list_isFlatEnvOf_map; [apply makeAllEvalEnv_isFlatEnvOf' | ];
    intros; 
    repeat match goal with 
      | [ |- isFlatEnvOf _ (envAddSSigma _ _) ] => apply envAddSSigma_isFlatEnvOf
      | [ |- isFlatEnvOf _ (envAddState _ _)] => apply envAddState_isFlatEnvOf
    end; try easy.

  (** those nice little singleton vectors have to go :) sorry *)
  Ltac destruct_vec1 := repeat match goal with [v : Vector.t _ 1 |- _] => specialize (vec_case1 v) as (? & ->) end. 

  Lemma fin_flat_nonhaltCards_agree q qflat m mflat : 
    finReprEl' qflat q -> opt_finReprEl' mflat m 
    -> isFlatTCardsOf (generateCardsForFlatNonHalt qflat mflat) (generateCardsForFinNonHalt q m). 
  Proof using flatTM_TM_compat. 
    destruct flatTM_TM_compat as [_  _  _  R  _  _]. 
    specialize (TMunflatten.isFlatteningTrans_validFlatTrans R) as [trans_funct _].
    destruct R as [R1 R2].
    intros. split; intros. 
    - unfold generateCardsForFlatNonHalt in H1. 
      destruct (lookup_complete flatTrans (qflat, [mflat]) (qflat, [(|_|, neutral)])) as [H2 | H2]. 
      + destruct lookup. apply R1 in H2 as (? & ? & x1 & x2 & F1 & F2 & F3 & F4 & F5); destruct_vec1. 
        subst. cbn in H1, F4. inv F4. destruct x3 as [[m' | ] mo];
        unfold opt_generateCardsForFlatNonHalt in H1; destruct x2 as [mflat | ], mo;
        apply opt_finReprElP_case in H0; try destruct H0 as (? & -> & H0); cbn in H0; subst; cbn [map_fst option_map] in H1. 
        all: eapply makeCards_isFlatCardOf in H1 as (fincard & H1 & H2); [ | unfold transEnvAddSM, transEnvAddS;  fin_flat_find_env];
        (exists fincard; split; [ | apply H2]);
        repeat match goal with [ H : finReprEl' (index _) _ |- _] => apply injective_index in H as -> end.
        all: unfold generateCardsForFinNonHalt, trans; rewrite F1; cbn [Vector.nth Vector.caseS]; try apply H1.
      + (*the case for the default value *)
        destruct lookup. destruct H2 as (H2 & H2'). inv H2'. clear R1. 
        unfold opt_generateCardsForFlatNonHalt in H1. 
        specialize (R2 q [|m|]). 
        destruct mflat as [mflat | ];
        apply opt_finReprElP_case in H0; try destruct H0 as (? & -> & H0); subst;
        (eapply makeCards_isFlatCardOf in H1 as (fincard & H1 & H3); [  | unfold transEnvAddSM, transEnvAddS;  fin_flat_find_env]);
        exists fincard; (split; [ | apply H3]). 
        all: unfold generateCardsForFinNonHalt, trans;
        destruct TM.trans; destruct_vec1.
        all: cbn in R2; unfold finReprEl' in *; (destruct R2 as [R2 | R2]; [exfalso; apply H2; rewrite H in R2; try rewrite H0 in R2; eauto | ]). 
        all: destruct R2 as [R2 R2']; inv R2; inv R2'; cbn [Vector.nth Vector.caseS]; apply H1. 
    - unfold generateCardsForFinNonHalt in H1. 
      destruct m as [m | ]; destruct trans eqn:H2; unfold trans in H2; destruct TM.trans eqn:H4; destruct_vec1; inv H2; 
      destruct p as [[m' | ] []];
      unfold opt_finReprEl', finReprEl' in *; cbn in H0; subst.
      all: eapply makeCards_isFlatCardOf in H1 as (flatcard & H1 & H3); [ | unfold transEnvAddSM, transEnvAddS; flat_fin_find_env ];
        exists flatcard; (split; [ | apply H3]).
      all: match type of H4 with TM.trans (?q, ?m) = (?q', ?a) => specialize (R2 q m) end; rewrite H4 in R2; cbn in R2. 
      all: destruct R2 as [R2 | [-> R2]]; [ | inv R2]. 
      all: try ( eapply (lookup_sound (L := flatTrans)) in R2; [ | apply trans_funct]; 
        unfold generateCardsForFlatNonHalt; rewrite R2; 
        unfold opt_generateCardsForFlatNonHalt; apply H1). 
      (*two cases remain which are due to the default semantics *)
      (*if a transition for the current configuration is contained in flatTrans, it will have to match the default one because of R1 *)
      all: unfold generateCardsForFlatNonHalt. 
      all: match type of H4 with TM.trans (?q, [|?m|]) = _ => 
      destruct (lookup_complete flatTrans (index q, [option_map index m]) (index q, [(None, neutral)])) as [H5 | [ _ H5]] end; cbn in H5. 
      1,3: destruct lookup eqn:H6; apply R1 in H5 as (? & ? & x1 & x2 & H5 & ? & ? & ? & ?);  
        destruct_vec1; subst; 
        repeat match goal with 
        | [x : option _ |- _] => destruct x
        | [H : index ?a = index ?b |- _] => apply injective_index in H as ->
        | [H : Some _ :: nil = _ |- _] => inv H
        | [H : _ = Some _ :: nil |- _] => inv H
        | [H : TM.trans ?a = _ , H1 : TM.trans ?a = _ |- _] => rewrite H1 in H; inv H
        | [H : _ |- _] => cbn in H
        end; apply H1. 
    1, 2: rewrite H5; apply H1.  
  Qed.  

  Lemma fin_flat_haltCards_agree q qflat : 
    finReprEl' qflat q  
    -> isFlatTCardsOf (generateCardsForFlatHalt qflat) (generateCardsForFinHalt q). 
  Proof using flatTM_TM_compat. 
    intros; split; intros. 
    - unfold generateCardsForFlatHalt in H0. 
      eapply makeCards_isFlatCardOf in H0 as (fincard & H1 & H2); [ | unfold transEnvAddS; fin_flat_find_env].
      exists fincard. split; [ | apply H2]. apply H1. 
    - unfold generateCardsForFinHalt in H0. 
      eapply makeCards_isFlatCardOf in H0 as (flatcard & H1 & H2); [ | unfold transEnvAddS; flat_fin_find_env]. 
      exists flatcard; split; [ | apply H2]. rewrite H in H1. apply H1. 
  Qed. 

  Lemma fin_flat_stateCards_agree : isFlatTCardsOf flatStateCards finStateCards.
  Proof using flatTM_TM_compat. 
    destruct flatTM_TM_compat as [_  _  _  _  _ []]. 
    split; intros. 
    - unfold flatStateCards in H. apply in_concat_map_iff in H as (q & H1 & H2). 
      apply in_seq in H1 as (_ & H1). cbn in H1. rewrite (states_finRepr) in H1. apply finReprElP_exists in H1 as (Q & H1).
      unfold generateCardsForFlat in H2. destruct nth eqn:H3; rewrite <- H1, R__halt in H3. 
      + eapply fin_flat_haltCards_agree in H2 as (fincard & H2 & H4); [ | apply H1]. 
        exists fincard. split; [ | eapply H4]. 
        unfold finStateCards. apply in_concat_map_iff. exists Q; split; [apply elem_spec | ]. 
        unfold generateCardsForFin. rewrite H3. apply H2. 
      + apply in_app_iff in H2. destruct_or H2; [ | apply in_concat_iff in H2 as (l' & H2 & H4); apply in_map_iff in H4 as (m & <- & H5)]. 
        * eapply fin_flat_nonhaltCards_agree in H2 as (fincard & H2 & H4); [ | apply H1 | apply opt_finReprElP_None]. 
          exists fincard. split; [ | apply H4]. 
          unfold finStateCards. apply in_concat_map_iff. exists Q; split; [apply elem_spec | ]. 
          unfold generateCardsForFin. rewrite H3. 
          apply in_concat_map_iff. exists None; split; [ apply elem_spec | ]. apply H2. 
        * apply in_seq in H5 as (_ & H5). cbn in H5. rewrite (Sigma_finRepr) in H5. apply finReprElP_exists in H5 as (M & H5). 
          eapply fin_flat_nonhaltCards_agree in H2 as (fincard & H2 & H4); [ | apply H1 | apply opt_finReprElP_Some; eauto]. 
          exists fincard. split; [ | apply H4]. 
          unfold finStateCards. apply in_concat_map_iff. exists Q; split; [apply elem_spec | ]. 
          unfold generateCardsForFin. rewrite H3. 
          apply in_concat_map_iff. exists (Some M); split; [ apply elem_spec | ]. apply H2. 
    - unfold finStateCards in H. apply in_concat_map_iff in H as (q & _ & H2). 
      unfold generateCardsForFin in H2. destruct halt eqn:H3; rewrite <- R__halt in H3.  
      + eapply fin_flat_haltCards_agree in H2 as (flatcard & H2 & H4); [ | reflexivity].   
        exists flatcard; split; [ | apply H4]. 
        unfold flatStateCards. apply in_concat_map_iff. exists (index q). 
        split; [ rewrite states_finRepr; apply in_seq; cbn; split; [lia | apply index_le] | ]. 
        unfold generateCardsForFlat. rewrite H3. apply H2. 
      + apply in_concat_map_iff in H2 as (m & _ & H2). 
        destruct m as [m | ]; 
        (eapply fin_flat_nonhaltCards_agree in H2 as (flatcard & H2 & H4); [ | reflexivity | ]).
        2: now apply opt_finReprElP_Some. 
        3: now apply opt_finReprElP_None. 
        * exists flatcard. split; [ | apply H4]. 
          unfold flatStateCards. apply in_concat_map_iff. exists (index q). 
          split; [ rewrite states_finRepr; apply in_seq; cbn; split; [lia | apply index_le] | ]. 
          unfold generateCardsForFlat. rewrite H3. apply in_app_iff. 
          right; apply in_concat_iff.
          exists (generateCardsForFlatNonHalt (index q) (Some (index m))).
          split; [apply H2 | ]. apply in_map_iff. exists (index m). split; [easy | ]. 
          apply in_seq; rewrite Sigma_finRepr; cbn; split; [lia | apply index_le]. 
        * exists flatcard. split; [ | apply H4]. 
          unfold flatStateCards. apply in_concat_map_iff. exists (index q). 
          split; [ rewrite states_finRepr; apply in_seq; cbn; split; [lia | apply index_le] | ]. 
          unfold generateCardsForFlat. rewrite H3. apply in_app_iff. 
          now left. 
  Qed.  

  Definition allFlatSimCards := flatTapeCards ++ flatStateCards.

  (** prelude cards *)
  Definition flat_baseEnvPrelude := makeAllEvalEnvFlat 0 3 1 0. 
  Definition flatPreludeCards := makePreludeCards flatStart makeCardsFlat flat_baseEnvPrelude.

  Lemma fin_flat_preludeCards_agree : isFlatTCardsOf flatPreludeCards finPreludeCards.
  Proof using flatTM_TM_compat. 
    split. 
    - intros. 
      destruct flatTM_TM_compat. 
      eapply makeCards_isFlatCardOf in H as (card & H1 & H2).
      2: { fin_flat_find_env. rewrite eq__start. reflexivity. }
      exists card. split; [ | easy]. easy.
    - intros. destruct flatTM_TM_compat. 
      eapply makeCards_isFlatCardOf in H as (card' & H1 & H2).
      2: { flat_fin_find_env. }
      exists card'. split; [ | easy].
      rewrite <- eq__start in H1. easy.
  Qed. 

  Definition allFlatCards := flatPreludeCards ++ allFlatSimCards. 

  Lemma fin_flat_cards_agree : isFlatTCardsOf allFlatCards allFinCards. 
  Proof using flatTM_TM_compat. 
    unfold allFlatCards, allFinCards. apply isFlatTCardsOf_concat. 
    - apply fin_flat_preludeCards_agree. 
    - unfold allFlatSimCards, allFinSimCards. apply isFlatTCardsOf_concat. 
      + apply fin_flat_tapeCards_agree. 
      + apply fin_flat_stateCards_agree. 
  Qed. 

  (*now we can derive the full reduction *)

  Lemma isFlatListOf_single (X : finType) a (A : X) : finReprEl' a A -> isFlatListOf [a] [A]. 
  Proof. 
    intros. unfold isFlatListOf. cbn. now rewrite <- H. 
  Qed. 

  Lemma ndelimC_finReprEl : finReprEl flatPreludeSig' flatNdelimC ndelimC. 
  Proof using flatTM_TM_compat. 
    split; [ now finRepr_simpl | cbn]. unfold flatNdelimC, flatPreludeSig'. easy.
  Qed. 
  Smpl Add (apply ndelimC_finReprEl) : finRepr.
  Lemma nstar_finReprEl : finReprEl flatPreludeSig' flatNstar nstar. 
  Proof using flatTM_TM_compat. 
    split; [ now finRepr_simpl | cbn]. unfold flatNstar, flatPreludeSig'. easy.
  Qed. 
  Smpl Add (apply nstar_finReprEl) : finRepr. 
  Lemma nblank_finReprEl : finReprEl flatPreludeSig' flatNblank nblank.
  Proof using flatTM_TM_compat. 
    split; [ now finRepr_simpl | cbn]. unfold flatNblank, flatPreludeSig'. easy.
  Qed. 
  Smpl Add (apply nblank_finReprEl) : finRepr. 
  Lemma ninit_finReprEl : finReprEl flatPreludeSig' flatNinit ninit.
  Proof using flatTM_TM_compat. 
    split; [ now finRepr_simpl | cbn]. unfold flatNinit, flatPreludeSig'. easy.
  Qed. 
  Smpl Add (apply ninit_finReprEl) : finRepr. 

  Smpl Add (eapply finReprEl_finReprEl') : finRepr.

  Lemma isFlatListOf_rev (X : finType) (A : list X) a: isFlatListOf a A -> isFlatListOf (rev a) (rev A).
  Proof. 
    revert A. induction a; intros. 
    - destruct A; [easy | unfold isFlatListOf in H; cbn in H; congruence].
    - destruct A; [ unfold isFlatListOf in H; cbn in H; congruence | ].
      apply isFlatListOf_cons in H as (H1 & H2). cbn. 
      apply isFlatListOf_app; [now apply IHa | ].
      now apply isFlatListOf_single.
  Qed. 

  (**We define the flattened initial string *)
  (** We need to define k, z' in terms of the flat fixed input, otherwise Coq's generalisation pulls in fixedInput and Sigma as arguments of the reduction*)
  Definition kflat := k' + |flatFixedInput|.
  Definition zflat := t + kflat.
  Definition zPflat := wo + zflat. 

  Fact kflat_k_eq : kflat = k. 
  Proof using flatFixedInput_compat. unfold kflat, k. rewrite flatFixedInput_compat, map_length; easy. Qed.  
  Fact zflat_z_eq : zflat = z. 
  Proof using flatFixedInput_compat. unfold zflat, z. now rewrite kflat_k_eq. Qed. 
  Fact zPflat_zP_eq : zPflat = z'. 
  Proof using flatFixedInput_compat. unfold zPflat, z'. now rewrite zflat_z_eq. Qed. 

  Definition flat_initial_string := [flatInr flatGamma flatNdelimC ] ++ rev (repEl zPflat (flatInr flatGamma flatNblank)) ++ [flatInr flatGamma flatNinit] ++ map (fun n => flatInr flatGamma (flatNsig n)) flatFixedInput ++ repEl k' (flatInr flatGamma flatNstar) ++ repEl (wo + t) (flatInr flatGamma flatNblank) ++ [flatInr flatGamma flatNdelimC]. 
  Lemma flat_initial : isFlatListOf flat_initial_string (map (inr (A := Gamma)) preludeInitialString). 
  Proof using Type*. 
    rewrite lifted_preludeInitialString. unfold flat_initial_string. 
    repeat match goal with [ |- isFlatListOf (_ ++ _) (_ ++ _) ] => apply isFlatListOf_app end. 
    - apply isFlatListOf_single. now finRepr_simpl. 
    - rewrite zPflat_zP_eq. apply isFlatListOf_rev, repEl_isFlatListOf. now finRepr_simpl.
    - apply isFlatListOf_single. now finRepr_simpl. 
    - rewrite flatFixedInput_compat. clear flatFixedInput_compat. induction fixedInput.  
      + easy.
      + cbn [map]. apply isFlatListOf_cons. split; [finRepr_simpl; [easy | split; [finRepr_simpl | reflexivity ] ] | ].
        apply IHl0.
    - apply repEl_isFlatListOf. now finRepr_simpl.
    - apply repEl_isFlatListOf. now finRepr_simpl.
    - apply isFlatListOf_single; now finRepr_simpl. 
  Qed. 

  Import FlatCC. 
  (*flattened final substrings *)
  Definition flat_haltingStates := filter (fun n => nth n flatHalt false) (seq 0 flatstates). 

  Lemma in_flat_haltingStates_iff s : s el flat_haltingStates <-> exists q, s = index q /\ halt q = true. 
  Proof using flatTM_TM_compat. 
    unfold flat_haltingStates. rewrite in_filter_iff. split; intros. 
    - destruct H as (H1 & H2).
      rewrite states_finRepr in H1. apply finType_enum_list_finReprEl in H1 as (q & H1 & H3). 
      exists q. destruct H1 as (_ &<-). split; [easy | ].
      destruct flatTM_TM_compat. destruct R__halt. rewrite <- R__halt. easy.
    - destruct H as (q & -> & H). split. 
      + apply in_seq. cbn; split; [ lia | ]. rewrite states_finRepr. apply index_le. 
      + destruct flatTM_TM_compat. destruct R__halt. rewrite R__halt. easy.
  Qed. 

  Definition flat_finalSubstrings : list (list nat) := map (fun pr => match pr with (s, m) => [flatInl $ flatInl (flatPair flatstates flatStateSigma s m)] end) (prodLists flat_haltingStates (seq 0 flatStateSigma)). 

  Smpl Add (reflexivity) : finRepr. 

  Lemma finReprElP_finReprEl (X: finType) (A : X) a x: finRepr X x -> finReprEl' a A -> finReprEl x a A.
  Proof. 
    intros. split. 
    - apply H. 
    - apply H0.
  Qed. 

  Lemma in_finalSubstrings_iff l : l el finalSubstrings <-> exists q m, l = [inl (q, m)] /\ halt q = true.
  Proof. 
    unfold finalSubstrings. rewrite in_map_iff. split; intros. 
    - destruct H as ((q & m) & <- & H). exists q, m. split; [easy | ].
      apply in_prodLists_iff in H as (H & _). unfold haltingStates in H. apply in_filter_iff in H. easy.
    - destruct H as (q & m & -> & H). exists (q, m). split; [easy | apply in_prodLists_iff].
      split; [ apply in_filter_iff | apply elem_spec]. easy.
  Qed. 
  
  Lemma flat_final : isFlatFinalOf flat_finalSubstrings (map (map inl) finalSubstrings). 
  Proof using flatTM_TM_compat. 
    split; intros. 
    - unfold flat_finalSubstrings in H. apply in_map_iff in H as ([s m] & <- & H2). 
      apply in_prodLists_iff in H2 as (H2 & H3). 
      apply in_flat_haltingStates_iff in H2 as (q & -> & H2).
      apply in_seq in H3 as (_ & H3). cbn in H3. 
      rewrite stateSigma_finRepr in H3.
      apply finReprElP_exists in H3 as (m1 & H3).
      exists [inl $ inl (q, m1)]. 
      split. 
      + apply in_map_iff. exists [inl (q, m1)]. split; [easy | ].
        apply in_finalSubstrings_iff. exists q, m1; easy.
      + apply isFlatListOf_single. rewrite <- H3. 
        finRepr_simpl; try easy; (apply finReprElP_finReprEl; [finRepr_simpl | try reflexivity]). 
    - apply in_map_iff in H as (fin' & <- & H1).
      apply in_finalSubstrings_iff in H1 as (q & m & -> & H1).
      exists [flatInl $ flatInl $ flatPair flatstates flatStateSigma (index q) (index m)]. 
      split. 
      + apply in_map_iff. exists (index q, index m).
        split; [easy | apply in_prodLists_iff]. split. 
        * apply in_flat_haltingStates_iff. easy.
        * apply in_seq; split; [lia | rewrite stateSigma_finRepr; apply index_le].
      + apply isFlatListOf_single. finRepr_simpl; try easy; (apply finReprElP_finReprEl; [finRepr_simpl | try reflexivity]).
  Qed. 

  Definition reduction_wf := Build_FlatTCC flatAlphabet flat_initial_string allFlatCards flat_finalSubstrings (S t). 

  Lemma reduction_isFlatTCCOf : isFlatTCCOf (Build_FlatTCC flatAlphabet flat_initial_string allFlatCards flat_finalSubstrings (S t)) (Build_TCC (map inr preludeInitialString) allFinCards (map (map inl) finalSubstrings) (S t)). 
  Proof using Type*. 
    constructor. 
    - cbn [TCC.Sigma FlatTCC.Sigma]. now finRepr_simpl.
    - cbn [TCC.init FlatTCC.init]. apply flat_initial.
    - cbn [TCC.cards FlatTCC.cards]. apply fin_flat_cards_agree. 
    - cbn [TCC.final FlatTCC.final]. apply flat_final.
    - easy.
  Qed. 

  Lemma reduction_wf_correct : 
    SingleTMGenNP (existT _ Sigma (fTM, fixedInput, k', t)) <-> FlatTCCLang reduction_wf.
  Proof using Type*. 
    rewrite <- SingleTMGenNP_to_TCC. symmetry. eapply isFlatTCCOf_equivalence, reduction_isFlatTCCOf.
  Qed. 

End fixTM. 

(**for the reduction, we check if the input TM is a valid flat TM. *)
(**if it isn't, we return a trivial no-instance of CC *)

Definition trivial_no_instance := Build_FlatTCC 0 [] [] [] 0. 
Lemma trivial_no_instance_is_no : not (FlatTCCLang trivial_no_instance). 
Proof. 
  intros (H1 &_). unfold FlatTCC_wellformed in H1. cbn in H1. lia. 
Qed. 

Import TMunflatten.
Definition reduction (fg : TMflat.flatTM * list nat * nat * nat) := 
  match fg with (tm, fixedInput, k', t) => if isValidFlatTM tm && (TMflat.tapes tm =? 1) && list_ofFlatType_dec (TMflat.sig tm) fixedInput then reduction_wf t k' tm fixedInput 
                                                  else trivial_no_instance
  end.

Lemma unflatten_single (tm : TMflat.flatTM) : validFlatTM tm -> TMflat.tapes tm = 1 -> sigT (fun (TM' : TM (finType_CS (Fin.t (TMflat.sig tm))) 1) => TMflat.isFlatteningTMOf tm TM').
Proof. 
  intros. rewrite <- H0. 
  exists (unflattenTM tm).
  apply unflattenTM_correct, H. 
Defined. 

Lemma FlatSingleTMGenNP_to_FlatTCC (f : TMflat.flatTM * list nat * nat * nat) : FlatSingleTMGenNP f <-> FlatTCCLang (reduction f). 
Proof. 
  split; intros. 
  - destruct f as (((tm & flatFixedInput) & k) & t). destruct H as (sig & M' & fixedInput & H1 & H2 & H3).
    specialize (isFlattening_is_valid H1) as H1'. 
    unfold reduction. specialize (isValidFlatTM_spec tm) as H4.
    apply reflect_iff in H4. apply H4 in H1'. rewrite H1'. 
    assert (TMflat.tapes tm = 1) as ->. 
    { destruct H1 as [-> _ _ _ _ _]. easy. }
    rewrite (proj2 (list_ofFlatType_dec_correct _ _)). 
    2: { apply isFlatListOf_list_ofFlatType in H2. destruct H1 as [_  eq_sig  _  _  _  _]. 
      rewrite eq_sig. apply H2. }
    eapply reduction_wf_correct.
    + apply H1. 
    + apply H2. 
    + apply H3. 
  - (*for the other direction, we check if the TM is a valid flattening *)
    (*if it is, there exists some unflattened Turing machine, to which we then apply the non-flat reduction *)
    (*the resulting TCC instance is a yes instance iff the FlatCC instance is a yes instance *)
    unfold reduction in H. destruct f as (((tm & flatFixedInput) & k) & t).
    specialize (isValidFlatTM_spec tm) as H2. apply reflect_iff in H2. 
    destruct isValidFlatTM.
    + destruct (Nat.eqb (TMflat.tapes tm) 1) eqn:H3. 
      * destruct (list_ofFlatType_dec) eqn:H4.
        -- apply Nat.eqb_eq in H3. apply list_ofFlatType_dec_correct in H4. 
           unfold FlatSingleTMGenNP.
            assert (validFlatTM tm) as H1 by easy. clear H2. 
            specialize (unflatten_single H1 H3) as (TM' & H5). 
            exists (finType_CS(Fin.t (TMflat.sig tm))), TM'.
            apply unflattenString in H4 as (fixedInput & H4).
            exists fixedInput. 
            split; [apply H5 | split; [apply H4 | ]]. 
            eapply SingleTMGenNP_to_TCC.
            eapply isFlatTCCOf_equivalence. 1: apply reduction_isFlatTCCOf; [apply H5 | apply H4]. 
            cbn in H.  
            apply H. 
        -- cbn in H. now apply trivial_no_instance_is_no in H. 
      * cbn in H. now apply trivial_no_instance_is_no in H. 
    + cbn in H. now apply trivial_no_instance_is_no in H. 
Qed. 
(* theories/L/Complexity/Reductions/Cook/SingleTMGenNP_to_TCC.vo (real: 250.80, user: 247.10, sys: 5.64, mem: 2440784 ko) *)