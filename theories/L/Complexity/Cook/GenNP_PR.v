(* -*- company-coq-local-symbols: (("|_|" .?␣)); -*- *)
From Undecidability.L.Complexity Require Import Cook.GenNP Cook.TCSR Cook.Prelim FlatFinTypes.
From PslBase Require Import FiniteTypes. 
From Undecidability.TM Require Import TM.
Require Import Lia. 
Require Import PslBase.FiniteTypes.BasicDefinitions. 
Require Import PslBase.FiniteTypes.FinTypes.

Section TM_single. 
  (*we use a variant of the Turing machine definitions fixed to a single tape *)

  Variable (mstates : finType).
  Variable (Sigma : finType).
  Variable (mtrans : (mstates * Vector.t (option Sigma) 1) -> (mstates * Vector.t (option Sigma * move) 1)). 
  Variable (start : eqType_X mstates). 
  Variable (halt : mstates -> bool). 

  Definition strans (a : mstates * option Sigma) : (mstates * (option Sigma * move)) :=
    let (q, t) := a in let (q', ac) := mtrans (q, [| t |]) in (q', Vector.nth ac Fin.F1). 
                                                                                            
  Definition sconfig := (mstates * tape Sigma)%type. (* single-tape configuration*)
  Implicit Type (c : sconfig). 
  Definition sstep  (trans : mstates * option Sigma -> mstates * (option Sigma * move)) (c : sconfig): sconfig := let (q, tp) := c in let (q', act) := trans (q, current tp) in (q', doAct tp act).

  Definition mconfig_for_sconfig c := let (q, tp) := c in mk_mconfig q [| tp |].
  Definition sconfig_for_mconfig (c : mconfig Sigma mstates 1) := let (q, tps) := c in (q, Vector.nth tps Fin.F1).

  Local Notation TM := (@Build_mTM Sigma 1 mstates mtrans start halt).
  Lemma sstep_agree1 c : sconfig_for_mconfig (@step Sigma 1 TM (mconfig_for_sconfig c)) = sstep strans c.
  Proof. 
    destruct c. cbn.
    destruct mtrans eqn:H1. unfold sconfig_for_mconfig.
    unfold step. unfold doAct_multi. cbn. unfold current_chars. cbn. setoid_rewrite H1. 
    eapply Vector.caseS with (n := 0). 
    2 : apply t0.
    intros.
    erewrite Vector.nth_map2 with (p2 := Fin0) (p3 := Fin0). 2-3: reflexivity. cbn. reflexivity.  
  Qed. 

  Lemma sstep_agree2 (c : mconfig Sigma mstates 1) : mconfig_for_sconfig (sstep strans (sconfig_for_mconfig c)) = step (c : mconfig Sigma (states TM) 1).  
  Proof.
    destruct c. cbn. unfold step. cbn. unfold current_chars.
    assert ([| current ctapes[@Fin0]|] = Vector.map (current (sig := Sigma)) ctapes). 
    {
      apply VectorDef.caseS' with (v := ctapes). intros. apply VectorDef.case0 with (v := t). cbn. reflexivity. 
    }
    rewrite H. destruct mtrans eqn:H1. 
    cbn. 
    apply VectorDef.caseS' with (v := t). 
    intros. 
    apply VectorDef.case0 with (v := t0). cbn. 
    apply VectorDef.caseS' with (v := ctapes). 
    intros. 
    apply VectorDef.case0 with (v := t1). cbn. reflexivity. 
 Qed. 
End TM_single.

Section fixTM. 
  Variable (Sigma : finType).
  Variable (TM : mTM Sigma 1).

  Notation states := (states TM).  
  Notation trans := (strans (@trans Sigma 1 TM)). 
  Notation start := (start TM). 
  Notation halt := (@halt Sigma 1 TM). 

  Variable (t : nat).
  Variable (k : nat). 

  Notation sconfig := (sconfig states Sigma). 
  Implicit Type (c : sconfig). 
  Notation sstep := (sstep trans). 
  
  Definition z' := t + k. (*effectively available space on each tape side *)
  Definition wo := 2.     (*additional space for each side in order to make proofs more convenient *)
  Definition z := wo + z'. (*length of each tape side *)
  Definition l := 2 * (z + 1) + 1. (*length of the whole string: two tape sides and the state symbol*)

  Hint Unfold z z' l. 

  Hint Constructors move.
  Notation polarity := move. 
  Notation positive := R. 
  Notation negative := L. 
  Notation neutral := N. 

  Implicit Type σ : Sigma. 

  Notation "'↓' σ" := ((negative, σ)) (at level 30). 
  Notation "'↑' σ" := ((positive, σ)) (at level 10).
  Notation "'∘' σ" := ((neutral, σ)) (at level 30). 

  Inductive delim := delimC. 
  Hint Constructors delim.
  Instance delim_eqTypeC : eq_dec delim.
  Proof. unfold dec. decide equality. Defined. 

  Instance delim_finTypeC : finTypeC (EqType delim). 
  Proof. exists [delimC]. intros []. simpl. dec; congruence. Defined. 

  Notation "#" := (inl delimC). 

  Notation stateSigma := (option Sigma). 
  Notation polSigma := ((polarity * stateSigma)%type).
  Notation tapeSigma := (sum delim polSigma).
  Notation States := ((states * stateSigma)%type). 
  Notation Gamma := ((States + tapeSigma)%type). 
 

  Implicit Type (γ : Gamma).
  Implicit Type (q : states).
  Implicit Type (m : stateSigma).
  Implicit Type (p : polarity).


  Notation "'|_|'" := (None). 

  (*flip the polarity of a symbol *)
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
    intros x. destruct x; [ destruct d; now cbn | ]. destruct p; cbn. now rewrite polarityFlip_involution. 
  Qed. 
  Lemma polarityFlipGamma_involution : involution polarityFlipGamma. 
  Proof. 
    intros x. destruct x; [now cbn | ]. cbn. now rewrite polarityFlipTapeSigma_involution.  
  Qed. 

  Notation "'~' x" := (polarityFlipGamma x). 
  Notation "'!' x" := (polarityFlipSigma x) (at level 1). 
  Notation "'%' x" := (polarityFlipTapeSigma x) (at level 30).

  Smpl Add (apply polarityFlipTapeSigma_involution) : involution.
  Smpl Add (apply polarityFlipGamma_involution) : involution.
  
  Lemma polarityFlipSigmaInv1 e p m : polarityFlipSigma e = (p, m) -> e = (polarityFlip p, m). 
  Proof. 
    unfold polarityFlipSigma. destruct e as [p' e]. intros. inv H. specialize (polarityFlip_involution p'). congruence. 
  Qed. 

  Lemma polarityFlipTapeSigmaInv1 e p m : polarityFlipTapeSigma e = inr (p, m) -> e = inr (polarityFlip p, m). 
  Proof.
    intros. destruct e; cbn in H; [destruct d; congruence | ].
    inv H. now apply polarityFlipSigmaInv1 in H1. 
  Qed. 

  Lemma polarityFlipGammaInv1 e p m : polarityFlipGamma e = inr (inr (p, m)) -> e = inr (inr (polarityFlip p, m)). 
  Proof. 
    intros. destruct e; cbn in H; [ congruence | ]. 
    inv H. now apply polarityFlipTapeSigmaInv1 in H1.
  Qed. 

  (*reverse a string + flip its polarities *)
  Definition polarityRev (x : list Gamma) : list Gamma := rev (map polarityFlipGamma x).

  Lemma polarityRev_involution : involution polarityRev.
  Proof. 
    intros x. unfold polarityRev. rewrite map_rev, rev_involutive, map_map. setoid_rewrite polarityFlipGamma_involution. 
    induction x; [eauto | cbn [map]; now rewrite IHx]. 
  Qed. 

  Smpl Add (apply polarityRev_involution) : involution. 

  Lemma polarityRev_eqn_move a b : a = polarityRev b -> b = polarityRev a. 
  Proof. intros ->; symmetry. involution_simpl. Qed. 


  (** *representation of tapes *)
  Notation stape := (list Sigma). 

  Notation halftape := (list Gamma).

  (*a string consisting of k blanks*)
  Fixpoint E p k : halftape := match k with 0 => [inr #] | S k => inr (inr (p, |_|)) :: E p k end. 
  Lemma E_length p n: |(E p n)| = S n. 
  Proof. 
    induction n; cbn.
    - reflexivity.  
    - rewrite <- IHn at 1. reflexivity.  (*slightly hacky because of typeclass inference *)
  Qed. 

  Lemma E_w_step p w : E p (wo + w) = (inr (inr (p, |_|))) :: E p (wo + w -1).
  Proof.
    remember (w + wo). destruct n. 
    + unfold wo in Heqn; lia. 
    + now cbn. 
  Qed. 

  Lemma E_polarityFlip p n : map polarityFlipGamma (E p n) = E (polarityFlip p) n. 
  Proof. induction n; cbn; now f_equal. Qed. 

  Definition mapPolarity p u : list Gamma := map (fun e => inr (inr (p, Some e))) u.
  Definition reprTape' w u h p:= length h = S wo + w /\ length u <= w /\ h = (mapPolarity p u) ++ E p ( wo + w - (|u|)). 

  Definition reprTape := reprTape' z'. 

  Notation "u '≃t' h" := (exists p, reprTape u h p) (at level 80).
  Notation "u '≃t(' p ')' h" := (reprTape u h p) (at level 80). 

  Notation "u '≃t(' p ',' w ')' h" := (reprTape' w u h p) (at level 80). 

  Lemma niltape_repr : forall w p, [] ≃t(p, w) (E p (wo + w)) /\ forall a, [] ≃t(p, w) a -> a = E p (wo + w). 
  Proof.
    intros. repeat split.
    - apply E_length. 
    - now cbn.
    - intros. destruct H as (H1 & H2 & H3). now rewrite H3.
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
  Notation strconfig := (list Gamma).

  Definition embedState (q : states) (m : stateSigma) : Gamma := inl (q, m). 
  Definition reprConfig' c ls qm rs := match c with (q, tape) => exists p, qm = embedState q (current tape) /\ reprTape (left tape) ls p /\ reprTape (right tape) rs p end. 
  Definition reprConfig c (s : list Gamma) := exists ls qm rs, s = rev ls ++ [qm] ++ rs /\ reprConfig' c ls qm rs. 

  Notation "c '≃c' '(' ls ',' q ',' rs ')'" := (reprConfig' c ls q rs) (at level 80). 
  Notation "c '≃c' s" := (reprConfig c s) (at level 80). 



  (** *automation  *)

  Lemma tape_repr_step u h a b p w : (a :: u) ≃t(p, S w) (b :: h) -> u ≃t(p, w) h. 
  Proof. 
    intros (H1 & H2 & H3). cbn [length] in *; repeat split.
    - lia. 
    - lia. 
    - cbn [mapPolarity map] in H3. replace (wo + S w - S (|u|)) with (wo + w - (|u|)) in H3 by lia. 
      replace (map (fun e => inr (inr (p, Some e))) u) with (mapPolarity p u) in H3 by now cbn.  
      cbn [app] in H3. congruence. 
  Qed. 

  Lemma tape_repr_inv w u p (x : States) a : u ≃t(p, w) (@inl States tapeSigma x) :: a -> False. 
  Proof. 
    intros []. destruct H0. destruct u; now cbn in H1. 
  Qed. 

  Lemma tape_repr_inv2 w p p' (σ : Sigma) a : [] ≃t(p, w) (@inr States tapeSigma (inr (p', Some σ)))::a -> False. 
  Proof. 
    intros (H1 & H2 & H3).
    cbn in H3. congruence. 
  Qed. 

  Lemma tape_repr_inv3 w p p' (u : Sigma) (us : list Sigma) h : u :: us ≃t(p, w) (inr (inr (p', |_|)) :: h) -> False. 
  Proof. intros (H1 & H2 & H3). cbn in H3. congruence. Qed. 

  Lemma tape_repr_inv4 w p (u : list Sigma) h : u ≃t(p, w) (inr #) :: h -> False. 
  Proof. intros (H1 & H2 & H3). cbn in H3. destruct u; cbn in H3;  congruence. Qed. 

  Lemma tape_repr_inv5 w p u h e : u ≃t(p, w) (inr #) :: e:: h -> False. 
  Proof. intros (H1 & H2 & H3). destruct u; cbn in H3; congruence. Qed. 

  Lemma tape_repr_inv6 w p u us h : us :: u ≃t(p, w) h -> exists h' n, h = (inr (inr (p, Some us))):: h' ++ E p (wo + n) /\ w = n + S (|h'|) /\ |h'| = |u| /\ u ≃t(p, w -1) h' ++ E p (wo + n). 
  Proof.
    intros.
    destruct h. { destruct H. cbn in H; lia. }
    destruct H as (H1 & H2 & H3). 
    cbn [mapPolarity length map] in H3. exists (mapPolarity p u), (w - S (|u|)). 
    repeat split. 
    - cbn in H2, H1. replace (wo + (w - S (|u|))) with (wo + w - S (|u|)) by lia. apply H3. 
    - unfold mapPolarity. rewrite map_length. cbn in H2. lia. 
    - unfold mapPolarity. now rewrite map_length. 
    - unfold mapPolarity. rewrite app_length, map_length. cbn in H1, H2. rewrite E_length. lia. 
    - cbn in H2; lia. 
    - cbn in H2. easy.
  Qed.

  Lemma tape_repr_inv7 w p p' u us n : us :: u ≃t(p, w) E p' n -> False. 
  Proof. intros (H1 & H2 & H3). destruct n; cbn in H3; congruence. Qed.

  Lemma tape_repr_inv8 u us p w e rs : us :: u ≃t(p, w) inr(inr e) :: rs -> e = (p, Some us). 
  Proof. intros (H1 & H2 & H3). cbn in H3. congruence. Qed. 

  Lemma tape_repr_inv9 us1 p w e1 rs : [us1] ≃t(p, S w) e1 :: rs -> rs = E p (wo + w). 
  Proof. 
    intros (H1 & H2 & H3). cbn in H3. inv H3. easy. 
  Qed. 

  Lemma tape_repr_inv10 u p w rs : u ≃t(p, w) rs -> w >= |u|. 
  Proof. 
    intros (H1 & H2 & H3). now cbn in H2. 
  Qed. 

  Lemma tape_repr_inv11 u p w rs : u ≃t(p, w) rs -> |rs| >= S wo. 
  Proof. intros (H1 & H2 & H3). rewrite H1. lia. Qed. 

  Lemma tape_repr_inv12 u p w rs : u ≃t(p, w) rs -> forall x, x el rs -> exists y, x = inr y. 
  Proof. 
    intros (_ & _ & ->) x H1. 
    apply in_app_or  in H1 as [H1 | H1]. 
    + unfold mapPolarity in H1. apply in_map_iff in H1 as (? & <- & H2). eauto. 
    + revert H1. generalize (wo + w - |u|). induction n; intros [H | H]; eauto. 
  Qed. 

  Lemma tape_repr_inv13 u p p' w rs σ: u ≃t(p, w) (inr (inr (p', Some σ)) :: rs) -> p' = p /\ exists u', u = σ :: u'. 
  Proof. 
    intros (H1 & H2 & H3). destruct u; cbn in *. 
    + congruence. 
    + split; [ | exists u];  congruence. 
  Qed. 

  Lemma tape_repr_inv14 u p w rs e: u ≃t(p, w) e :: inr (#) :: rs -> False. 
  Proof. 
    intros (H1 & H2 & H3). destruct u; unfold wo in H3; cbn in H3; try congruence.
    destruct u; cbn in H3; try congruence.
  Qed. 

  Lemma tape_repr_inv15 u p w : u ≃t(p, w) [] -> False. 
  Proof.
    intros (H1 & H2 & H3). now cbn in H1.
  Qed. 

  Ltac destruct_tape1 := repeat match goal with [H : delim |- _ ] => destruct H end.
  Ltac discr_tape := destruct_tape1; match goal with
                     | [H : ?u ≃t(?p, ?w) [] |- _] => now apply tape_repr_inv15 in H
                     | [ H : ?u ≃t(?p, ?w) (inl ?e) :: ?a |- _] => now apply tape_repr_inv in H
                     
                     | [ H : [] ≃t(?p, ?w) (inr (inr (_, Some ?e))) :: ?a |- _] => now apply tape_repr_inv2 in H
                     | [ H : ?u :: ?us ≃t(?p, ?w) inr (inr (_, |_|)):: ?a |- _] => now apply tape_repr_inv3 in H
                     | [H : _ ≃t(_, _) _ :: inr # :: _ |- _ ] => now apply tape_repr_inv14 in H
                     | [ H : ?us ≃t(?p, ?w) inr # :: ?a |- _] => now apply tape_repr_inv4 in H
                     | [H : _ ≃t(?p, ?w) inr # :: ?e :: ?a |- _] => now apply tape_repr_inv5 in H
                     | [H : ?u :: ?us ≃t(?p, 0) _ |- _] => destruct H; cbn in *; lia
                     | [H : ?u :: ?us ≃t(?p, ?w) E _ ?n |- _] => now apply tape_repr_inv7 in H
                     | [H : ?us ≃t(?p, ?w) ?a |- _] => let H1 := fresh in apply tape_repr_inv11 in H as H1; unfold wo in H1; cbn [length] in H1; lia (*this is really expensive, but in some cases desirable to have *)
                     (* | [H : ?us ≃t(?p, ?w) _ |- _] => try (apply tape_repr_inv10 in H; cbn in H; lia) *)
                      end. 

  Ltac inv_tape' H := repeat match type of H with
                        | _ ≃t(?p, ?w) ?x :: ?h => is_var x; destruct x; [discr_tape | ]     
                        | _ ≃t(?p, ?w) (inr ?e) :: ?h => is_var e; destruct e; [discr_tape | ]
                        | [] ≃t(?p, ?w) (inr (inr ?e)) :: ?h => is_var e; destruct e
                        | ?u ≃t(?p, ?w) inr (inr (_, |_|)) :: ?h => is_var u; destruct u; [ | discr_tape] 
                        | ?u :: ?us ≃t(?p, ?w) ?h => is_var h; destruct h; [ discr_tape | ]
                        | ?u :: ?us ≃t(?p, ?w) ?h' ++ ?h'' => is_var h'; destruct h'; cbn in H; try discr_tape
                        | ?u :: ?us ≃t(?p, ?w) inr(inr ?e) :: _ => is_var e; specialize (tape_repr_inv8 H) as ->  
                        | ?u1 :: _ ≃t(?p, ?w) _  => is_var w; destruct w; [ discr_tape | ]
                        | ?u1 :: [] ≃t(_, S ?w) _ :: ?h  => specialize (tape_repr_inv9 H) as ->
                        | ?u ≃t(_, _) inr (inr (_, Some _)) :: _ => is_var u;
                                                                  let Heqn := fresh "Hpeqn" in
                                                                  specialize (tape_repr_inv13 H) as (Heqn & (? & ->)); inv Heqn
                        end;
                        (*if we can, we go into recursion after applying tape_repr_step *)
                        match type of H with
                        |  ?u1 :: _ ≃t(?p, S ?w) ?e :: _  => let H' := fresh in specialize (tape_repr_step H) as H'; inv_tape' H'; clear H' 
                         | _ => idtac
                        end.

  (*the destruct_tape_in tactic generates equations for subtapes which are equal to E _. *)
  (*We do not want to call inv on those equations since they might contain non-trivial equalities which cannot be resolved with a rewrite and would thus be lost with inv*)
  Ltac clear_trivial_niltape H := cbn in H; match type of H with
        | inr (inr (?p, |_|)) :: ?h = inr (inr (?p, |_|)) :: ?h' => let H' := fresh in assert (h = h') as H' by congruence; tryif clear_trivial_niltape H' then clear H else clear H'
        | ?h = inr (inr _) :: _ => is_var h; rewrite H in *; clear H
        | ?h = E _ _ => is_var h; rewrite H in *; clear H
  end.

  Ltac destruct_tape_in H := unfold reprTape in H;
                             inv_tape' H;
                             try match type of H with
                                 | [] ≃t(_, _) ?h => let H' := fresh in specialize (proj2 (niltape_repr _ _ ) _ H) as H'; clear_trivial_niltape H'
                                 | ?u ≃t(?p, ?w) inr _ :: ?h  => is_var u; destruct u; try discr_tape
                                 end;
                             inv_tape' H;
                             repeat match goal with [H : ?h = ?h |- _] => clear H end.

  Ltac destruct_tape_in_tidy H := unfold reprTape in H;
                             try match type of H with
                                 | _ ≃t(_, z') _ => let H' := fresh "n" in let H'' := fresh H' "Zeqn" in
                                                    remember z' as H' eqn:H'' in H; destruct_tape_in H;
                                                    repeat match goal with [H2 : context[wo + H'] |- _]=> cbn [wo Nat.add] in H2 end; rewrite !H'' in *; try clear H' H'' 
                                 | _ => destruct_tape_in H
                             end. 
 
  Ltac inv_tape := match goal with
                        | [H : _ ≃t(_, _) _ |- _] => inv_tape' H
                   end. 

  Ltac unfold_tape := unfold reprTape in *. 
                        
  Ltac destruct_tape := unfold_tape; inv_tape;
                        try match goal with
                        | [H: ?u ≃t(?p, ?w) inr _ :: ?h |- _] => is_var u; destruct u; try discr_tape
                            end;
                        inv_tape;
                        repeat match goal with [H : ?h = ?h |- _] => clear H end.

(*For easier automation, we define the rewrite rules using inductive predicates *)
  Section fixRulePred.
    (*We define the equivalent of rewritesHeadList for predicate-based rules  *)

    Context {X : Type}.
    Context (p : X -> X -> X -> X -> X -> X -> Prop). 

    Inductive rewritesHeadInd: list X -> list X -> Prop :=
      | rewHead_indC (x1 x2 x3 x4 x5 x6 : X) s1 s2 : p x1 x2 x3 x4 x5 x6 -> rewritesHeadInd (x1 :: x2 :: x3 :: s1) (x4 :: x5 :: x6 :: s2). 

    Hint Constructors rewritesHeadInd. 

    (*a few facts which will be useful *)
    Lemma rewritesHeadInd_tail_invariant (γ1 γ2 γ3 γ4 γ5 γ6 : X) s1 s2 s1' s2' :
      rewritesHeadInd (γ1 :: γ2 :: γ3 :: s1) (γ4 :: γ5 :: γ6 :: s2) <-> rewritesHeadInd (γ1 :: γ2 :: γ3 :: s1') (γ4 :: γ5 :: γ6 :: s2').
    Proof. split; intros; inv H; eauto. Qed. 

    Corollary rewritesHeadInd_rem_tail (γ1 γ2 γ3 γ4 γ5 γ6 : X) h1 h2 :
      rewritesHeadInd [γ1; γ2; γ3] [γ4; γ5; γ6] <-> rewritesHeadInd (γ1 :: γ2 :: γ3 :: h1) (γ4 :: γ5 :: γ6 :: h2).
    Proof. now apply rewritesHeadInd_tail_invariant. Qed. 

    Lemma rewritesHeadInd_append_invariant (γ1 γ2 γ3 γ4 γ5 γ6 : X) s1 s2 s1' s2' :
      rewritesHeadInd (γ1 :: γ2 :: γ3 :: s1) (γ4 :: γ5 :: γ6 :: s2) <-> rewritesHeadInd (γ1 :: γ2 :: γ3 :: s1 ++ s1') (γ4 :: γ5 :: γ6 :: s2 ++ s2').
    Proof. now apply rewritesHeadInd_tail_invariant. Qed.

    Lemma rewritesAt_rewritesHeadInd_add_at_end i a b h1 h2 :
      rewritesAt rewritesHeadInd i a b -> rewritesAt rewritesHeadInd i (a ++ h1) (b ++ h2).
    Proof. 
      intros. unfold rewritesAt in *. inv H; symmetry in H0; symmetry in H1; repeat erewrite skipn_app2; eauto; try congruence; cbn; eauto. 
    Qed.

    Lemma rewritesAt_rewritesHeadInd_rem_at_end i a b h1 h2 :
      rewritesAt rewritesHeadInd i (a ++ h1) (b ++ h2) -> i < |a| - 2 -> i < |b| - 2 -> rewritesAt rewritesHeadInd i a b.
    Proof. 
      intros. unfold rewritesAt in *.
      assert (i <= |a|) by lia. destruct (skipn_app3 h1 H2) as (a' & H3 & H4). rewrite H3 in H. 
      assert (i <= |b|) by lia. destruct (skipn_app3 h2 H5) as (b' & H6 & H7). rewrite H6 in H. 
      clear H2 H5.
      rewrite <- firstn_skipn with (l := a) (n := i) in H4 at 1. apply app_inv_head in H4 as <-. 
      rewrite <- firstn_skipn with (l := b) (n := i) in H7 at 1. apply app_inv_head in H7 as <-. 
      specialize (skipn_length i a) as H7. specialize (skipn_length i b) as H8. 
      remember (skipn i a) as l. do 3 (destruct l as [ | ? l] ; [cbn in H7; lia | ]). 
      remember (skipn i b) as l'. do 3 (destruct l' as [ | ? l']; [cbn in H8; lia | ]). 
      cbn in H. rewrite rewritesHeadInd_tail_invariant in H. apply H. 
    Qed. 
  End fixRulePred. 

  Hint Constructors rewritesHeadInd.

  (*unfold the three symbols at the head of premise and conclusion of a rewrite rule *)
  Ltac rewritesHeadInd_inv := 
    repeat match goal with
    | [H : rewritesHeadInd _ ?a _ |- _] => is_var a; destruct a; try (inv H; fail)
    | [H : rewritesHeadInd _ (_ :: ?a) _ |- _] => is_var a; destruct a; try (inv H; fail)
    | [H : rewritesHeadInd _ (_ :: _ :: ?a) _ |- _] => is_var a; destruct a; try (inv H; fail)
    | [H : rewritesHeadInd _ _ ?a |- _ ] => is_var a; destruct a; try (inv H; fail)
    | [H : rewritesHeadInd _ _ (_ :: ?a) |-_ ] => is_var a; destruct a; try (inv H; fail)
    | [H : rewritesHeadInd _ _ (_ :: _ :: ?a) |- _] => is_var a; destruct a; try (inv H; fail)
    end.


  (** *inductive rule predicates for tape rewrites *)

  (*the rules for shifting the tape to the right *)
  Inductive shiftRightRules : Gamma -> Gamma -> Gamma -> Gamma -> Gamma -> Gamma -> Prop :=
    | shiftRightSSSS σ1 σ2 σ3 σ4 p : shiftRightRules (inr (inr (p, Some σ1))) (inr (inr (p, Some σ2))) (inr (inr (p, Some σ3))) (inr (inr (positive, Some σ4))) (inr (inr (positive, Some σ1))) (inr (inr (positive, Some σ2))) 
    | shiftRightBBBS p σ1 : shiftRightRules (inr (inr (p, |_|))) (inr (inr (p, |_|))) (inr (inr (p, |_|))) (inr (inr (positive, Some σ1))) (inr (inr (positive, |_|))) (inr (inr (positive, |_|)))
    | shiftRightBBBB p : shiftRightRules (inr (inr (p, |_|))) (inr (inr (p, |_|))) (inr (inr (p, |_|))) (inr (inr (positive, |_|))) (inr (inr (positive, |_|))) (inr (inr (positive, |_|)))
    | shiftRightSBB σ1 σ2 p : shiftRightRules (inr (inr (p, Some σ1))) (inr (inr (p, |_|))) (inr (inr (p, |_|))) (inr (inr (positive, Some σ2))) (inr (inr (positive, Some σ1))) (inr (inr (positive, |_|)))
    | shiftRightSSB σ1 σ2 σ3 p : shiftRightRules (inr (inr (p, Some σ1))) (inr (inr (p, Some σ2))) (inr (inr (p, |_|))) (inr (inr (positive, Some σ3))) (inr (inr (positive, Some σ1))) (inr (inr (positive, Some σ2))) 
    | shiftRightBBS σ1 p : shiftRightRules (inr (inr (p, |_|))) (inr (inr (p, |_|))) (inr (inr (p, Some σ1))) (inr (inr (positive, |_|))) (inr (inr (positive, |_|))) (inr (inr (positive, |_|)))
    | shiftRightBSS σ1 σ2 p : shiftRightRules (inr (inr (p, |_|))) (inr (inr (p, Some σ1))) (inr (inr (p, Some σ2))) (inr (inr (positive, |_|))) (inr (inr (positive, |_|))) (inr (inr (positive, Some σ1)))
    | shiftRightSSSB σ1 σ2 σ3 p : shiftRightRules (inr (inr (p, Some σ1))) (inr (inr (p, Some σ2))) (inr (inr (p, Some σ3))) (inr (inr (positive, |_|))) (inr (inr (positive, Some σ1))) (inr (inr (positive, Some σ2))).

  Hint Constructors shiftRightRules. 

  (*identity rules *)
  Inductive identityRules : Gamma -> Gamma -> Gamma -> Gamma -> Gamma -> Gamma -> Prop :=
    | identityC (m1 m2 m3 : stateSigma) p : identityRules (inr (inr (p, m1))) (inr (inr (p, m2))) (inr (inr (p, m3))) (inr (inr (neutral, m1))) (inr (inr (neutral, m2))) (inr (inr (neutral, m3)))
  | identityDBB p p' : identityRules (inr #) (inr (inr (p, |_|))) (inr (inr (p, |_|))) (inr #) (inr (inr (p', |_|))) (inr (inr (p', |_|)))
  | identityBBD p p' : identityRules (inr (inr (p, |_|))) (inr (inr (p, |_|))) (inr #) (inr (inr (p', |_|))) (inr (inr (p', |_|))) (inr #). 

  Hint Constructors identityRules.

  (*the rules for shifting the tape left are derived from the ones for right shifts using reversion and polarity flips *)
  Inductive tapeRules : Gamma -> Gamma -> Gamma -> Gamma -> Gamma -> Gamma -> Prop :=
  | shiftLeftTapeC γ1 γ2 γ3 γ4 γ5 γ6: shiftRightRules (~γ3) (~γ2) (~γ1) (~γ6) (~γ5) (~γ4) -> tapeRules γ1 γ2 γ3 γ4 γ5 γ6
  | shiftRightTapeC γ1 γ2 γ3 γ4 γ5 γ6: shiftRightRules γ1 γ2 γ3 γ4 γ5 γ6 -> tapeRules γ1 γ2 γ3 γ4 γ5 γ6
  | identityTapeC γ1 γ2 γ3 γ4 γ5 γ6: identityRules γ1 γ2 γ3 γ4 γ5 γ6 -> tapeRules γ1 γ2 γ3 γ4 γ5 γ6. 

  Hint Constructors tapeRules. 

  Notation rewHeadTape := (rewritesHeadInd tapeRules).

  (*since the rules for shifting left are derived from the rules for shifting right using polarityFlipGamma, the polarity flip functions need to be reduced in order to be able to apply the constructors *)
  Hint Extern 4 (tapeRules _ _ _ _ _ _) => apply shiftLeftTapeC;
  cbn [polarityFlipGamma polarityFlipTapeSigma polarityFlipSigma polarityFlip].


  Ltac rewHeadTape_inv1 :=
    repeat match goal with
    | [H : rewHeadTape _ _ |- _] => inv H
    | [H : tapeRules _ _ _ _ _ _ |- _] => inv H
    end.

  (*identity rules are invariant under polarity flip + reversion *)
  Lemma identityWindow_revp (γ1 γ2 γ3 γ4 γ5 γ6 : Gamma) : identityRules γ1 γ2 γ3 γ4 γ5 γ6 <-> identityRules (~γ3) (~γ2) (~γ1) (~γ6) (~γ5) (~γ4).
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

  (*in fact, all tape rules are invariant under polarity flip + reversion: for the shift rules, this directly follows from the definition *)
  Lemma tapeRules_revp' γ1 γ2 γ3 γ4 γ5 γ6 : tapeRules γ1 γ2 γ3 γ4 γ5 γ6 -> tapeRules (~γ3) (~γ2) (~γ1) (~γ6) (~γ5) (~γ4). 
  Proof. 
    intros. rewHeadTape_inv1. 
    - eauto. 
    - constructor. now rewrite !polarityFlipGamma_involution.
    - apply identityWindow_revp in H0. eauto.  
  Qed. 

  Lemma tapeRules_revp γ1 γ2 γ3 γ4 γ5 γ6 : tapeRules γ1 γ2 γ3 γ4 γ5 γ6 <-> tapeRules (~γ3) (~γ2) (~γ1) (~γ6) (~γ5) (~γ4).
  Proof. 
    split.
    apply tapeRules_revp'. intros H%tapeRules_revp'.
    specialize polarityFlipGamma_involution as H1. unfold involution in H1.
    now repeat rewrite H1 in H.
  Qed.

  (*inversion of the tape rules *)
  Ltac rewHeadTape_inv2 :=
    repeat match goal with
      | [H : rewHeadTape _ _ |- _ ] => inv H
      | [H : tapeRules _ _ _ _ _ _ |- _] => inv H
      | [H : shiftRightRules _ _ _ _ _ _ |- _ ] => inv H
      | [H : identityRules _ _ _ _ _ _ |- _] => inv H
      | [d : delim |- _] => destruct d
      | [H : (~?e) = inr (inr (_, _)) |- _] => apply polarityFlipGammaInv1 in H; try rewrite H in *; clear H
      | [H : inr (inr (_, _)) = (~?e) |- _] => symmetry in H; apply polarityFlipGammaInv1 in H; try rewrite H in *; clear H
      | [H : inr _ = inr _ |- _] => inv H
      | [H : inl _ = inl _ |- _] => inv H
    end; try congruence. 
 
  (*the following lemmas allow us to prove results only for the right tape half and derive the corresponding results for the left tape half as corollaries *)
  (*Lemma 15 *)
  Lemma tape_rewrite_symm1 h h' :
    valid rewHeadTape h h' -> valid rewHeadTape (polarityRev h) (polarityRev h').
  Proof.
    intros.  
    induction H; intros. 
    - cbn; constructor. 
    - apply valid_length_inv in H.
      destruct a, b; try destruct a; try destruct b; cbn in *; try lia. all: repeat constructor. 
    - rewritesHeadInd_inv; cbn. 
      rewrite valid_iff. unfold validExplicit. repeat rewrite app_length.
      repeat rewrite rev_length, map_length. cbn [length]. split.
      1: apply valid_length_inv in H; now cbn [length] in H. 
      replace ((|a|) + 1 + 1 + 1 - 2) with (S (|a|)) by lia. intros. destruct (nat_eq_dec i (|a|)) as [-> | F]. 
      * (*rewrite at the new position, cannot apply IH *)
        unfold rewritesAt. 
        apply rewritesHeadInd_rem_tail in H0.
        inv H0. apply tapeRules_revp' in H3. 
        cbn [rev map].
        repeat rewrite <- app_assoc.
        rewrite skipn_app with (xs := rev (map polarityFlipGamma a)).
        rewrite skipn_app with (xs := rev (map polarityFlipGamma b)).
        2, 3: rewrite rev_length, map_length. 3: reflexivity. 
        2: { apply valid_length_inv in H; cbn [length] in H. lia. }
        cbn. constructor. apply H3. 
      * (*this follows by IH *)
        cbn [polarityRev map rev] in IHvalid. 
        apply valid_iff in IHvalid as (IH1 & IH2). 
        assert (0 <= i < |a|) by lia. 
        repeat rewrite app_length in IH2. rewrite rev_length, map_length in IH2. cbn [length] in IH2.
        replace ((|a|) + 1 + 1 - 2) with (|a|) in IH2 by lia. 
        specialize (IH2 i H2).
        apply rewritesAt_rewritesHeadInd_add_at_end. apply IH2. 
  Qed. 

  Lemma tape_rewrite_symm2 h h' : valid rewHeadTape (polarityRev h) (polarityRev h') -> valid rewHeadTape h h'.
  Proof.
    intros. specialize (tape_rewrite_symm1 H) as H1. now repeat rewrite polarityRev_involution in H1.
  Qed. 

  Lemma tape_rewrite_symm3 h h' : valid rewHeadTape h h' -> valid rewHeadTape (map polarityFlipGamma h) h'. 
  Proof. 
    intros. unfold reprTape in H. induction H; intros. 
    - cbn; constructor. 
    - cbn; constructor. 2: now rewrite map_length. apply IHvalid.  
    - cbn. rewritesHeadInd_inv. constructor 3.
      + apply IHvalid. 
      + cbn. apply rewritesHeadInd_rem_tail.
        rewHeadTape_inv2; cbn; eauto 100.  
  Qed.

  (*Lemma 16 *)
  Lemma E_rewrite_blank p p' n: valid rewHeadTape (E p (S (S n))) (E p' (S (S n))). 
  Proof. 
    intros. induction n. 
    + apply valid_base. eauto. 
    + constructor 3. 
      - cbn [E] in IHn. now apply IHn. 
      - destruct p'; eauto. 
  Qed. 

  (*blank rewriting is uniquely determined if the head of the target is known *)
  Lemma E_rewrite_blank_unique' p p' n : n >= 1 -> forall s, valid rewHeadTape (E p' (S n)) (inr (inr (p, |_|)) :: s) -> s = E p n. 
  Proof. 
    intros H. induction n; intros; [lia | ]. 
    destruct n; cbn [E] in *. 
    + inv_valid. rewHeadTape_inv2. 
      apply valid_length_inv in H4. inv H4. now (destruct s2; cbn in H1).
    + inv_valid. rewHeadTape_inv2.
      1-2: cbn in *; destruct p; cbn in H5; try congruence; clear H5.
      all: apply IHn in H4; [congruence | lia]. 
  Qed. 

  Corollary E_rewrite_blank_unique p p' n : forall s, valid rewHeadTape (E p (S (S n))) (inr (inr (p', |_|)) :: s) -> s = E p' (S n).
  Proof. intros; now eapply E_rewrite_blank_unique'. Qed.

  (*the same results for the left tape half *)
  Lemma E_rewrite_blank_rev p p' w : valid rewHeadTape (rev (E p (S (S w)))) (rev (E p' (S (S w)))).  
  Proof. 
    rewrite <- polarityFlip_involution with (x := p). rewrite <- polarityFlip_involution with (x := p'). 
    rewrite <- !E_polarityFlip. apply tape_rewrite_symm1. rewrite !E_polarityFlip. apply E_rewrite_blank.
  Qed. 

  Lemma E_rewrite_blank_rev_unique p p' w s : valid rewHeadTape (rev (E p (S (S w)))) (rev (inr (inr (p', |_|)) :: s)) -> s = (E p' (S (w))). 
  Proof. 
    intros.
    assert (valid rewHeadTape (polarityRev (E (polarityFlip p) (S (S w)))) (polarityRev (map polarityFlipGamma (inr (inr (p', |_|)) :: s)))). 
    {
      unfold polarityRev. rewrite E_polarityFlip. rewrite map_involution. 2: involution_simpl. rewrite polarityFlip_involution. apply H.
    }
    apply tape_rewrite_symm2 in H0.
    cbn in H0. apply E_rewrite_blank_unique in H0.
    apply involution_invert_eqn2 with (a := s) (f:= (map polarityFlipGamma))  (b := E (polarityFlip p') (S w)) in H0.
    2: involution_simpl. now rewrite H0, E_polarityFlip, polarityFlip_involution. 
  Qed. 

  (*Lemma 17 *)
  (*we can leave a tape string which only contains one non-blank unchanged *)
  Lemma E_rewrite_sym_stay p σ n : valid rewHeadTape (inr (inr (p, Some σ)) :: E p (S (S n))) (inr (inr (∘ (Some σ))) :: E neutral (S (S n))).  
  Proof. 
    constructor 3. 
    - apply E_rewrite_blank. 
    - cbn[E]. apply rewritesHeadInd_rem_tail. eauto. 
  Qed. 

  (*we can add a symbol at the head of an empty tape string *)
  Lemma E_rewrite_sym p σ n: valid rewHeadTape (E p (S (S (S n)))) (inr (inr (positive, Some σ)) :: E positive (S (S n))). 
  Proof. 
    cbn [E].
    constructor 3. 
    - apply E_rewrite_blank. 
    - eauto. 
  Qed. 

  Lemma E_rewrite_sym_unique p m n : forall (s : string Gamma), valid rewHeadTape (E p (S (S (S n)))) (inr (inr (positive, m)) :: s) -> s = E positive (S (S n)). 
  Proof. 
    intros. inv_valid. rewHeadTape_inv2.
    all: cbn [E]; f_equal; apply E_rewrite_blank_unique in H3; auto. 
  Qed. 

  Lemma E_rewrite_sym_rev p σ n : valid rewHeadTape (rev (E p (S (S (S n))))) (rev (inr (inr (negative, Some σ)) :: E negative (S (S n)))). 
  Proof. 
    (*follows using tape_rewrite_symm1, tape_rewrite_symm3 and E_rewrite_sym *)
    specialize (E_rewrite_sym p σ n) as H1. 
    eapply tape_rewrite_symm1 in H1. 
    eapply tape_rewrite_symm3 in H1.
    unfold polarityRev in H1. rewrite map_rev, map_map in H1. setoid_rewrite polarityFlipGamma_involution in H1. rewrite map_id in H1. 
    cbn [map polarityFlipGamma polarityFlipTapeSigma polarityFlipSigma polarityFlip] in H1. 
    now rewrite E_polarityFlip in H1. 
  Qed. 

  Lemma E_rewrite_sym_rev_unique p σ n : forall s, valid rewHeadTape (rev (E p (S (S (S n))))) (rev (inr (inr (negative, Some σ)) :: s)) -> s = E negative (S (S n)). 
  Proof. 
    intros.
    assert (valid rewHeadTape (polarityRev (E (polarityFlip p) (S (S (S n))))) (polarityRev (inr (inr (positive, Some σ)) :: map polarityFlipGamma s))). 
    {
      unfold polarityRev. rewrite E_polarityFlip. cbn. rewrite map_involution. 2: involution_simpl.
      specialize (polarityFlip_involution p) as H1. rewrite H1. apply H. 
    }
    eapply tape_rewrite_symm2 in H0.
    apply E_rewrite_sym_unique in H0. 
    enough (map polarityFlipGamma (E negative (S (S n))) = E positive (S (S n))).
    { rewrite <- H1 in H0. apply involution_invert_eqn in H0. assumption. apply map_involution, polarityFlipGamma_involution. }
    apply E_polarityFlip. 
  Qed. 

  (*we can also remove a symbol *)
  Lemma E_rewrite_sym_rem p σ n : valid rewHeadTape (inr (inr (p, Some σ)) :: E p (S (S n))) (E negative (S (S (S n)))). 
  Proof. 
    cbn. constructor 3.  
    - apply E_rewrite_blank.
    - eauto. 
  Qed. 

  Lemma  E_rewrite_sym_rem_unique p p' σ n : forall s, valid rewHeadTape (inr (inr (p, Some σ)) :: E p (S (S n))) (inr (inr (p', |_|)):: s) -> p' = negative /\ s = E negative (S (S n)). 
  Proof. 
    intros. inv_valid. rewHeadTape_inv2.
    destruct p'; cbn in H5; try congruence; clear H5.
    split; [reflexivity | ]. 
    inv_valid. 1: destruct n; cbn in H5; lia.
    rewHeadTape_inv2.
    3: {
      destruct n; cbn in *; inv H3.
      apply valid_length_inv in H2; destruct s0; cbn in H2; congruence.
    }
    all: destruct n; cbn in H3; [congruence | ];
      apply E_rewrite_blank_unique in H2;
      rewrite H2; easy.   
  Qed. 

  Lemma E_rewrite_sym_rem_rev p σ n : valid rewHeadTape (rev (inr (inr (p, Some σ)) :: E p (S (S n)))) (rev (E positive (S (S (S n))))). 
  Proof. 
    specialize (E_rewrite_sym_rem p σ n) as H1. 
    eapply tape_rewrite_symm1 in H1. 
    eapply tape_rewrite_symm3 in H1.
    unfold polarityRev in H1. rewrite map_rev, map_map in H1. setoid_rewrite polarityFlipGamma_involution in H1. rewrite map_id in H1. 
    cbn [map polarityFlipGamma polarityFlipTapeSigma polarityFlipSigma polarityFlip] in H1. 
    now rewrite E_polarityFlip in H1. 
  Qed. 

  Lemma E_rewrite_sym_rem_rev_unique p p' σ n : forall s, valid rewHeadTape (rev (inr (inr (p, Some σ)) :: E p (S (S n)))) (rev (inr (inr (p', |_|)) :: s)) -> p' = positive /\ s = E p' (S (S n)). 
  Proof. 
    intros.
    assert (valid rewHeadTape (polarityRev (inr (inr (polarityFlip p, Some σ)) :: E (polarityFlip p) (S (S n)))) (polarityRev (inr (inr (polarityFlip p', |_|)) :: map polarityFlipGamma s))). 
    {
      unfold polarityRev. cbn [map]. rewrite E_polarityFlip. cbn. rewrite map_involution. 2: apply polarityFlipGamma_involution.
      specialize (polarityFlip_involution) as H1. unfold involution in H1. 
      rewrite !H1. apply H. 
    }
    eapply tape_rewrite_symm2 in H0.
    apply E_rewrite_sym_rem_unique in H0 as (H0 & H1). 
    destruct p'; cbn in H0; try congruence; clear H0. 
    split; [reflexivity | ]. 
    enough (map polarityFlipGamma (E negative (S (S n))) = E positive (S (S n))).
    { rewrite <- H1 in H0. rewrite map_involution in H0; [apply H0 | involution_simpl]. }
    apply E_polarityFlip. 
  Qed. 

  (** *the following results generalise Lemma 15 *)

  (*Lemma 18 *)
  (*we can add a symbol to an arbitrary tape string if there is enough space left *)
  Lemma tape_repr_add_right rs σ h p w:
    rs ≃t(p, w) h -> length rs < w
    -> exists h', valid rewHeadTape h (inr (inr (↑ (Some σ))) :: h')
            /\ (forall h0, valid rewHeadTape h (inr (inr (↑ (Some σ))) :: h0) -> h0 = h')
            /\ σ :: rs ≃t(positive, w)  (inr (inr (↑ (Some σ))) :: h').
  Proof. 
    intros. revert w h σ H H0. 
    induction rs.
    - intros. destruct_tape_in_tidy H.
      exists (E positive (wo + w - 1)). rewrite <- and_assoc; split.
      + cbn in H0. destruct w; [lia | ]. unfold wo.
        replace (2 + S w) with (S (S (S w))) by lia. cbn [Nat.sub]. split.
        * (*existence*) apply E_rewrite_sym.
        * (*uniqueness*) intros. eapply E_rewrite_sym_unique with (m := Some σ), H1. 
      + repeat split. 
        * cbn. rewrite E_length. lia. 
        * now cbn. 
    - intros. apply tape_repr_inv6 in H as (h' & n & -> & -> & H2 & H3).
      replace (n + S (|h'|) - 1) with (n + |h'|) in H3 by lia.
      destruct rs; [ | destruct rs].
      + (*at the end of the used tape region *)
        destruct h'; [clear H2 | now cbn in H2]. clear H3.
        destruct n; [cbn in H0; cbn in H0; lia | ].
        exists (inr (inr ((↑ (Some a)))):: E positive (wo + n)). rewrite <- and_assoc; split.
        * cbn. split.
          ++ (*existence*) constructor 3. 
             -- apply E_rewrite_sym. 
             -- apply rewritesHeadInd_rem_tail. eauto. 
          ++ (*uniqueness *) intros. inv_valid.
             rewHeadTape_inv2. apply E_rewrite_sym_unique with (m := Some a) in H4. now inv H4. 
        * repeat split; cbn. 
          -- rewrite E_length. cbn in H0. lia. 
          -- cbn in H0; lia. 
          -- now rewrite Nat.add_comm.
      + (* rs has length 1*)
        destruct_tape. cbn [app] in H3. 
        destruct h'; [ | now cbn in H2]. clear H2.
        cbn [app] in H3. destruct_tape. cbn [length] in *.
        destruct n; [lia | ]. clear H0. 
        exists (inr(inr (↑ (Some a))) :: inr (inr (↑ (Some e))) :: E positive (wo + n)). 
        cbn [app]; rewrite <- and_assoc; split. 
        * split.
          ** (*existence*) constructor 3. 
              -- replace (2 + S n) with (S(S (S n))) by lia. constructor 3. 
                ++ apply E_rewrite_sym. 
                ++ cbn [E]. apply rewritesHeadInd_rem_tail; eauto. 
              -- cbn[E]. apply rewritesHeadInd_rem_tail. eauto. 
          ** (*uniqueness*)
            intros. inv_valid. rewHeadTape_inv2. 
            inv_valid. rewHeadTape_inv2. 
            apply E_rewrite_sym_unique in H2. 
            cbn [E] in H2. inv H2. inv H3. reflexivity.  
        * repeat split.
          -- cbn. rewrite E_length. lia. 
          -- cbn; lia. 
          -- cbn[mapPolarity map length app]. now replace (wo + (S n + 2) - 3) with (wo + n) by lia. 
     + (*rs has at least two elements. this is the interesting case as it needs the IH *) 
       destruct_tape. cbn [app] in H3. cbn [length app] in H3. rewrite Nat.add_succ_r in H3. 
       apply tape_repr_step in H3 as H4. destruct_tape. cbn [app length] in *. destruct_tape. 

       (*we use the IH with h := inr (...e) :: inr (...e0) :: h' ++ E(n + wo); w := S (S (n + |h'|)); σ := a *)
       rewrite Nat.add_succ_r in H3. specialize (IHrs _ _ a H3). 
       edestruct (IHrs) as (h'' & F1 & F3 & F2). lia. 
       exists (inr (inr (↑(Some a))) :: h'').
       (*we need to know one more symbol at the head of h'' for the proof *)
       destruct_tape_in F2. 
       rewrite <- and_assoc; split; [split | ].
       * (*existence*)constructor 3.  
         -- apply F1. 
         -- apply rewritesHeadInd_rem_tail; eauto. 
       * (*uniqueness*)
         intros. clear IHrs. inv_valid. rewHeadTape_inv2. apply F3 in H7. inv H7. reflexivity. 
       * repeat split.
         -- cbn; destruct F2 as (F2 & _ & _). cbn in F2. lia.  
         -- cbn; destruct F2 as (_ & F2 & _). cbn in F2. lia. 
         -- destruct F2 as (_ & _ & ->). cbn[app length Nat.add Nat.sub].
            replace (wo + (n + S (S (S (|h'|)))) - (S (S (S (S(|rs|)))))) with (wo + S (S (n + (|h'|))) - S (S (S(|rs|)))) by lia.
            easy. 
  Qed. 

  (*the same result for the left tape half can be derived using the symm lemmas*)
  Corollary tape_repr_add_left ls σ h p w:
    ls ≃t(p, w) h -> length ls < w
    -> exists h', valid rewHeadTape (rev h) (rev (inr (inr (↓ (Some σ))) :: h'))
            /\ (forall h0, valid rewHeadTape (rev h) (rev (inr (inr (↓ (Some σ))) :: h0)) -> h0 = h')
            /\ σ :: ls ≃t(negative, w)  (inr (inr (↓ (Some σ))) :: h').
  Proof. 
    intros. specialize (@tape_repr_add_right ls σ h p w H H0) as (h' & H1 & H3 & H2). 
    exists (map polarityFlipGamma h'). rewrite <- and_assoc. split. 
    - eapply tape_rewrite_symm1 in H1.  
      apply tape_rewrite_symm3 in H1. split. 
      + cbn in *. unfold polarityRev in H1. rewrite map_rev in H1. rewrite map_involution in H1.
        2: apply polarityFlipGamma_involution.
        apply H1. 
      + intros. specialize (H3 (map polarityFlipGamma h0)).
        rewrite <- involution_invert_eqn2 with (f := map polarityFlipGamma) (a := h0) (b := h'); [reflexivity | apply map_involution, polarityFlipGamma_involution | ]. 
        apply H3. eapply tape_rewrite_symm2. 
        unfold polarityRev. rewrite <- map_rev. apply tape_rewrite_symm3. 
        cbn. rewrite map_involution; [now apply H4 | apply polarityFlipGamma_involution]. 
   - apply tape_repr_polarityFlip in H2. cbn in H2. easy. 
  Qed. 

  (*Lemma 19*)
  (*we can remove a symbol from the right tape half *)
  (*this is a weaker version where we know that the second symbol (the new head symbol) is not a blank *)
  (*the general version will be derived from this *)
  Lemma tape_repr_rem_right' rs σ1 σ2 (h : list Gamma) p w :
    σ1 :: σ2 :: rs ≃t(p, w) inr (inr (p, Some σ1)) :: inr (inr (p, Some σ2)) :: h
    -> exists (h' : list Gamma), valid rewHeadTape (inr (inr (p, Some σ1)) :: inr (inr (p, Some σ2)) :: h) (inr (inr (↓ (Some σ2))) :: h')
                           /\ (forall h0, valid rewHeadTape (inr (inr (p, Some σ1)) :: inr (inr (p, Some σ2)) :: h) (inr (inr (↓ (Some σ2))) :: h0) -> h0 = h')
                           /\ σ2 :: rs ≃t(negative, w) (inr (inr (↓ (Some σ2))) :: h').
  Proof. 
    revert w h σ1 σ2. 
    induction rs. 
    - intros. destruct_tape. exists (E negative (S wo + w)). rewrite <- and_assoc; split. 
      + (* existence*) split.
        * constructor 3.
          -- constructor 3.
             ++ apply E_rewrite_blank. 
             ++ apply rewritesHeadInd_rem_tail. eauto. 
          -- apply rewritesHeadInd_rem_tail. eauto. 
        * (*uniqueness *) intros. do 2 (inv_valid; rewHeadTape_inv2).  
           apply E_rewrite_blank_unique in H3. inv H3. now cbn. 
      + (*correctness*)
        repeat split.
        * cbn. rewrite E_length. lia. 
        * now cbn.
  - intros. destruct_tape_in H. 
    destruct rs. 
    + destruct_tape_in H. 
      exists (inr (inr (↓ (Some a))) :: E negative (S wo + w)). rewrite <- and_assoc; split. 
      * split. 
        -- constructor 3.
           ++ constructor 3. { apply E_rewrite_sym_rem. }
              apply rewritesHeadInd_rem_tail. eauto.  
           ++ apply rewritesHeadInd_rem_tail. eauto.
        -- (* uniqueness*) intros.  
           inv_valid. rewHeadTape_inv2; [inv_valid; rewHeadTape_inv2 | ].
           do 2 inv_valid; rewHeadTape_inv2. 
           apply E_rewrite_blank_unique in H4. inv H4. cbn [E]; easy. 
      * (*correctness *)
        repeat split. 
        -- cbn [length]. rewrite E_length. lia. 
        -- now cbn.
    + destruct_tape.
      (*need IH *)
      apply tape_repr_step in H. 
      specialize (IHrs _ _ σ2 a H) as (h0 & F1 & F2 & F3). destruct_tape. 
      exists (inr (inr (↓ (Some a))) :: (inr (inr (↓ (Some e)))) :: h0). 
      rewrite <- and_assoc; split; [split | ]. 
      * constructor 3.
        -- apply F1. 
        -- apply rewritesHeadInd_rem_tail. eauto. 
      * (*uniqueness *)intros. inv_valid. rewHeadTape_inv2; apply F2 in H4; now inv H4. 
      * clear F2 F1 H. destruct F3 as (H1 & H2 & H3). repeat split.
        -- cbn in *. lia. 
        -- cbn in *; lia. 
        -- inv H3. easy. 
  Qed.      

  Lemma tape_repr_rem_right rs σ (m : stateSigma) h p w :
    σ :: rs ≃t(p, w) inr (inr (p, Some σ)) :: inr (inr (p, m)) :: h
    -> exists h', valid rewHeadTape (inr (inr (p, Some σ)) :: inr (inr (p, m)) :: h) (inr (inr (negative, m)) :: h')
            /\ (forall h0, valid rewHeadTape (inr (inr (p, Some σ)) :: inr (inr (p, m)) :: h) (inr (inr (negative, m)) :: h0) -> h0 = h' )
            /\ rs ≃t(negative, w) (inr (inr (negative, m)) :: h').
  Proof. 
    intros. destruct m as [σ2 | ].
    + inv_tape' H.
      now apply tape_repr_rem_right'.
    + destruct_tape_in_tidy H.
      apply tape_repr_step in H as H'. destruct_tape_in_tidy H'. clear H'.
      exists (E negative (wo + w)). repeat split. 
      * constructor 3; [apply E_rewrite_blank | cbn; eauto ].
      * intros. inv_valid. rewHeadTape_inv2. 
        apply E_rewrite_blank_unique in H4. now inv H4.  
      * cbn; now rewrite E_length. 
      * now cbn. 
  Qed.

  Corollary tape_repr_rem_left ls σ (m : stateSigma) h p w :
    σ :: ls ≃t(p, w) inr (inr (p, Some σ)) :: inr (inr (p, m)) :: h
    -> exists h', valid rewHeadTape (rev (inr (inr (p, Some σ)) :: inr (inr (p, m)) :: h)) (rev (inr (inr (positive, m)) :: h'))
            /\ (forall h0, valid rewHeadTape (rev (inr (inr (p, Some σ)) :: inr (inr (p, m)) :: h)) (rev (inr (inr (positive, m)) :: h0)) -> h0 = h')
            /\ ls ≃t(positive, w) (inr (inr (positive, m)) :: h').
  Proof. 
    intros. specialize (@tape_repr_rem_right ls σ m h p w H) as (h' & H1 & H3 & H2). 
    exists (map polarityFlipGamma h'). rewrite <- and_assoc. split. 
    - eapply tape_rewrite_symm1 in H1. apply tape_rewrite_symm3 in H1.
      split. 
      + unfold polarityRev in H1. rewrite map_rev in H1. rewrite map_involution in H1. 2: apply polarityFlipGamma_involution.  destruct m; cbn in H1; cbn; apply H1.
      + intros. specialize (H3 (map polarityFlipGamma h0)).
        rewrite <- involution_invert_eqn2 with (f := map polarityFlipGamma) (a := h0) (b := h'); [reflexivity | apply map_involution, polarityFlipGamma_involution | ]. 
        apply H3. eapply tape_rewrite_symm2. 
        unfold polarityRev. rewrite <- map_rev. apply tape_rewrite_symm3. 
        cbn in *. rewrite map_involution; [destruct m; cbn in *; now apply H0 | apply polarityFlipGamma_involution]. 
   - apply tape_repr_polarityFlip in H2. destruct m; cbn in H2; easy. 
  Qed. 


  (*Lemma 20*)
  (*we can leave tape strings unchanged (mod polarity) *)
  Lemma tape_repr_stay_right' rs σ h p w :
    σ :: rs ≃t(p, w) inr(inr (p, Some σ)) :: h
    -> exists h', valid rewHeadTape (inr (inr (p, Some σ)) :: h) (inr (inr (neutral, Some σ)) :: h')
            /\ (forall h0, valid rewHeadTape (inr (inr (p, Some σ)) :: h) (inr (inr (∘ (Some σ))) :: h0) -> h0 = h')
            /\ σ :: rs ≃t(neutral, w) (inr (inr (∘ (Some σ)))) :: h'.
  Proof. 
    revert w h σ.  
    induction rs. 
    - intros. destruct_tape. exists (E neutral (wo + w)). 
      rewrite <- and_assoc. split. 
      + split.
        * constructor 3. apply E_rewrite_blank.
          apply rewritesHeadInd_rem_tail. eauto. 
        * intros. inv_valid.  
          rewHeadTape_inv2. apply E_rewrite_blank_unique in H4. inv H4. easy. 
      + repeat split; cbn in *; try rewrite E_length; cbn in *; easy. 
    - intros. destruct_tape_in H. destruct rs; destruct_tape_in H. 
      + exists (inr (inr (∘ (Some a))) :: E neutral (wo + w)). rewrite <- and_assoc; split. 
        * split.
          -- constructor 3. 2: { apply rewritesHeadInd_rem_tail. eauto. }
             apply E_rewrite_sym_stay. 
          -- intros. do 2 (inv_valid; rewHeadTape_inv2). 
             apply E_rewrite_blank_unique in H3. inv H3. easy. 
        * repeat split; cbn in *; try rewrite E_length; cbn in *; easy.  
     + apply tape_repr_step in H. specialize (IHrs _ _ a H) as (h0 & F1 & F2 & F3). destruct_tape_in F3. 
       exists (inr (inr (∘ (Some a))) :: inr (inr (∘ (Some e))) :: h0). rewrite <- and_assoc; split.
       * split.
         -- constructor 3.
            ++ apply F1. 
            ++ apply rewritesHeadInd_rem_tail; eauto. 
         -- intros. inv_valid. rewHeadTape_inv2. apply F2 in H4. inv H4. easy. 
       * clear F2 F1 H. destruct F3 as (H1 & H2 & H3). cbn in H1, H2. repeat split; cbn. 1-2: lia. inv H3. easy. 
  Qed. 

  Lemma tape_repr_stay_right rs e h p w :
    rs ≃t(p, w) inr (inr (p, e)) :: h
    -> exists h', valid rewHeadTape (inr (inr (p, e)) :: h) (inr (inr (neutral, e)) :: h')
            /\ (forall h0, valid rewHeadTape (inr (inr (p, e)) :: h) (inr (inr (neutral, e)) :: h0) -> h0 = h')
            /\ rs ≃t(neutral, w) (inr (inr (neutral, e)) :: h').
  Proof.
    intros. destruct e. 
    - cbn in H. destruct_tape_in H. now apply tape_repr_stay_right'. 
    - cbn in H. destruct_tape_in_tidy H. exists (inr (inr (neutral, |_|)) :: E neutral w). split; [ | split]. 
      + apply E_rewrite_blank.
      + intros. apply E_rewrite_blank_unique in H0. now inv H0. 
      + repeat split; cbn; [rewrite E_length | ]; lia.
  Qed. 

  Corollary tape_repr_stay_left ls e h p w :
    ls ≃t(p, w) inr(inr (p, e)) :: h
    -> exists h', valid rewHeadTape (rev (inr (inr (p, e)) :: h)) (rev (inr (inr (neutral, e)) :: h'))
            /\ (forall h0, valid rewHeadTape (rev (inr (inr (p, e)) :: h)) (rev (inr (inr (neutral, e)) :: h0)) -> h0 = h')
            /\ ls ≃t(neutral, w) (inr (inr (neutral, e))) :: h'.
  Proof. 
    intros. specialize (@tape_repr_stay_right ls e h p w H) as (h' & H1 & H3 & H2). 
    exists (map polarityFlipGamma h'). rewrite <- and_assoc. split. 
    - eapply tape_rewrite_symm1 in H1.
      apply tape_rewrite_symm3 in H1.
      split. 
      + cbn [rev].
        unfold polarityRev in H1. rewrite map_rev in H1. rewrite map_involution in H1. 2: apply polarityFlipGamma_involution. 
        destruct e; cbn in H1; apply H1. 
      + intros. specialize (H3 (map polarityFlipGamma h0)).
        rewrite <- involution_invert_eqn2 with (f := map polarityFlipGamma) (a := h0) (b := h'); [reflexivity | apply map_involution, polarityFlipGamma_involution | ]. 
        apply H3. eapply tape_rewrite_symm2. 
        unfold polarityRev. rewrite <- map_rev. apply tape_rewrite_symm3. 
        cbn. rewrite map_involution; [destruct e; cbn; now apply H0 | apply polarityFlipGamma_involution]. 
   - apply tape_repr_polarityFlip in H2. destruct e; cbn in H2; easy. 
  Qed. 

(** *preliminaries for transitions *)

  Definition configState (c : sconfig) := match c with (q, _) => q end. 
  Notation "s '≻' s'" := (halt (configState s) = false /\ sstep s = s') (at level 50). 

  (*decomposition into left, center, right *)
  Lemma tapeToList_lcr sig (tp : tape sig) : tapeToList tp = rev (left tp) ++ (match current tp with Some a => [a] | _ => [] end) ++ right tp. 
  Proof.
    destruct tp; cbn. all: firstorder. 
  Qed. 

  Lemma sizeOfTape_lcr sig (tp : tape sig) : sizeOfTape tp = |left tp| + |right tp| + (if current tp then 1 else 0). 
  Proof. 
    unfold sizeOfTape. rewrite tapeToList_lcr. rewrite !app_length. rewrite rev_length. destruct current; cbn; lia. 
  Qed.

  (*simplification tactic for equations that will arise from inversions*)
  Lemma prod_eq (X Y : Type) (a c : X) (b d : Y) : (a, b) = (c, d) -> a = c /\ b = d. 
  Proof. intros; split; congruence. Qed. 

  Ltac simp_eqn := repeat match goal with
                          | [H : trans (?a, ?b) = ?h1, H1 : trans (?a, ?b) = ?h2 |- _] => assert (h1 = h2) by congruence; clear H1
                          | [H : (?a, ?b) = (?c, ?d) |- _] => specialize (prod_eq H) as (? & ?); clear H
                          | [H : ?a = ?a |- _] => clear H
                          | [H : ?a = _ |- _] => is_var a; rewrite H in *; clear H
                          | [H : Some ?a = Some ?b |- _] => assert (a = b) by congruence; clear H
                          | [H : inr ?a = inr ?b |- _] => assert (a = b) by congruence; clear H
                          | [H : inl ?a = inl ?b |- _] => assert (a = b) by congruence; clear H
                          | [H : ?h1 :: ?a = ?h2 :: ?b |- _] => assert (a = b) by congruence; assert (h1 = h2) by congruence; clear H
                          | [H : rev ?A = _ |- _ ] => is_var A; apply involution_invert_eqn2 in H as ?; [ | involution_simpl]; clear H
                          | [H : _ = rev ?A |- _ ] => is_var A; symmetry in H; apply involution_invert_eqn2 in H; [ | involution_simpl]
                          | [H : context[E _ (S _)] |- _] => cbn in H
                          | [H : context[E _ (wo + _)] |- _] => cbn in H
                    end; try congruence.


  (** *transition rules *)
  (*again, we use inductive definitions *)
  Create HintDb trans discriminated. 
  Definition transRule := Gamma -> Gamma -> Gamma -> Gamma -> Gamma -> Gamma -> Prop.

  (*We structure the rules in several layers: first of all, we have to differentiate whether, for a transition, the Turing machine writes a symbol or not *)
  (*(note that we take the view that the TM can write a symbol even if our transition function returns None (this just means that the symbol under the head remains unchanged) if there is currently a symbol under the head: in this case the written symbol is just the current symbol) *)
  (*in the cases (Some, Some), (Some, None), (None, Some) (denoting the read/write positions of the transition function) the TM writes a symbol; only in the (None, None) case it does not write one *)

  (*rules for the case where the Turing machine writes a symbol *)
  (*shift right rules *)
  (*order of additional arguments: current state, next state, read symbol, written symbol (does not match output of transition function!) *)
  Inductive transSomeRightCenter :  states -> states -> stateSigma -> stateSigma -> transRule :=
    | tsrc q q' (a b : stateSigma) (m1 m2 m3 : stateSigma) p : transSomeRightCenter q q' a b (inr (inr (p, m1))) (inl (q, a)) (inr (inr (p, m2))) (inr (inr (positive, m3))) (inl (q', m1)) (inr (inr (positive, b))).  

  Hint Constructors transSomeRightCenter : trans. 

  Inductive transSomeRightRight : states -> states -> stateSigma -> transRule :=
    | tsrr q q' (a : stateSigma) (m1 m2 m3 : stateSigma) p : transSomeRightRight q q' a (inr (inr (p, m1))) (inr (inr (p, m2))) (inl (q, a)) (inr (inr (positive, m3))) (inr (inr (positive, m1))) (inl (q', m2)). 

  Hint Constructors transSomeRightRight : trans. 

  Inductive transSomeRightLeft : states -> states -> stateSigma -> stateSigma -> transRule :=
    | tsrl q q' (a b : stateSigma) (m1 m2 m3 : stateSigma) p: transSomeRightLeft q q' a b (inl (q, a)) (inr (inr (p, m1))) (inr (inr (p, m2))) (inl (q', m3)) (inr (inr (positive, b))) (inr (inr (positive, m1))). 

  Hint Constructors transSomeRightLeft : trans. 

  (*shift left rules *)
  Inductive transSomeLeftCenter : states -> states -> stateSigma -> stateSigma -> transRule :=
    | tslc q q' (a b : stateSigma) (m1 m2 m3 : stateSigma) p : transSomeLeftCenter q q' a b (inr (inr (p, m1))) (inl (q, a)) (inr (inr (p, m2))) (inr (inr (negative, b))) (inl (q', m2)) (inr (inr (negative, m3))). 

  Hint Constructors transSomeLeftCenter : trans. 

  Inductive transSomeLeftLeft : states -> states -> stateSigma -> transRule :=
    | tsll q q' (a : stateSigma) (m1 m2 m3 : stateSigma) p : transSomeLeftLeft q q' a (inl (q, a)) (inr (inr (p, m1))) (inr (inr (p, m2))) (inl (q', m1)) (inr (inr (negative, m2))) (inr (inr(negative, m3))). 

  Hint Constructors transSomeLeftLeft : trans. 

  Inductive transSomeLeftRight : states -> states -> stateSigma -> stateSigma -> transRule :=
    | tslr q q' (a b : stateSigma) (m1 m2 m3 : stateSigma) p : transSomeLeftRight q q' a b (inr (inr (p, m1))) (inr (inr (p, m2))) (inl (q, a)) (inr (inr (negative, m2))) (inr (inr (negative, b))) (inl (q', m3)).

  Hint Constructors transSomeLeftRight : trans. 

  (*stay rules *)
  
  Inductive transSomeStayCenter : states -> states -> stateSigma -> stateSigma -> transRule :=
    | tssc q q' (a b : stateSigma) (m1 m2 : stateSigma) p : transSomeStayCenter q q' a b (inr (inr (p, m1))) (inl (q, a)) (inr (inr (p, m2))) (inr (inr (neutral, m1))) (inl (q', b)) (inr (inr (neutral, m2))). 

  Hint Constructors transSomeStayCenter : trans. 

  Inductive transSomeStayLeft : states -> states -> stateSigma -> stateSigma -> transRule :=
    | tssl q q' (a b : stateSigma) (m1 m2 : stateSigma) p : transSomeStayLeft q q' a b (inl (q, a)) (inr (inr (p, m1))) (inr (inr (p, m2))) (inl (q', b)) (inr (inr (neutral, m1))) (inr (inr (neutral, m2))). 

  Hint Constructors transSomeStayLeft : trans. 

  Inductive transSomeStayRight : states -> states -> stateSigma -> stateSigma -> transRule :=
    | tssr q q' (a b : stateSigma) (m1 m2 : stateSigma) p : transSomeStayRight q q' a b (inr (inr (p, m1))) (inr (inr (p, m2))) (inl (q, a)) (inr (inr (neutral, m1))) (inr (inr (neutral, m2))) (inl (q', b)). 

  Hint Constructors transSomeStayRight : trans. 

  (* bundling predicates *)

  (*we first group together according to where the state symbol is: left/right/center *)
  (*note that we have to differentiate between the three cases (Some, Some), (Some, None), (None, Some) *)

  (*Some, Some *)
  Inductive transSomeSomeLeft : states -> transRule :=
  | transSSLeftLeftC q q' (a b : Sigma) γ2 γ3 γ4 γ5 γ6: trans (q, Some a) = (q', (Some b, R)) -> transSomeLeftLeft q q' (Some a) (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6 -> transSomeSomeLeft q (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6
  | transSSRightLeftC q q' (a b : Sigma) γ2 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some b, L)) ->  transSomeRightLeft q q' (Some a) (Some b) (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6 -> transSomeSomeLeft q (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6
  | transSSStayLeftC q q' (a b : Sigma) γ2 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some b, N)) -> transSomeStayLeft q q' (Some a) (Some b) (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6 -> transSomeSomeLeft q (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6. 

  Hint Constructors transSomeSomeLeft : trans. 

  Inductive transSomeSomeRight : states -> transRule :=
  | transSSLeftRightC q q' (a b: Sigma) γ1 γ2 γ4 γ5 γ6: trans (q, Some a) = (q', (Some b, R)) -> transSomeLeftRight q q' (Some a) (Some b) γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6 -> transSomeSomeRight q γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6
  | transSSRightRightC q q' (a b : Sigma) γ1 γ2 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some b, L)) -> transSomeRightRight q q' (Some a) γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6 -> transSomeSomeRight q γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6
  | transSSStayRightC q q' (a b : Sigma)  γ1 γ2 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some b, N)) -> transSomeStayRight q q' (Some a) (Some b) γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6 -> transSomeSomeRight q γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6. 

  Hint Constructors transSomeSomeRight : trans. 

  Inductive transSomeSomeCenter : states -> transRule :=
  | transSSLeftCenterC q q' (a b: Sigma) γ1 γ3 γ4 γ5 γ6: trans (q, Some a) = (q', (Some b, R)) -> transSomeLeftCenter q q' (Some a) (Some b) γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6 -> transSomeSomeCenter q γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6
  | transSSRightCenterC q q' (a b: Sigma) γ1 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some b, L)) -> transSomeRightCenter q q' (Some a) (Some b) γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6 -> transSomeSomeCenter q γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6
  | transSSStayCenterC q q' (a b: Sigma) γ1 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some b, N)) -> transSomeStayCenter q q' (Some a) (Some b) γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6 -> transSomeSomeCenter q γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6. 

  Hint Constructors transSomeSomeCenter : trans.

  (*None, Some *)
  Inductive transNoneSomeLeft : states -> transRule :=
  | transNSLeftLeftC q q' (b : Sigma) γ2 γ3 γ4 γ5 γ6: trans (q, None) = (q', (Some b, R)) -> transSomeLeftLeft q q' |_| (inl (q, |_|)) γ2 γ3 γ4 γ5 γ6 -> transNoneSomeLeft q (inl (q, |_|)) γ2 γ3 γ4 γ5 γ6
  | transNSRightLeftC q q' (b : Sigma) γ2 γ3 γ4 γ5 γ6 : trans (q, |_|) = (q', (Some b, L)) ->  transSomeRightLeft q q' (|_|) (Some b) (inl (q, |_|)) γ2 γ3 γ4 γ5 γ6 -> transNoneSomeLeft q (inl (q, |_|)) γ2 γ3 γ4 γ5 γ6
  | transNSStayLeftC q q' (b : Sigma) γ2 γ3 γ4 γ5 γ6 : trans (q, |_|) = (q', (Some b, N)) -> transSomeStayLeft q q' (|_|) (Some b) (inl (q, |_|)) γ2 γ3 γ4 γ5 γ6 -> transNoneSomeLeft q (inl (q, |_|)) γ2 γ3 γ4 γ5 γ6. 

  Hint Constructors transNoneSomeLeft : trans. 

  Inductive transNoneSomeRight : states -> transRule :=
  | transNSLeftRightC q q' (b: Sigma) γ1 γ2 γ4 γ5 γ6: trans (q, |_|) = (q', (Some b, R)) -> transSomeLeftRight q q' (|_|) (Some b) γ1 γ2 (inl (q, |_|)) γ4 γ5 γ6 -> transNoneSomeRight q γ1 γ2 (inl (q, |_|)) γ4 γ5 γ6
  | transNSRightRightC q q' (b : Sigma) γ1 γ2 γ4 γ5 γ6 : trans (q, |_|) = (q', (Some b, L)) -> transSomeRightRight q q' (|_|) γ1 γ2 (inl (q, |_|)) γ4 γ5 γ6 -> transNoneSomeRight q γ1 γ2 (inl (q, |_|)) γ4 γ5 γ6
  | transNSStayRightC q q' (b : Sigma)  γ1 γ2 γ4 γ5 γ6 : trans (q, |_|) = (q', (Some b, N)) -> transSomeStayRight q q' (|_|) (Some b) γ1 γ2 (inl (q, |_|)) γ4 γ5 γ6 -> transNoneSomeRight q γ1 γ2 (inl (q, |_|)) γ4 γ5 γ6. 

  Hint Constructors transNoneSomeRight : trans. 

  Inductive transNoneSomeCenter : states -> transRule :=
  | transNSLeftCenterC q q' (b: Sigma) γ1 γ3 γ4 γ5 γ6: trans (q, |_|) = (q', (Some b, R)) -> transSomeLeftCenter q q' (|_|) (Some b) γ1 (inl (q, |_|)) γ3 γ4 γ5 γ6 -> transNoneSomeCenter q γ1 (inl (q, |_|)) γ3 γ4 γ5 γ6
  | transNSRightCenterC q q' (b: Sigma) γ1 γ3 γ4 γ5 γ6 : trans (q, |_|) = (q', (Some b, L)) -> transSomeRightCenter q q' (|_|) (Some b) γ1 (inl (q, |_|)) γ3 γ4 γ5 γ6 -> transNoneSomeCenter q γ1 (inl (q, |_|)) γ3 γ4 γ5 γ6
  | transNSStayCenterC q q' (b: Sigma) γ1 γ3 γ4 γ5 γ6 : trans (q, |_|) = (q', (Some b, N)) -> transSomeStayCenter q q' (|_|) (Some b) γ1 (inl (q, |_|)) γ3 γ4 γ5 γ6 -> transNoneSomeCenter q γ1 (inl (q, |_|)) γ3 γ4 γ5 γ6. 

  Hint Constructors transNoneSomeCenter : trans.

  (*Some, None  *)
  Inductive transSomeNoneLeft : states -> transRule :=
  | transSNLeftLeftC q q' (a : Sigma) γ2 γ3 γ4 γ5 γ6: trans (q, Some a) = (q', (None, R)) -> transSomeLeftLeft q q' (Some a) (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6 -> transSomeNoneLeft q (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6
  | transSNRightLeftC q q' (a : Sigma) γ2 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (None, L)) ->  transSomeRightLeft q q' (Some a) (Some a) (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6 -> transSomeNoneLeft q (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6
  | transSNStayLeftC q q' (a : Sigma) γ2 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (None, N)) -> transSomeStayLeft q q' (Some a) (Some a) (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6 -> transSomeNoneLeft q (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6. 

  Hint Constructors transSomeNoneLeft : trans. 

  Inductive transSomeNoneRight : states -> transRule :=
  | transSNLeftRightC q q' (a : Sigma) γ1 γ2 γ4 γ5 γ6: trans (q, Some a) = (q', (None, R)) -> transSomeLeftRight q q' (Some a) (Some a) γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6 -> transSomeNoneRight q γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6
  | transSNRightRightC q q' (a : Sigma) γ1 γ2 γ4 γ5 γ6 : trans (q, Some a) = (q', (None, L)) -> transSomeRightRight q q' (Some a) γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6 -> transSomeNoneRight q γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6
  | transSNStayRightC q q' (a : Sigma)  γ1 γ2 γ4 γ5 γ6 : trans (q, Some a) = (q', (None, N)) -> transSomeStayRight q q' (Some a) (Some a) γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6 -> transSomeNoneRight q γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6. 

  Hint Constructors transSomeNoneRight : trans. 

  Inductive transSomeNoneCenter : states -> transRule :=
  | transSNLeftCenterC q q' (a: Sigma) γ1 γ3 γ4 γ5 γ6: trans (q, Some a) = (q', (None, R)) -> transSomeLeftCenter q q' (Some a) (Some a) γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6 -> transSomeNoneCenter q γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6
  | transSNRightCenterC q q' (a: Sigma) γ1 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (None, L)) -> transSomeRightCenter q q' (Some a) (Some a) γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6 -> transSomeNoneCenter q γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6
  | transSNStayCenterC q q' (a: Sigma) γ1 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (None, N)) -> transSomeStayCenter q q' (Some a) (Some a) γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6 -> transSomeNoneCenter q γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6. 

  Hint Constructors transSomeNoneCenter : trans.


  (* finally, also group those three cases together *)
  Inductive transSomeSome : states -> transRule :=
  | transSSLeft q γ1 γ2 γ3 γ4 γ5 γ6 : transSomeSomeLeft q γ1 γ2 γ3 γ4 γ5 γ6 -> transSomeSome q γ1 γ2 γ3 γ4 γ5 γ6
  | transSSRight q γ1 γ2 γ3 γ4 γ5 γ6 : transSomeSomeRight q γ1 γ2 γ3 γ4 γ5 γ6 -> transSomeSome q γ1 γ2 γ3 γ4 γ5 γ6
  | transSSCenter q γ1 γ2 γ3 γ4 γ5 γ6 : transSomeSomeCenter q γ1 γ2 γ3 γ4 γ5 γ6 -> transSomeSome q γ1 γ2 γ3 γ4 γ5 γ6.

  Hint Constructors transSomeSome : trans.

  Inductive transNoneSome : states -> transRule :=
  | transNSLeft q γ1 γ2 γ3 γ4 γ5 γ6 : transNoneSomeLeft q γ1 γ2 γ3 γ4 γ5 γ6 -> transNoneSome q γ1 γ2 γ3 γ4 γ5 γ6
  | transNSRight q γ1 γ2 γ3 γ4 γ5 γ6 : transNoneSomeRight q γ1 γ2 γ3 γ4 γ5 γ6 -> transNoneSome q γ1 γ2 γ3 γ4 γ5 γ6
  | transNSCenter q γ1 γ2 γ3 γ4 γ5 γ6 : transNoneSomeCenter q γ1 γ2 γ3 γ4 γ5 γ6 -> transNoneSome q γ1 γ2 γ3 γ4 γ5 γ6.

  Hint Constructors transNoneSome : trans.
  
  Inductive transSomeNone : states -> transRule :=
  | transSNLeft q γ1 γ2 γ3 γ4 γ5 γ6 : transSomeNoneLeft q γ1 γ2 γ3 γ4 γ5 γ6 -> transSomeNone q γ1 γ2 γ3 γ4 γ5 γ6
  | transSNRight q γ1 γ2 γ3 γ4 γ5 γ6 : transSomeNoneRight q γ1 γ2 γ3 γ4 γ5 γ6 -> transSomeNone q γ1 γ2 γ3 γ4 γ5 γ6
  | transSNCenter q γ1 γ2 γ3 γ4 γ5 γ6 : transSomeNoneCenter q γ1 γ2 γ3 γ4 γ5 γ6 -> transSomeNone q γ1 γ2 γ3 γ4 γ5 γ6.

  Hint Constructors transSomeNone : trans.

  (*the special case of (None, None) needs extra care as the Turing machine doesn't write any symbol *) 
  (*the structure of the rules is the same for this case, but we need a more fine-grained definition of the base rules because of the special handling if we are the border of the visited tape region *)

  (*shift right rules *)
  Inductive transNoneRightCenter :  states -> states -> transRule :=
  | tnrc1 q q' (m : stateSigma) p : transNoneRightCenter q q' (inr (inr (p, |_|))) (inl (q, |_|)) (inr (inr (p, m))) (inr (inr (neutral, |_|))) (inl (q', |_|)) (inr (inr (neutral, m)))
  | tnrc2 q q' (σ : Sigma) (m: stateSigma) p : transNoneRightCenter q q' (inr (inr (p, Some σ))) (inl (q, |_|)) (inr (inr (p, |_|))) (inr (inr (positive, m))) (inl (q', Some σ)) (inr (inr (positive, |_|))). 

  Hint Constructors transNoneRightCenter : trans. 

  Inductive transNoneRightRight : states -> states -> transRule :=
  | tnrr1 q q' p p': transNoneRightRight q q' (inr (inr (p, |_|))) (inr (inr (p, |_|))) (inl (q, |_|)) (inr (inr (p', |_|))) (inr (inr (p', |_|))) (inl (q', |_|))
  | tnrr2 q q' σ p p': transNoneRightRight q q' (inr (inr (p, |_|))) (inr (inr (p,Some σ))) (inl (q, |_|)) (inr (inr (p', |_|))) (inr (inr (p', |_|))) (inl (q', Some σ))
  | tnrr3 q q' σ1 σ2 (m1 : stateSigma) p : transNoneRightRight q q' (inr (inr (p, Some σ1))) (inr (inr (p, Some σ2))) (inl (q, |_|)) (inr (inr (positive, m1))) (inr (inr (positive, Some σ1))) (inl (q', Some σ2)).

  Hint Constructors transNoneRightRight : trans. 

  Inductive transNoneRightLeft : states -> states -> transRule :=
  | tnrl1 q q' (m : stateSigma) p p': transNoneRightLeft q q' (inl (q, |_|)) (inr (inr (p, |_|))) (inr (inr (p, |_|))) (inl (q', m)) (inr (inr (p', |_|))) (inr (inr (p', |_|)))
  | tnrl2 q q' (m : stateSigma) σ p p' : transNoneRightLeft q q' (inl (q, |_|)) (inr (inr (p, Some σ))) (inr (inr (p, m))) (inl (q', |_|)) (inr (inr (p', Some σ))) (inr (inr (p', m))).  

  Hint Constructors transNoneRightLeft : trans. 

  (*shift left rules *)
  Inductive transNoneLeftCenter : states -> states -> transRule :=
  | tnlc1 q q' (m : stateSigma) p : transNoneLeftCenter q q' (inr (inr (p, m))) (inl (q, |_|)) (inr (inr (p, |_|))) (inr (inr (neutral, m))) (inl (q', |_|)) (inr (inr (neutral, |_|)))
  | tnlc2 q q' (m : stateSigma) σ p : transNoneLeftCenter q q' (inr (inr (p, |_|))) (inl (q, |_|)) (inr (inr (p, Some σ))) (inr (inr (negative, |_|))) (inl (q', Some σ)) (inr (inr (negative, m))). 

  Hint Constructors transNoneLeftCenter : trans. 

  Inductive transNoneLeftLeft : states -> states -> transRule :=
  | tnll1 q q' p p': transNoneLeftLeft q q' (inl (q, |_|)) (inr (inr (p, |_|))) (inr (inr (p, |_|))) (inl (q', |_|)) (inr (inr (p', |_|))) (inr (inr (p', |_|)))
  | tnll2 q q' σ p p': transNoneLeftLeft q q' (inl (q, |_|)) (inr (inr (p, Some σ))) (inr (inr (p, |_|))) (inl (q', Some σ)) (inr (inr (p', |_|))) (inr (inr (p', |_|)))
  | tnll3 q q' σ1 σ2 (m : stateSigma) p : transNoneLeftLeft q q' (inl (q, |_|)) (inr (inr (p, Some σ1))) (inr (inr (p, Some σ2))) (inl (q', Some σ1)) (inr (inr (negative, Some σ2))) (inr (inr (negative, m))).

  Hint Constructors transNoneLeftLeft : trans. 

  Inductive transNoneLeftRight : states -> states -> transRule :=
  | tnlr1 q q' (m : stateSigma) p p': transNoneLeftRight q q' (inr (inr (p,  |_|))) (inr (inr (p, |_|))) (inl (q, |_|)) (inr (inr (p', |_|))) (inr (inr (p', |_|))) (inl (q', m))
  | tnlr2 q q' (m1 : stateSigma) σ p : transNoneLeftRight q q' (inr (inr (p, m1))) (inr (inr (p, Some σ))) (inl (q, |_|)) (inr (inr (neutral, m1))) (inr (inr (neutral, Some σ))) (inl (q', |_|)). 

  Hint Constructors transNoneLeftRight : trans. 

  (*stay rules *)
  Inductive transNoneStayCenter : states -> states -> transRule :=
  | tnsc1 q q' (m : stateSigma) p : transNoneStayCenter q q' (inr (inr (p, m))) (inl (q, |_|)) (inr (inr (p, |_|))) (inr (inr (neutral, m))) (inl (q', |_|)) (inr (inr (neutral, |_|)))
  | tnsc2 q q' (m : stateSigma) p : transNoneStayCenter q q' (inr (inr (p, |_|))) (inl (q, |_|)) (inr (inr (p, m))) (inr (inr (neutral, |_|))) (inl (q', |_|)) (inr (inr (neutral, m))). 

  Hint Constructors transNoneStayCenter : trans. 

  Inductive transNoneStayLeft : states -> states -> transRule :=
  | tnsl1 q q' σ (m : stateSigma) p : transNoneStayLeft q q' (inl (q, |_|)) (inr (inr (p, Some σ))) (inr (inr (p, m))) (inl (q', |_|)) (inr (inr (neutral, Some σ))) (inr (inr (neutral, m)))
  | tnsl2 q q' p: transNoneStayLeft q q' (inl (q, |_|)) (inr (inr (p, |_|))) (inr (inr (p, |_|))) (inl (q', |_|)) (inr (inr (neutral, |_|))) (inr (inr (neutral, |_|))).

  Hint Constructors transNoneStayLeft : trans. 

  Inductive transNoneStayRight : states -> states ->  transRule :=
  | tnsr1 q q' σ (m : stateSigma) p : transNoneStayRight q q' (inr (inr (p, m))) (inr (inr (p, Some σ))) (inl (q, |_|)) (inr (inr (neutral, m))) (inr (inr (neutral, Some σ))) (inl (q', |_|))
  | tnsr2 q q' p : transNoneStayRight q q' (inr (inr (p, |_|))) (inr (inr (p, |_|))) (inl (q, |_|)) (inr (inr (neutral, |_|))) (inr (inr (neutral, |_|))) (inl (q', |_|)). 

  Hint Constructors transNoneStayRight : trans. 


  Inductive transNoneNoneLeft : states -> transRule :=
  | transNNLeftLeftC q q' γ2 γ3 γ4 γ5 γ6: trans (q, None) = (q', (None, R)) -> transNoneLeftLeft q q' (inl (q, |_|)) γ2 γ3 γ4 γ5 γ6 -> transNoneNoneLeft q (inl (q, |_|)) γ2 γ3 γ4 γ5 γ6
  | transNNRightLeftC q q' γ2 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (None, L)) ->  transNoneRightLeft q q' (inl (q, |_|)) γ2 γ3 γ4 γ5 γ6 -> transNoneNoneLeft q (inl (q, |_|)) γ2 γ3 γ4 γ5 γ6
  | transNNStayLeftC q q' γ2 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (None, N)) -> transNoneStayLeft q q' (inl (q, |_|)) γ2 γ3 γ4 γ5 γ6 -> transNoneNoneLeft q (inl (q, |_|)) γ2 γ3 γ4 γ5 γ6. 

  Hint Constructors transNoneNoneLeft : trans. 

  Inductive transNoneNoneRight : states -> transRule :=
  | transNNLeftRightC q q' γ1 γ2 γ4 γ5 γ6: trans (q, None) = (q', (None, R)) -> transNoneLeftRight q q' γ1 γ2 (inl (q, |_|)) γ4 γ5 γ6 -> transNoneNoneRight q γ1 γ2 (inl (q, |_|)) γ4 γ5 γ6
  | transNNRightRightC q q' γ1 γ2 γ4 γ5 γ6 : trans (q, None) = (q', (None, L)) -> transNoneRightRight q q' γ1 γ2 (inl (q, |_|)) γ4 γ5 γ6 -> transNoneNoneRight q γ1 γ2 (inl (q, |_|)) γ4 γ5 γ6
  | transNNStayRightC q q' γ1 γ2 γ4 γ5 γ6 : trans (q, None) = (q', (None, N)) -> transNoneStayRight q q' γ1 γ2 (inl (q, |_|)) γ4 γ5 γ6 -> transNoneNoneRight q γ1 γ2 (inl (q, |_|)) γ4 γ5 γ6. 

  Hint Constructors transNoneNoneRight : trans. 

  Inductive transNoneNoneCenter : states -> transRule :=
  | transNNLeftCenterC q q' γ1 γ3 γ4 γ5 γ6: trans (q, None) = (q', (None, R)) -> transNoneLeftCenter q q' γ1 (inl (q, |_|)) γ3 γ4 γ5 γ6 -> transNoneNoneCenter q γ1 (inl (q, |_|)) γ3 γ4 γ5 γ6
  | transNNRightCenterC q q' γ1 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (None, L)) -> transNoneRightCenter q q' γ1 (inl (q, |_|)) γ3 γ4 γ5 γ6 -> transNoneNoneCenter q γ1 (inl (q, |_|)) γ3 γ4 γ5 γ6
  | transNNStayCenterC q q' γ1 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (None, N)) -> transNoneStayCenter q q' γ1 (inl (q, |_|)) γ3 γ4 γ5 γ6 -> transNoneNoneCenter q γ1 (inl (q, |_|)) γ3 γ4 γ5 γ6. 

  Hint Constructors transNoneNoneCenter : trans. 

  Inductive transNoneNone : states -> transRule :=
  | transNNLeft q γ1 γ2 γ3 γ4 γ5 γ6 : transNoneNoneLeft q γ1 γ2 γ3 γ4 γ5 γ6 -> transNoneNone q γ1 γ2 γ3 γ4 γ5 γ6
  | transNNRight q γ1 γ2 γ3 γ4 γ5 γ6 : transNoneNoneRight q γ1 γ2 γ3 γ4 γ5 γ6 -> transNoneNone q γ1 γ2 γ3 γ4 γ5 γ6
  | transNNStay q γ1 γ2 γ3 γ4 γ5 γ6 : transNoneNoneCenter q γ1 γ2 γ3 γ4 γ5 γ6 -> transNoneNone q γ1 γ2 γ3 γ4 γ5 γ6.

  Hint Constructors transNoneNone : trans. 


  (*finally, group together all of the four cases *)
  Inductive transRules  : transRule :=
  | transSomeSomeC q γ1 γ2 γ3 γ4 γ5 γ6: halt q = false -> transSomeSome q γ1 γ2 γ3 γ4 γ5 γ6 -> transRules γ1 γ2 γ3 γ4 γ5 γ6
  | transSomeNoneC q γ1 γ2 γ3 γ4 γ5 γ6 : halt q = false -> transSomeNone q γ1 γ2 γ3 γ4 γ5 γ6 -> transRules γ1 γ2 γ3 γ4 γ5 γ6
  | transNoneSomeC q γ1 γ2 γ3 γ4 γ5 γ6 : halt q = false -> transNoneSome q γ1 γ2 γ3 γ4 γ5 γ6 -> transRules γ1 γ2 γ3 γ4 γ5 γ6
  | transNoneNoneC q γ1 γ2 γ3 γ4 γ5 γ6 : halt q = false -> transNoneNone q γ1 γ2 γ3 γ4 γ5 γ6 -> transRules γ1 γ2 γ3 γ4 γ5 γ6.

  Hint Constructors transRules : trans. 

  Ltac transRules_inv1 :=
    match goal with
    | [H : transRules _ _ _ _ _ _ |- _] => inv H
    end.

  (*full inverions - very (!) costly *)
  Ltac transRules_inv2_once := match goal with
      | [H : transRules _ _ _ _ _ _ |- _] => inv H
      | [H : context[transSomeSome] |- _ ] => inv H
      | [H : context[transNoneSome] |- _ ] => inv H
      | [H : context[transSomeNone] |- _ ] => inv H
      | [H : context[transNoneNone] |- _ ] => inv H
      | [H : context[transSomeSomeLeft] |- _ ] => inv H
      | [H : context[transSomeSomeRight] |- _] => inv H
      | [H : context[transSomeSomeCenter] |- _ ] => inv H
      | [H : context[transSomeNoneLeft] |- _ ] => inv H
      | [H : context[transSomeNoneRight] |- _] => inv H
      | [H : context[transSomeNoneCenter] |- _ ] => inv H
      | [H : context[transNoneSomeLeft] |- _ ] => inv H
      | [H : context[transNoneSomeRight] |- _] => inv H
      | [H : context[transNoneSomeCenter] |- _ ] => inv H
      | [H : context[transSomeStayLeft] |- _] => inv H
      | [H : context[transSomeStayCenter] |- _ ] => inv H
      | [H : context[transSomeStayRight] |- _ ] => inv H
      | [H : context[transSomeLeftCenter] |- _ ] => inv H
      | [H : context[transSomeLeftLeft] |- _] => inv H
      | [H : context[transSomeLeftRight] |- _] => inv H
      | [H : context[transSomeRightLeft] |- _] => inv H
      | [H : context[transSomeRightRight] |- _] => inv H
      | [H : context[transSomeRightCenter] |- _] => inv H
      | [H : context[transNoneNoneLeft] |- _ ] => inv H
      | [H : context[transNoneNoneRight] |- _] => inv H
      | [H : context[transNoneNoneCenter] |- _ ] => inv H
      | [H : context[transNoneStayLeft] |- _] => inv H
      | [H : context[transNoneStayCenter] |- _ ] => inv H
      | [H : context[transNoneStayRight] |- _ ] => inv H
      | [H : context[transNoneLeftCenter] |- _ ] => inv H
      | [H : context[transNoneLeftLeft] |- _] => inv H
      | [H : context[transNoneLeftRight] |- _] => inv H
      | [H : context[transNoneRightLeft] |- _] => inv H
      | [H : context[transNoneRightRight] |- _] => inv H
      | [H : context[transNoneRightCenter] |- _] => inv H
    end. 

  Ltac transRules_inv2 := repeat transRules_inv2_once. 

(*   (*manual inversion lemmas because of performance *) *)
(*   Lemma transSomeSome_inv1 q q0 m γ2 γ3 γ4 γ5 γ6 : transSomeSome q (inl (q0, m)) γ2 γ3 γ4 γ5 γ6 -> q0 = q /\ (exists σ, m = Some σ) /\ exists q' m', γ4 = inl (q', m') /\ transSomeSomeLeft q (inl (q, m)) γ2 γ3 (inl (q', m')) γ5 γ6. *)
(*   Proof. *)
(*     intros. inv H. *)
(*     + inv H0; (split; [ reflexivity | split; [eauto | ] ]; exists q'; transRules_inv2_once; eauto with trans).   *)
(*     + transRules_inv2.  *)
(*     + transRules_inv2.  *)
(*   Qed.  *)

(*   Lemma transSomeSome_inv2 q q0 m γ1 γ3 γ4 γ5 γ6 : transSomeSome q γ1 (inl (q0, m)) γ3 γ4 γ5 γ6 -> q0 = q /\ (exists σ, m = Some σ) /\ exists q' m', γ5 = inl (q', m') /\ transSomeSomeCenter q γ1 (inl (q, m)) γ3 γ4 (inl (q', m')) γ6. *)
(*   Proof. *)
(*     intros. inv H.  *)
(*     + transRules_inv2.  *)
(*     + transRules_inv2. *)
(*     + inv H0; (split; [ reflexivity | split; [eauto | ]]; exists q'; transRules_inv2_once; eauto with trans). *)
(*   Qed.  *)

(*   Lemma transSomeSome_inv3 q q0 m γ1 γ2 γ4 γ5 γ6 : transSomeSome q γ1 γ2 (inl (q0, m)) γ4 γ5 γ6 -> q0 = q /\ (exists σ, m = Some σ) /\ exists q' m', γ6 = inl (q', m') /\ transSomeSomeRight q γ1 γ2 (inl (q, m)) γ4 γ5 (inl (q', m')).  *)
(*   Proof.  *)
(*     intros. inv H.  *)
(*     + transRules_inv2.  *)
(*     + inv H0; (split; [ reflexivity | split; [eauto | ]]; exists q'; transRules_inv2_once; eauto with trans). *)
(*     + transRules_inv2. *)
(*   Qed.  *)

(*   Lemma transSomeNone_inv1 q q0 m γ2 γ3 γ4 γ5 γ6 : transSomeNone q (inl (q0, m)) γ2 γ3 γ4 γ5 γ6 -> q0 = q /\ (exists σ, m = Some σ) /\ exists q' m', γ4 = inl (q', m') /\ transSomeNoneLeft q (inl (q, m)) γ2 γ3 (inl (q', m')) γ5 γ6. *)
(*   Proof. *)
(*     intros. inv H. *)
(*     + inv H0; (split; [ reflexivity | split; [eauto | ] ]; exists q'; transRules_inv2_once; eauto with trans).   *)
(*     + transRules_inv2.  *)
(*     + transRules_inv2.  *)
(*   Qed.  *)

(*   Lemma transSomeNone_inv2 q q0 m γ1 γ3 γ4 γ5 γ6 : transSomeNone q γ1 (inl (q0, m)) γ3 γ4 γ5 γ6 -> q0 = q /\ (exists σ, m = Some σ) /\ exists q' m', γ5 = inl (q', m') /\ transSomeNoneCenter q γ1 (inl (q, m)) γ3 γ4 (inl (q', m')) γ6. *)
(*   Proof. *)
(*     intros. inv H.  *)
(*     + transRules_inv2.  *)
(*     + transRules_inv2. *)
(*     + inv H0; (split; [ reflexivity | split; [eauto | ]]; exists q'; transRules_inv2_once; eauto with trans). *)
(*   Qed.  *)

(*   Lemma transSomeNone_inv3 q q0 m γ1 γ2 γ4 γ5 γ6 : transSomeNone q γ1 γ2 (inl (q0, m)) γ4 γ5 γ6 -> q0 = q /\ (exists σ, m = Some σ) /\ exists q' m', γ6 = inl (q', m') /\ transSomeNoneRight q γ1 γ2 (inl (q, m)) γ4 γ5 (inl (q', m')).  *)
(*   Proof.  *)
(*     intros. inv H.  *)
(*     + transRules_inv2.  *)
(*     + inv H0; (split; [ reflexivity | split; [eauto | ]]; exists q'; transRules_inv2_once; eauto with trans). *)
(*     + transRules_inv2. *)
(*   Qed. *)

(*   Lemma transNoneSome_inv1 q q0 m γ2 γ3 γ4 γ5 γ6 : transNoneSome q (inl (q0, m)) γ2 γ3 γ4 γ5 γ6 -> q0 = q /\ m = |_| /\ exists q' m', γ4 = inl (q', m') /\ transNoneSomeLeft q (inl (q, m)) γ2 γ3 (inl (q', m')) γ5 γ6. *)
(*   Proof. *)
(*     intros. inv H. *)
(*     + inv H0; (split; [ reflexivity | split; [ reflexivity | ]]; exists q'; transRules_inv2_once; eauto with trans).   *)
(*     + transRules_inv2.  *)
(*     + transRules_inv2.  *)
(*   Qed.  *)

(*   Lemma transNoneSome_inv2 q q0 m γ1 γ3 γ4 γ5 γ6 : transNoneSome q γ1 (inl (q0, m)) γ3 γ4 γ5 γ6 -> q0 = q /\ m = |_| /\  exists q' m', γ5 = inl (q', m') /\ transNoneSomeCenter q γ1 (inl (q, m)) γ3 γ4 (inl (q', m')) γ6. *)
(*   Proof. *)
(*     intros. inv H.  *)
(*     + transRules_inv2.  *)
(*     + transRules_inv2. *)
(*     + inv H0; (split; [ reflexivity | split; [reflexivity | ]]; exists q'; transRules_inv2_once; eauto with trans). *)
(*   Qed.  *)

(*   Lemma transNoneSome_inv3 q q0 m γ1 γ2 γ4 γ5 γ6 : transNoneSome q γ1 γ2 (inl (q0, m)) γ4 γ5 γ6 -> q0 = q /\ m = |_| /\ exists q' m', γ6 = inl (q', m') /\ transNoneSomeRight q γ1 γ2 (inl (q, m)) γ4 γ5 (inl (q', m')).  *)
(*   Proof.  *)
(*     intros. inv H.  *)
(*     + transRules_inv2.  *)
(*     + inv H0; (split; [ reflexivity | split; [reflexivity | ]]; exists q'; transRules_inv2_once; eauto with trans). *)
(*     + transRules_inv2. *)
(*   Qed. *)

(* Lemma transNoneNone_inv1 q q0 m γ2 γ3 γ4 γ5 γ6 : transNoneNone q (inl (q0, m)) γ2 γ3 γ4 γ5 γ6 -> q0 = q /\ m = |_| /\ exists q' m', γ4 = inl (q', m') /\ transNoneNoneLeft q (inl (q, m)) γ2 γ3 (inl (q', m')) γ5 γ6. *)
(*   Proof. *)
(*     intros. inv H. *)
(*     + inv H0; (split; [ reflexivity | split; [reflexivity | ]]; exists q'; transRules_inv2_once; eauto with trans).   *)
(*     + transRules_inv2.  *)
(*     + transRules_inv2.  *)
(*   Qed.  *)

(*   Lemma transNoneNone_inv2 q q0 m γ1 γ3 γ4 γ5 γ6 : transNoneNone q γ1 (inl (q0, m)) γ3 γ4 γ5 γ6 -> q0 = q /\ m = |_| /\ exists q' m', γ5 = inl (q', m') /\ transNoneNoneCenter q γ1 (inl (q, m)) γ3 γ4 (inl (q', m')) γ6. *)
(*   Proof. *)
(*     intros. inv H.  *)
(*     + transRules_inv2.  *)
(*     + transRules_inv2. *)
(*     + inv H0; (split; [ reflexivity | split; [reflexivity | ]]; exists q'; transRules_inv2_once; eauto with trans). *)
(*   Qed.  *)

(*   Lemma transNoneNone_inv3 q q0 m γ1 γ2 γ4 γ5 γ6 : transNoneNone q γ1 γ2 (inl (q0, m)) γ4 γ5 γ6 -> q0 = q /\ m = |_| /\ exists q' m', γ6 = inl (q', m') /\ transNoneNoneRight q γ1 γ2 (inl (q, m)) γ4 γ5 (inl (q', m')).  *)
(*   Proof.  *)
(*     intros. inv H.  *)
(*     + transRules_inv2.  *)
(*     + inv H0; (split; [ reflexivity | split; [reflexivity | ]]; exists q'; transRules_inv2_once; eauto with trans). *)
(*     + transRules_inv2. *)
(*   Qed. *)

(*   Ltac inv_eqn H := match type of H with *)
(*                     | ?h = ?h' => is_var h; rewrite !H in *; clear H *)
(*                     | ?h = ?h' => is_var h'; rewrite <- !H in *; clear H *)
(*                     | _ => inv H *)
(*                      end.  *)

(*   (*inversions for the second level of the hierarchy of predicates *) *)
(*   Ltac inv_trans_prim := repeat match goal with *)
(*         | [H : transSomeSome _ _ _ (inl (_, _)) _ _ _ |- _] => let Heqn := fresh "eqn" in let Heqn' := fresh "eqn" in apply transSomeSome_inv3 in H as (<- & (? & Heqn') & (? & ? & Heqn & ?)); inv_eqn Heqn; inv_eqn Heqn' *)
(*         | [H : transSomeSome _ (inl (_, _)) _ _ _ _ _ |- _] => let Heqn := fresh "eqn" in let Heqn' := fresh "eqn" in apply transSomeSome_inv1 in H as (<- & (? & Heqn') & (? & ? & Heqn & ?)); inv_eqn Heqn; inv_eqn Heqn' *)
(*         | [H : transSomeSome _ _ (inl (_, _)) _ _ _ _ |- _] => let Heqn := fresh "eqn" in let Heqn' := fresh "eqn" in apply transSomeSome_inv2 in H as (<- & (? & Heqn') & (? & ? & Heqn & ?)); inv_eqn Heqn; inv_eqn Heqn' *)
(*         | [H : transSomeNone _ _ _ (inl (_, _)) _ _ _ |- _] => let Heqn := fresh "eqn" in let Heqn' := fresh "eqn" in apply transSomeNone_inv3 in H as (<- & (? & Heqn') & (? & ? & Heqn & ?)); inv_eqn Heqn; inv_eqn Heqn' *)
(*         | [H : transSomeNone _ (inl (_, _)) _ _ _ _ _ |- _] => let Heqn := fresh "eqn" in let Heqn' := fresh "eqn" in apply transSomeNone_inv1 in H as (<- & (? & Heqn') & (? & ? & Heqn & ?)); inv_eqn Heqn; inv_eqn Heqn' *)
(*         | [H : transSomeNone _ _ (inl (_, _)) _ _ _ _ |- _] => let Heqn := fresh "eqn" in let Heqn' := fresh "eqn" in apply transSomeNone_inv2 in H as (<- & (? & Heqn') & (? & ? & Heqn & ?)); inv_eqn Heqn; inv_eqn Heqn' *)
(*         | [H : transNoneSome _ _ _ (inl (_, _)) _ _ _ |- _] => let Heqn := fresh "eqn" in let Heqn' := fresh "eqn" in apply transNoneSome_inv3 in H as (<- & Heqn' & (? & ? & Heqn & ?)); inv_eqn Heqn; inv_eqn Heqn' *)
(*         | [H : transNoneSome _ (inl (_, _)) _ _ _ _ _ |- _] => let Heqn := fresh "eqn" in let Heqn' := fresh "eqn" in apply transNoneSome_inv1 in H as (<- & Heqn' & (? & ? & Heqn & ?)); inv_eqn Heqn; inv_eqn Heqn' *)
(*         | [H : transNoneSome _ _ (inl (_, _)) _ _ _ _ |- _] => let Heqn := fresh "eqn" in let Heqn' := fresh "eqn" in apply transNoneSome_inv2 in H as (<- & Heqn' & (? & ? & Heqn & ?)); inv_eqn Heqn; inv_eqn Heqn' *)
(*         | [H : transNoneNone _ _ _ (inl (_, _)) _ _ _ |- _] => let Heqn := fresh "eqn" in let Heqn' := fresh "eqn" in apply transNoneNone_inv3 in H as (<- & Heqn' & (? & ? & Heqn & ?)); inv_eqn Heqn; inv_eqn Heqn' *)
(*         | [H : transNoneNone _ (inl (_, _)) _ _ _ _ _ |- _] => let Heqn := fresh "eqn" in let Heqn' := fresh "eqn" in apply transNoneNone_inv1 in H as (<- & Heqn' & (? & ? & Heqn & ?)); inv_eqn Heqn; inv_eqn Heqn' *)
(*         | [H : transNoneNone _ _ (inl (_, _)) _ _ _ _ |- _] => let Heqn := fresh "eqn" in let Heqn' := fresh "eqn" in apply transNoneNone_inv2 in H as (<- & Heqn' & (? & ? & Heqn & ?)); inv_eqn Heqn; inv_eqn Heqn' *)
(*       end. *)

(*   (*third-level inversions *) *)
(*   Lemma transSomeSomeRight_inv1 q a b q' γ1 γ2 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some b, positive)) -> transSomeSomeRight q γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6 -> transSomeLeftRight q q' (Some a) (Some b) γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6.  *)
(*   Proof. intros. inv H0; simp_eqn. Qed.  *)

(*   Lemma transSomeSomeRight_inv2 q a b q' γ1 γ2 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some b, negative)) -> transSomeSomeRight q γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6 -> transSomeRightRight q q' (Some a) γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6. *)
(*   Proof. intros. inv H0; simp_eqn. Qed. *)

(*   Lemma transSomeSomeRight_inv3 q a b q' γ1 γ2 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some b, neutral)) -> transSomeSomeRight q γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6 -> transSomeStayRight q q' (Some a) (Some b) γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6. *)
(*   Proof. intros. inv H0; simp_eqn. Qed. *)

(*   Lemma transSomeSomeLeft_inv1 q a b q' γ2 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some b, positive)) -> transSomeSomeLeft q (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6 -> transSomeLeftLeft q q' (Some a) (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6. *)
(*   Proof. intros. inv H0; simp_eqn. Qed.  *)

(*   Lemma transSomeSomeLeft_inv2 q a b q' γ2 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some b, negative)) -> transSomeSomeLeft q (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6 -> transSomeRightLeft q q' (Some a) (Some b) (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6. *)
(*   Proof. intros. inv H0; simp_eqn. Qed. *)

(*   Lemma transSomeSomeLeft_inv3 q a b q' γ2 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some b, neutral)) -> transSomeSomeLeft q  (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6 -> transSomeStayLeft q q' (Some a) (Some b) (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6. *)
(*   Proof. intros. inv H0; simp_eqn. Qed. *)

(*   Lemma transSomeSomeCenter_inv1 q a b q' γ1 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some b, positive)) -> transSomeSomeCenter q γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6 -> transSomeLeftCenter q q' (Some a) (Some b) γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6. *)
(*   Proof. intros. inv H0; simp_eqn. Qed.  *)

(*   Lemma transSomeSomeCenter_inv2 q a b q' γ1 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some b, negative)) -> transSomeSomeCenter q γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6 -> transSomeRightCenter q q' (Some a) (Some b) γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6. *)
(*   Proof. intros. inv H0; simp_eqn. Qed. *)

(*   Lemma transSomeSomeCenter_inv3 q a b q' γ1 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some b, neutral)) -> transSomeSomeCenter q  γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6 -> transSomeStayCenter q q' (Some a) (Some b) γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6. *)
(*   Proof. intros. inv H0; simp_eqn. Qed. *)

(*   (*the same for None, Some *) *)
(*   Lemma transNoneSomeRight_inv1 q b q' γ1 γ2 γ4 γ5 γ6 : trans (q, None) = (q', (Some b, positive)) -> transNoneSomeRight q γ1 γ2 (inl (q, None)) γ4 γ5 γ6 -> transSomeLeftRight q q' (None) (Some b) γ1 γ2 (inl (q, None)) γ4 γ5 γ6.  *)
(*   Proof. intros. inv H0; simp_eqn. Qed.  *)

(*   Lemma transNoneSomeRight_inv2 q b q' γ1 γ2 γ4 γ5 γ6 : trans (q, None) = (q', (Some b, negative)) -> transNoneSomeRight q γ1 γ2 (inl (q, None)) γ4 γ5 γ6 -> transSomeRightRight q q' (None) γ1 γ2 (inl (q, None)) γ4 γ5 γ6. *)
(*   Proof. intros. inv H0; simp_eqn. Qed. *)

(*   Lemma transNoneSomeRight_inv3 q b q' γ1 γ2 γ4 γ5 γ6 : trans (q, None) = (q', (Some b, neutral)) -> transNoneSomeRight q γ1 γ2 (inl (q, None)) γ4 γ5 γ6 -> transSomeStayRight q q' (None) (Some b) γ1 γ2 (inl (q, None)) γ4 γ5 γ6. *)
(*   Proof. intros. inv H0; simp_eqn. Qed. *)

(*   Lemma transNoneSomeLeft_inv1 q b q' γ2 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (Some b, positive)) -> transNoneSomeLeft q (inl (q, None)) γ2 γ3 γ4 γ5 γ6 -> transSomeLeftLeft q q' (None) (inl (q, None)) γ2 γ3 γ4 γ5 γ6. *)
(*   Proof. intros. inv H0; simp_eqn. Qed.  *)

(*   Lemma transNoneSomeLeft_inv2 q b q' γ2 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (Some b, negative)) -> transNoneSomeLeft q (inl (q, None)) γ2 γ3 γ4 γ5 γ6 -> transSomeRightLeft q q' (None) (Some b) (inl (q, None)) γ2 γ3 γ4 γ5 γ6. *)
(*   Proof. intros. inv H0; simp_eqn. Qed. *)

(*   Lemma transNoneSomeLeft_inv3 q b q' γ2 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (Some b, neutral)) -> transNoneSomeLeft q  (inl (q, None)) γ2 γ3 γ4 γ5 γ6 -> transSomeStayLeft q q' (None) (Some b) (inl (q, None)) γ2 γ3 γ4 γ5 γ6. *)
(*   Proof. intros. inv H0; simp_eqn. Qed. *)

(*   Lemma transNoneSomeCenter_inv1 q b q' γ1 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (Some b, positive)) -> transNoneSomeCenter q γ1 (inl (q, None)) γ3 γ4 γ5 γ6 -> transSomeLeftCenter q q' (None) (Some b) γ1 (inl (q, None)) γ3 γ4 γ5 γ6. *)
(*   Proof. intros. inv H0; simp_eqn. Qed.  *)

(*   Lemma transNoneSomeCenter_inv2 q b q' γ1 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (Some b, negative)) -> transNoneSomeCenter q γ1 (inl (q, None)) γ3 γ4 γ5 γ6 -> transSomeRightCenter q q' (None) (Some b) γ1 (inl (q, None)) γ3 γ4 γ5 γ6. *)
(*   Proof. intros. inv H0; simp_eqn. Qed. *)

(*   Lemma transNoneSomeCenter_inv3 q b q' γ1 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (Some b, neutral)) -> transNoneSomeCenter q  γ1 (inl (q, None)) γ3 γ4 γ5 γ6 -> transSomeStayCenter q q' (None) (Some b) γ1 (inl (q, None)) γ3 γ4 γ5 γ6. *)
(*   Proof. intros. inv H0; simp_eqn. Qed. *)

(*   (*Some, None*) *)
(*   Lemma transSomeNoneRight_inv1 q a q' γ1 γ2 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some a, positive)) -> transSomeNoneRight q γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6 -> transSomeLeftRight q q' (Some a) (Some a) γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6.  *)
(*   Proof. intros. inv H0; simp_eqn. Qed.  *)

(*   Lemma transSomeNoneRight_inv2 q a q' γ1 γ2 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some a, negative)) -> transSomeNoneRight q γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6 -> transSomeRightRight q q' (Some a) γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6. *)
(*   Proof. intros. inv H0; simp_eqn. Qed. *)

(*   Lemma transSomeNoneRight_inv3 q a q' γ1 γ2 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some a, neutral)) -> transSomeNoneRight q γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6 -> transSomeStayRight q q' (Some a) (Some a) γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6. *)
(*   Proof. intros. inv H0; simp_eqn. Qed. *)

(*   Lemma transSomeNoneLeft_inv1 q a q' γ2 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some a, positive)) -> transSomeNoneLeft q (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6 -> transSomeLeftLeft q q' (Some a) (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6. *)
(*   Proof. intros. inv H0; simp_eqn. Qed.  *)

(*   Lemma transSomeNoneLeft_inv2 q a q' γ2 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some a, negative)) -> transSomeNoneLeft q (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6 -> transSomeRightLeft q q' (Some a) (Some a) (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6. *)
(*   Proof. intros. inv H0; simp_eqn. Qed. *)

(*   Lemma transSomeNoneLeft_inv3 q a q' γ2 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some a, neutral)) -> transSomeNoneLeft q  (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6 -> transSomeStayLeft q q' (Some a) (Some a) (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6. *)
(*   Proof. intros. inv H0; simp_eqn. Qed. *)

(*   Lemma transSomeNoneCenter_inv1 q a q' γ1 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some a, positive)) -> transSomeNoneCenter q γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6 -> transSomeLeftCenter q q' (Some a) (Some a) γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6. *)
(*   Proof. intros. inv H0; simp_eqn. Qed.  *)

(*   Lemma transSomeNoneCenter_inv2 q a q' γ1 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some a, negative)) -> transSomeNoneCenter q γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6 -> transSomeRightCenter q q' (Some a) (Some a) γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6. *)
(*   Proof. intros. inv H0; simp_eqn. Qed. *)

(*   Lemma transSomeNoneCenter_inv3 q a q' γ1 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some a, neutral)) -> transSomeNoneCenter q  γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6 -> transSomeStayCenter q q' (Some a) (Some a) γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6. *)
(*   Proof. intros. inv H0; simp_eqn. Qed. *)

(*   (* None, None*) *)
(*   Lemma transNoneNoneRight_inv1 q q' γ1 γ2 γ4 γ5 γ6 : trans (q, None) = (q', (None, positive)) -> transNoneNoneRight q γ1 γ2 (inl (q, None)) γ4 γ5 γ6 -> transNoneLeftRight q q' γ1 γ2 (inl (q, None)) γ4 γ5 γ6.  *)
(*   Proof. intros. inv H0; simp_eqn. Qed.  *)

(*   Lemma transNoneNoneRight_inv2 q q' γ1 γ2 γ4 γ5 γ6 : trans (q, None) = (q', (None, negative)) -> transNoneNoneRight q γ1 γ2 (inl (q, None)) γ4 γ5 γ6 -> transNoneRightRight q q' γ1 γ2 (inl (q, None)) γ4 γ5 γ6. *)
(*   Proof. intros. inv H0; simp_eqn. Qed. *)

(*   Lemma transNoneNoneRight_inv3 q q' γ1 γ2 γ4 γ5 γ6 : trans (q, None) = (q', (None, neutral)) -> transNoneNoneRight q γ1 γ2 (inl (q, None)) γ4 γ5 γ6 -> transNoneStayRight q q' γ1 γ2 (inl (q, None)) γ4 γ5 γ6. *)
(*   Proof. intros. inv H0; simp_eqn. Qed. *)

(*   Lemma transNoneNoneLeft_inv1 q q' γ2 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (None, positive)) -> transNoneNoneLeft q (inl (q, None)) γ2 γ3 γ4 γ5 γ6 -> transNoneLeftLeft q q' (inl (q, None)) γ2 γ3 γ4 γ5 γ6. *)
(*   Proof. intros. inv H0; simp_eqn. Qed.  *)

(*   Lemma transNoneNoneLeft_inv2 q q' γ2 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (None, negative)) -> transNoneNoneLeft q (inl (q, None)) γ2 γ3 γ4 γ5 γ6 -> transNoneRightLeft q q' (inl (q, None)) γ2 γ3 γ4 γ5 γ6. *)
(*   Proof. intros. inv H0; simp_eqn. Qed. *)

(*   Lemma transNoneNoneLeft_inv3 q q' γ2 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (None, neutral)) -> transNoneNoneLeft q  (inl (q, None)) γ2 γ3 γ4 γ5 γ6 -> transNoneStayLeft q q' (inl (q, None)) γ2 γ3 γ4 γ5 γ6. *)
(*   Proof. intros. inv H0; simp_eqn. Qed. *)

(*   Lemma transNoneNoneCenter_inv1 q q' γ1 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (None, positive)) -> transNoneNoneCenter q γ1 (inl (q, None)) γ3 γ4 γ5 γ6 -> transNoneLeftCenter q q' γ1 (inl (q, None)) γ3 γ4 γ5 γ6. *)
(*   Proof. intros. inv H0; simp_eqn. Qed.  *)

(*   Lemma transNoneNoneCenter_inv2 q q' γ1 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (None, negative)) -> transNoneNoneCenter q γ1 (inl (q, None)) γ3 γ4 γ5 γ6 -> transNoneRightCenter q q' γ1 (inl (q, None)) γ3 γ4 γ5 γ6. *)
(*   Proof. intros. inv H0; simp_eqn. Qed. *)

(*   Lemma transNoneNoneCenter_inv3 q q' γ1 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (None, neutral)) -> transNoneNoneCenter q  γ1 (inl (q, None)) γ3 γ4 γ5 γ6 -> transNoneStayCenter q q' γ1 (inl (q, None)) γ3 γ4 γ5 γ6. *)
(*   Proof. intros. inv H0; simp_eqn. Qed. *)

(*   (*apply the inversion lemmas from above *) *)
(*   Ltac inv_trans_sec := *)
(*   match goal with *)
(*   | [H : trans (_, _) = (_, (_, neutral)) |- _] => *)
(*     repeat match goal with *)
(*             | [H2 : context[transSomeSomeLeft] |- _] => first [eapply transSomeSomeLeft_inv3 in H2; [ | apply H] | inv H2; now simp_eqn]  *)
(*             | [H2 : context[transSomeSomeRight] |- _] => first [eapply transSomeSomeRight_inv3 in H2; [ | apply H] | inv H2; now simp_eqn] *)
(*             | [H2 : context[transSomeSomeCenter] |- _] => first [eapply transSomeSomeCenter_inv3 in H2; [ | apply H] | inv H2; now simp_eqn] *)
(*             | [H2 : context[transNoneSomeLeft] |- _] => first [eapply transNoneSomeLeft_inv3 in H2; [ | apply H] | inv H2; now simp_eqn]  *)
(*             | [H2 : context[transNoneSomeRight] |- _] => first [eapply transNoneSomeRight_inv3 in H2; [ | apply H] | inv H2; now simp_eqn] *)
(*             | [H2 : context[transNoneSomeCenter] |- _] => first [eapply transNoneSomeCenter_inv3 in H2; [ | apply H] | inv H2; now simp_eqn] *)
(*             | [H2 : context[transSomeNoneLeft] |- _] => first [eapply transSomeNoneLeft_inv3 in H2; [ | apply H] | inv H2; now simp_eqn]  *)
(*             | [H2 : context[transSomeNoneRight] |- _] => first [eapply transSomeNoneRight_inv3 in H2; [ | apply H] | inv H2; now simp_eqn] *)
(*             | [H2 : context[transSomeNoneCenter] |- _] => first [eapply transSomeNoneCenter_inv3 in H2; [ | apply H] | inv H2; now simp_eqn] *)
(*             | [H2 : context[transNoneNoneLeft] |- _] => first [eapply transNoneNoneLeft_inv3 in H2; [ | apply H] | inv H2; now simp_eqn]  *)
(*             | [H2 : context[transNoneNoneRight] |- _] => first [eapply transNoneNoneRight_inv3 in H2; [ | apply H] | inv H2; now simp_eqn] *)
(*             | [H2 : context[transNoneNoneCenter] |- _] => first [eapply transNoneNoneCenter_inv3 in H2; [ | apply H] | inv H2; now simp_eqn] *)
(*     end *)
(*   | [H : trans (_, _) = (_, (_, negative)) |- _] => *)
(*     repeat match goal with *)
(*             | [H2 : context[transSomeSomeLeft] |- _] => first [eapply transSomeSomeLeft_inv2 in H2; [ | apply H] | inv H2; now simp_eqn]  *)
(*             | [H2 : context[transSomeSomeRight] |- _] => first [eapply transSomeSomeRight_inv2 in H2; [ | apply H] | inv H2; now simp_eqn] *)
(*             | [H2 : context[transSomeSomeCenter] |- _] => first [eapply transSomeSomeCenter_inv2 in H2; [ | apply H] | inv H2; now simp_eqn] *)
(*             | [H2 : context[transNoneSomeLeft] |- _] => first [eapply transNoneSomeLeft_inv2 in H2; [ | apply H] | inv H2; now simp_eqn]  *)
(*             | [H2 : context[transNoneSomeRight] |- _] => first [eapply transNoneSomeRight_inv2 in H2; [ | apply H] | inv H2; now simp_eqn] *)
(*             | [H2 : context[transNoneSomeCenter] |- _] => first [eapply transNoneSomeCenter_inv2 in H2; [ | apply H] | inv H2; now simp_eqn] *)
(*             | [H2 : context[transSomeNoneLeft] |- _] => first [eapply transSomeNoneLeft_inv2 in H2; [ | apply H] | inv H2; now simp_eqn]  *)
(*             | [H2 : context[transSomeNoneRight] |- _] => first [eapply transSomeNoneRight_inv2 in H2; [ | apply H] | inv H2; now simp_eqn] *)
(*             | [H2 : context[transSomeNoneCenter] |- _] => first [eapply transSomeNoneCenter_inv2 in H2; [ | apply H] | inv H2; now simp_eqn] *)
(*             | [H2 : context[transNoneNoneLeft] |- _] => first [eapply transNoneNoneLeft_inv2 in H2; [ | apply H] | inv H2; now simp_eqn]  *)
(*             | [H2 : context[transNoneNoneRight] |- _] => first [eapply transNoneNoneRight_inv2 in H2; [ | apply H] | inv H2; now simp_eqn] *)
(*             | [H2 : context[transNoneNoneCenter] |- _] => first [eapply transNoneNoneCenter_inv2 in H2; [ | apply H] | inv H2; now simp_eqn] *)
(*     end *)
(*   | [H : trans (_, _) = (_, (_, positive)) |- _] => *)
(*     repeat match goal with *)
(*             | [H2 : context[transSomeSomeLeft] |- _] => first [eapply transSomeSomeLeft_inv1 in H2; [ | apply H] | inv H2; now simp_eqn]  *)
(*             | [H2 : context[transSomeSomeRight] |- _] => first [eapply transSomeSomeRight_inv1 in H2; [ | apply H] | inv H2; now simp_eqn] *)
(*             | [H2 : context[transSomeSomeCenter] |- _] => first [eapply transSomeSomeCenter_inv1 in H2; [ | apply H] | inv H2; now simp_eqn] *)
(*             | [H2 : context[transNoneSomeLeft] |- _] => first [eapply transNoneSomeLeft_inv1 in H2; [ | apply H] | inv H2; now simp_eqn]  *)
(*             | [H2 : context[transNoneSomeRight] |- _] => first [eapply transNoneSomeRight_inv1 in H2; [ | apply H] | inv H2; now simp_eqn] *)
(*             | [H2 : context[transNoneSomeCenter] |- _] => first [eapply transNoneSomeCenter_inv1 in H2; [ | apply H] | inv H2; now simp_eqn] *)
(*             | [H2 : context[transSomeNoneLeft] |- _] => first [eapply transSomeNoneLeft_inv1 in H2; [ | apply H] | inv H2; now simp_eqn]  *)
(*             | [H2 : context[transSomeNoneRight] |- _] => first [eapply transSomeNoneRight_inv1 in H2; [ | apply H] | inv H2; now simp_eqn] *)
(*             | [H2 : context[transSomeNoneCenter] |- _] => first [eapply transSomeNoneCenter_inv1 in H2; [ | apply H] | inv H2; now simp_eqn] *)
(*             | [H2 : context[transNoneNoneLeft] |- _] => first [eapply transNoneNoneLeft_inv1 in H2; [ | apply H] | inv H2; now simp_eqn]  *)
(*             | [H2 : context[transNoneNoneRight] |- _] => first [eapply transNoneNoneRight_inv1 in H2; [ | apply H] | inv H2; now simp_eqn] *)
(*             | [H2 : context[transNoneNoneCenter] |- _] => first [eapply transNoneNoneCenter_inv1 in H2; [ | apply H] | inv H2; now simp_eqn] *)
(*     end *)
(*  end.  *)


  (** *predicates for halting extensions *)

  (*these are the rules that leave the configuration unchanged in a halting configuration *)
  Inductive haltRules : transRule := 
  | haltCenter q (m1 m2 : stateSigma) m p : halt q = true -> haltRules (inr (inr (p, m1))) (inl (q, m)) (inr (inr (p, m2))) (inr (inr (neutral, m1))) (inl (q, m)) (inr (inr (neutral, m2)))
  | haltRight q (m1 m2 m : stateSigma) p : halt q = true -> haltRules (inr (inr (p, m1))) (inr (inr (p, m2))) (inl (q, m)) (inr (inr (neutral, m1))) (inr (inr (neutral, m2))) (inl (q, m)) 
  | haltLeft q (m1 m2 m : stateSigma) p : halt q = true -> haltRules (inl (q, m)) (inr (inr (p, m1))) (inr (inr (p, m2))) (inl (q, m)) (inr (inr (neutral, m1))) (inr (inr (neutral, m2))).

  Hint Constructors haltRules : trans.

  Ltac haltRules_inv1 :=
    match goal with
           | [H : haltRules _ _ _ _ _ _ |- _] => inv H
    end. 

  (** * combined predicate for tape + states *)

  Definition simRules γ1 γ2 γ3 γ4 γ5 γ6 := transRules γ1 γ2 γ3 γ4 γ5 γ6 \/ haltRules γ1 γ2 γ3 γ4 γ5 γ6 \/ tapeRules γ1 γ2 γ3 γ4 γ5 γ6.  

  Hint Unfold simRules : trans. 

  Notation rewHeadSim := (rewritesHeadInd simRules). 



  Ltac rewHeadSim_inv1 :=
    repeat match goal with
    | [H : rewHeadSim _ _ |- _] => inv H
    | [H : simRules _ _ _ _ _ _ |- _] => destruct H as [H | [H | H]]
    | [H : transRules _ _ _ _ _ _ |- _] => inv H
    | [H : haltRules _ _ _ _ _ _ |- _] => inv H
    | [H : tapeRules _ _ _ _ _ _ |- _] => inv H
    end.

  Hint Constructors valid : trans. 

  (*tape strings do not contain state symbols *)
  Definition isStateSym (γ : Gamma) := exists η, γ = inl η. 
  Definition isSpecStateSym (q : states) (γ : Gamma) := exists m, γ = inl (q, m). 

  Hint Unfold isStateSym.
  Hint Unfold isSpecStateSym.

  Lemma isStateSym_isSpecStateSym γ: isStateSym γ <-> exists q, isSpecStateSym q γ. 
  Proof.  
    split.
    - intros ([q m] & ?). eauto. 
    - intros (q & []). eauto. 
  Qed. 
 
  Lemma E_alphabet a p w : a el (E p w) -> a = inr (inr (p, |_|)) \/ a = inr #. 
  Proof. 
    intros. induction w.  
    - cbn in H. firstorder. 
    - cbn in H. destruct H as [H | H]; firstorder.
  Qed.

  Lemma reprTape_no_isStateSym u p w h e : e el h -> u ≃t(p, w) h -> not (isStateSym e). 
  Proof. 
    intros. destruct H0 as (_ & _ & ->). 
    apply in_app_or in H. destruct H as [H | H]. 
    - unfold mapPolarity in H. apply in_map_iff in H as (m & H & _). intros (? & ->). congruence. 
    - apply E_alphabet in H. intros (? & ->). destruct H; congruence. 
  Qed. 

  (** * a few simple facts about applicability of rules *)

(*   Lemma rewHead_tape_sim s s' : valid rewHeadTape s s' -> valid rewHeadSim s s'.  *)
(*   Proof. intros. induction H; [ | | inv H0]; eauto 6 with trans. Qed.  *)


(*   (*exactly one of the symbols for transitions or halting rewrites is a state symbol *) *)
(*   Lemma transRules_statesym1 γ1 γ2 γ3 γ4 γ5 γ6 : transRules γ1 γ2 γ3 γ4 γ5 γ6 -> isStateSym γ1 -> not (isStateSym γ2) /\ not (isStateSym γ3). *)
(*   Proof. unfold isStateSym. intros. destruct H0; split; intros []; transRules_inv2; congruence. Qed.  *)

(*   Lemma transRules_statesym2 γ1 γ2 γ3 γ4 γ5 γ6 : transRules γ1 γ2 γ3 γ4 γ5 γ6 -> isStateSym γ2 -> not (isStateSym γ1) /\ not (isStateSym γ3). *)
(*   Proof. unfold isStateSym. intros. destruct H0; split; intros []; transRules_inv2; congruence. Qed. *)

(*   Lemma transRules_statesym3 γ1 γ2 γ3 γ4 γ5 γ6 : transRules γ1 γ2 γ3 γ4 γ5 γ6 -> isStateSym γ3 -> not (isStateSym γ1) /\ not (isStateSym γ2). *)
(*   Proof. unfold isStateSym. intros. destruct H0; split; intros []; transRules_inv2; congruence. Qed. *)

(*   Lemma haltRules_statesym1 γ1 γ2 γ3 γ4 γ5 γ6 : haltRules γ1 γ2 γ3 γ4 γ5 γ6 -> isStateSym γ1 -> not (isStateSym γ2) /\ not (isStateSym γ3). *)
(*   Proof. unfold isStateSym. intros. destruct H0; split; intros []; haltRules_inv1; congruence. Qed. *)

(*   Lemma haltRules_statesym2 γ1 γ2 γ3 γ4 γ5 γ6 : haltRules γ1 γ2 γ3 γ4 γ5 γ6 -> isStateSym γ2 -> not (isStateSym γ1) /\ not (isStateSym γ3). *)
(*   Proof. unfold isStateSym. intros. destruct H0; split; intros []; haltRules_inv1; congruence. Qed. *)

(*   Lemma haltRules_statesym3 γ1 γ2 γ3 γ4 γ5 γ6 : haltRules γ1 γ2 γ3 γ4 γ5 γ6 -> isStateSym γ3 -> not (isStateSym γ1) /\ not (isStateSym γ2). *)
(*   Proof. unfold isStateSym. intros. destruct H0; split; intros []; haltRules_inv1; congruence. Qed. *)

(*   Lemma transRules_statesym γ1 γ2 γ3 γ4 γ5 γ6 : transRules γ1 γ2 γ3 γ4 γ5 γ6 -> exists q, halt q = false /\ (isSpecStateSym q γ1 \/ isSpecStateSym q γ2 \/ isSpecStateSym q γ3).  *)
(*   Proof. unfold isSpecStateSym. intros. transRules_inv2; exists q; eauto. Qed.  *)

(*   Lemma haltRules_statesym γ1 γ2 γ3 γ4 γ5 γ6 : haltRules γ1 γ2 γ3 γ4 γ5 γ6 -> exists q, halt q = true /\ (isSpecStateSym q γ1 \/ isSpecStateSym q γ2 \/ isSpecStateSym q γ3).  *)
(*   Proof. unfold isSpecStateSym. intros. haltRules_inv1; exists q; eauto. Qed.  *)

(*   (* string representing a tape half can only be rewritten using the tape rules *) *)
(*   Lemma rewHeadTrans_tape' u h h' p w: u ≃t(p, w) h -> rewHeadSim h h' -> rewHeadTape h h'.  *)
(*   Proof.  *)
(*     intros. inv H0.  *)
(*     specialize (tape_repr_inv12 H) as H2. *)
(*     destruct H1 as [ H1 | H1]; [ | destruct H1].  *)
(*     + apply transRules_statesym in H1. *)
(*       destruct H1 as (q & _ & [(x & -> ) | [(x & ->) | (x & ->)]]). *)
(*       all: destruct (H2 (inl (q, x))); [ eauto | congruence]. *)
(*     + apply haltRules_statesym in H0.  *)
(*       destruct H0 as (q & _ & [(x & ->) | [(x & ->) | (x & ->)]]).  *)
(*       all: destruct (H2 (inl (q, x))); [eauto | congruence].  *)
(*     + eauto.  *)
(*   Qed.  *)

(*   Lemma rewHeadSim_tape u h h' p w : u ≃t(p, w) h -> valid rewHeadSim h h' -> valid rewHeadTape h h'.  *)
(*   Proof.  *)
(*     intros. revert u w H. induction H0; intros.  *)
(*     - eauto with trans.  *)
(*     - constructor 2. 2: assumption. clear IHvalid. *)
(*       do 2 (destruct a; destruct b; try now cbn in H; try now inv H0; eauto with trans). *)
(*     - constructor 3. *)
(*       + destruct_tape. destruct a; [ discr_tape | ].   *)
(*         * destruct H1 as (H1 & _ & H2). cbn in H2.  inv H2. cbn in H1; destruct w.   *)
(*           -- apply valid_length_inv in H0. *)
(*              do 3 (destruct b; try now cbn in H0). repeat constructor. *)
(*           -- apply IHvalid with (u := []) (w0 := w). apply niltape_repr.  *)
(*         * apply tape_repr_step in H1. now apply IHvalid with (u := u) (w := w). *)
(*       + now eapply rewHeadTrans_tape'. *)
(*   Qed.  *)

(*   (*we would also like to obtain the other direction for this result, i.e. for polarityRev h *) *)
(*   (*this is a bit more tricky because we cannot reverse h in the ≃t predicate - thus, a straightforward induction will not go through *) *)
(*   (*instead, we use the equivalent characterisation via rewritesAt *) *)
(*   Lemma rewHeadSim_tape_polarityRev u h h' p w : *)
(*     u ≃t(p, w) h -> valid rewHeadSim (polarityRev h) (polarityRev h') *)
(*     -> valid rewHeadTape (polarityRev h) (polarityRev h'). *)
(*   Proof.  *)
(*     intros. apply valid_iff. apply valid_iff in H0 as (H1 & H2).   *)
(*     split. *)
(*     { apply H1. } *)
(*     intros. specialize (H2 i H0).  *)
(*     unfold rewritesAt in *.  *)
(*     rewrite <- (firstn_skipn (|h| - i) h) in H.  *)
(*     apply tape_repr_polarityFlip in H. rewrite map_app in H.  *)
(*     rewrite map_firstn, map_skipn in H. *)

(*     assert (0 <= i < (|h|)) as H3 by (unfold polarityRev in H0; rewrite rev_length, map_length in H0; lia).  *)
(*     rewrite firstn_skipn_rev in H. *)
(*     rewrite map_length in H. replace ((|h|) - (|h| - i)) with i in H by lia.  *)
(*     clear H3.  *)

(*     specialize (skipn_length i (polarityRev h) ) as H3.  *)
(*     specialize (skipn_length i (polarityRev h')) as H4.  *)

(*     remember (skipn i (polarityRev h)) as h1.  *)
(*     remember (skipn i (polarityRev h')) as h2. *)
(*     do 3 (destruct h1 as [ | ? h1]; cbn in *; [lia | ]).  *)
(*     do 3 (destruct h2 as [ | ? h2]; cbn in *; [lia | ]). *)
(*     unfold polarityRev in Heqh1, Heqh2. rewrite <- Heqh1 in H. clear Heqh1 Heqh2 H1 H0 H3 H4.  *)

(*     apply rewritesHeadInd_rem_tail in H2.   *)
(*     apply rewritesHeadInd_rem_tail. *)
(*     inv H2. destruct H1 as [H1 | [H1 | H1]].   *)
(*     - apply transRules_statesym in H1 as (q & _ & [H1 | [H1 | H1]]).  *)
(*       all: match type of H1 with isSpecStateSym ?q ?s => assert (exists q, isSpecStateSym q s) as H2 by eauto; apply isStateSym_isSpecStateSym in H2;  *)
(*       eapply (reprTape_no_isStateSym) with (e := s) in H; [ congruence | ] end.  *)
(*       all: apply in_or_app; left; rewrite <- in_rev; eauto.  *)
(*     - apply haltRules_statesym in H1 as (q & _ & [H1 | [H1 | H1]]).  *)
(*       all: match type of H1 with isSpecStateSym ?q ?s => assert (exists q, isSpecStateSym q s) as H2 by eauto; apply isStateSym_isSpecStateSym in H2;  *)
(*       eapply (reprTape_no_isStateSym) with (e := s) in H; [ congruence | ] end.  *)
(*       all: apply in_or_app; left; rewrite <- in_rev; eauto. *)
(*     - eauto.  *)
(*    Qed.  *)
      
(*   (*if we are not in a halting state, but have a state symbol, the rewrite must be due to a transition rule *) *)
(*   Lemma rewHeadSim_trans q γ1 γ2 γ3 γ4 γ5 γ6 : *)
(*     (isSpecStateSym q γ1 \/ isSpecStateSym q γ2 \/ isSpecStateSym q γ3) *)
(*     -> halt q = false *)
(*     -> simRules γ1 γ2 γ3 γ4 γ5 γ6 *)
(*     -> transRules γ1 γ2 γ3 γ4 γ5 γ6. *)
(*   Proof.  *)
(*     intros [H1 | [H1 | H1]]; (intros H0 H; destruct H as [H | H]; [eauto | destruct H; [ | destruct H1; rewHeadTape_inv2; congruence]]).   *)
(*     all: specialize (haltRules_statesym H) as (q' & H2 & [H3 | [H3 | H3]]).  *)
(*     all: try match goal with *)
(*              | [ H : isSpecStateSym ?q1 ?g, H' : isSpecStateSym ?q2 ?g |- _ ] => destruct H, H'; congruence *)
(*              | [H : haltRules ?g1 _ _ _ _ _, H1 : isSpecStateSym _ ?g1, H2 : isSpecStateSym _ ?g2 |- _] => *)
(*                apply haltRules_statesym1 in H; [ rewrite !isStateSym_isSpecStateSym in H; destruct H; exfalso; eauto| apply isStateSym_isSpecStateSym; eauto ] *)
(*              | [H : haltRules _ ?g1 _ _ _ _, H1 : isSpecStateSym _ ?g1, H2 : isSpecStateSym _ ?g2 |- _] => *)
(*                apply haltRules_statesym2 in H; [ rewrite !isStateSym_isSpecStateSym in H; destruct H; exfalso; eauto| apply isStateSym_isSpecStateSym; eauto ] *)
(*              | [H : haltRules _ _ ?g1 _ _ _, H1 : isSpecStateSym _ ?g1, H2 : isSpecStateSym _ ?g2 |- _] => *)
(*                apply haltRules_statesym3 in H; [ rewrite !isStateSym_isSpecStateSym in H; destruct H; exfalso; eauto| apply isStateSym_isSpecStateSym; eauto ] *)
(*               end.  *)
(*   Qed.  *)

(*   (*if we are in a halting state and have a state symbol, the rewrite must be due to a halting rule *) *)
(*   Lemma rewHeadSim_halt q γ1 γ2 γ3 γ4 γ5 γ6 : *)
(*     (isSpecStateSym q γ1 \/ isSpecStateSym q γ2 \/ isSpecStateSym q γ3) *)
(*     -> halt q = true *)
(*     -> simRules γ1 γ2 γ3 γ4 γ5 γ6 *)
(*     -> haltRules γ1 γ2 γ3 γ4 γ5 γ6. *)
(*   Proof.  *)
(*     intros [H1 | [H1 | H1]]; (intros H0 H; destruct H as [H | H]; [ | destruct H; [ eauto | destruct H1; rewHeadTape_inv2; congruence]]). *)
(*     all: specialize (transRules_statesym H) as (q' & H2 & [H3 | [H3 | H3]]). *)
(*     all: try match goal with *)
(*              | [ H : isSpecStateSym ?q1 ?g, H' : isSpecStateSym ?q2 ?g |- _ ] => destruct H, H'; congruence *)
(*              | [H : transRules ?g1 _ _ _ _ _, H1 : isSpecStateSym _ ?g1, H2 : isSpecStateSym _ ?g2 |- _] => *)
(*                apply transRules_statesym1 in H; [ rewrite !isStateSym_isSpecStateSym in H; destruct H; exfalso; eauto| apply isStateSym_isSpecStateSym; eauto ] *)
(*              | [H : transRules _ ?g1 _ _ _ _, H1 : isSpecStateSym _ ?g1, H2 : isSpecStateSym _ ?g2 |- _] => *)
(*                apply transRules_statesym2 in H; [ rewrite !isStateSym_isSpecStateSym in H; destruct H; exfalso; eauto| apply isStateSym_isSpecStateSym; eauto ] *)
(*              | [H : transRules _ _ ?g1 _ _ _, H1 : isSpecStateSym _ ?g1, H2 : isSpecStateSym _ ?g2 |- _] => *)
(*                apply transRules_statesym3 in H; [ rewrite !isStateSym_isSpecStateSym in H; destruct H; exfalso; eauto| apply isStateSym_isSpecStateSym; eauto ] *)
(*               end.  *)
(*   Qed.  *)

(*   (** *a few more technical facts regarding rewrites *) *)

(*   Lemma valid_reprConfig_unfold pred s q tp : *)
(*     (exists s', valid pred s s' /\ (forall s'', valid pred s s'' -> s'' = s') /\ (q, tp) ≃c s') *)
(*     <-> (exists ls qm rs, valid pred s (rev ls ++ [qm] ++ rs) /\ (forall s'', valid pred s s'' -> s'' = rev ls ++ [qm] ++ rs) /\ (q, tp) ≃c (ls, qm, rs)). *)
(*   Proof.  *)
(*     unfold reprConfig.  *)
(*     split. *)
(*     - intros (s' & H & H' & (ls & qm & rs & -> & H1)). exists ls, qm, rs. eauto.  *)
(*     - intros (ls & qm & rs & H1 & H2 & H3). exists (rev ls ++ [qm] ++ rs). split; [ | split]. *)
(*       + apply H1.  *)
(*       + apply H2. *)
(*       + exists ls, qm, rs. eauto.  *)
(*   Qed.  *)

(*   Lemma rewritesHeadInd_single (X : Type) pred (x1 x2 x3 x4 x5 x6 : X) : *)
(*     pred x1 x2 x3 x4 x5 x6 <-> rewritesHeadInd pred [x1; x2; x3] [x4; x5; x6].  *)
(*   Proof. *)
(*     split. *)
(*     - intros H; now constructor. *)
(*     - intros H; now inv H.  *)
(*   Qed.  *)
     
(*   (*a somewhat ugly but necessary lemma...*) *)
(*   (*this enables us to justify a configuration string rewrite by rewriting the two tape halves and then applying three rules at the center *) *)
(*   Lemma valid_rewritesHeadInd_center (X : Type) (p : X -> X -> X -> X -> X -> X -> Prop) A B (c d e f g : X) A' B' (c' d' e' f' g' : X) : *)
(*     (valid (rewritesHeadInd p) (A ++ [c; d; e; f; g] ++ B) (A' ++ [c'; d'; e'; f'; g'] ++ B') /\ |A| = |A'| /\ |B| = |B'|) *)
(*     <-> (valid (rewritesHeadInd p) (A ++ [c; d]) (A' ++ [c'; d']) /\ valid (rewritesHeadInd p) (f :: g :: B) (f' :: g' :: B') /\ *)
(*        p c d e c' d' e' /\ p d e f d' e' f' /\ p e f g e' f' g'). *)
(*   Proof.  *)
(*     split; intros.  *)
(*     - destruct H as (H1 & H2 & H3). apply valid_iff in H1 as (H0 & H1). *)
(*       repeat rewrite app_length in H0. cbn in H0.  *)
(*       repeat split. *)
(*       + apply valid_iff. split; [rewrite !app_length; cbn; lia | ].   *)
(*         intros. eapply rewritesAt_rewritesHeadInd_rem_at_end.  *)
(*         1: rewrite <- !app_assoc; cbn; eapply H1.  *)
(*         1: repeat rewrite app_length in *; cbn in *; lia.  *)
(*         all: repeat rewrite app_length in *; cbn in *; lia.  *)
(*       + apply valid_iff. split; [cbn ; lia | ]. *)
(*         intros. specialize (H1 (i + |A| + 3)). *)
(*         rewrite !app_length in H1. replace (i + ((|A|) + 3)) with ((3 + |A|) + i) in H1 by lia. *)
(*         replace (A ++ [c; d; e; f; g] ++ B) with (A ++ [c; d; e] ++ f :: g :: B) in H1 by auto.  *)
(*         replace (A' ++ [c'; d'; e'; f'; g'] ++ B') with (A' ++ [c'; d'; e'] ++ f' :: g' :: B') in H1 by auto.  *)
(*         unfold rewritesAt in H1.  *)
(*         rewrite !app_assoc in H1.  *)
(*         rewrite !skipn_add  in H1. 2, 3: rewrite app_length; cbn; lia.  *)
(*         apply H1. cbn in *; lia.  *)
(*       + specialize (H1 (|A|)). unfold rewritesAt in H1. rewrite !skipn_app in H1. 2, 3: lia.  *)
(*         cbn in H1. rewrite rewritesHeadInd_tail_invariant with (s1' := []) (s2' := []) in H1. *)
(*         apply rewritesHeadInd_single, H1. rewrite app_length; cbn; lia.  *)
(*       + specialize (H1 (S (|A|))). unfold rewritesAt in H1. *)
(*         replace (A ++ [c; d; e; f; g] ++ B) with ((A ++ [c]) ++ [d; e; f; g] ++ B) in H1 by (rewrite <- app_assoc; now cbn).  *)
(*         replace (A' ++ [c'; d'; e'; f'; g'] ++ B') with ((A' ++ [c']) ++ [d';e';f';g'] ++ B') in H1 by (rewrite <- app_assoc; now cbn).  *)
(*         rewrite !skipn_app in H1. 2, 3: rewrite app_length; cbn; lia. *)
(*         cbn in H1. rewrite rewritesHeadInd_tail_invariant with (s1' := []) (s2' := []) in H1. *)
(*         apply rewritesHeadInd_single, H1. rewrite !app_length; cbn; lia. *)
(*       + specialize (H1 (S (S (|A|)))). unfold rewritesAt in H1. *)
(*         replace (A ++ [c; d; e; f; g] ++ B) with ((A ++ [c;d]) ++ [e; f; g] ++ B) in H1 by (rewrite <- app_assoc; now cbn).  *)
(*         replace (A' ++ [c'; d'; e'; f'; g'] ++ B') with ((A' ++ [c'; d']) ++ [e';f';g'] ++ B') in H1 by (rewrite <- app_assoc; now cbn).  *)
(*         rewrite !skipn_app in H1. 2, 3: rewrite app_length; cbn; lia. *)
(*         cbn in H1. rewrite rewritesHeadInd_tail_invariant with (s1' := []) (s2' := []) in H1. *)
(*         apply rewritesHeadInd_single, H1. rewrite !app_length; cbn; lia. *)
(*    - destruct H as (H1 & H2 & H3 & H4 & H5). *)
(*      assert (|A| = |A'|). { apply valid_length_inv in H1. rewrite !app_length in H1; cbn in H1; lia. } *)
(*      assert (|B| = |B'|). { apply valid_length_inv in H2. cbn in H2; lia. } *)
(*      repeat split. *)
(*      2, 3: assumption.  *)
(*      apply valid_iff. split.  *)
(*      + rewrite !app_length. cbn. lia.  *)
(*      + intros. rewrite !app_length in H6; cbn in H6. *)
(*        destruct (le_lt_dec (|A|) i); [destruct (le_lt_dec (|A| + 3) i) | ]. *)
(*        * (*rhs*) assert (exists j, i = (|A|) + 3 + j) as (j & ->) by (exists (i - (|A|) - 3); lia).  *)
(*           replace (A ++ [c; d; e; f; g] ++ B) with (A ++ [c; d; e] ++ [f; g] ++ B) by now cbn. *)
(*           replace (A' ++ [c'; d'; e'; f'; g'] ++ B') with (A' ++ [c';d';e'] ++ [f';g'] ++ B') by now cbn.  *)
(*           unfold rewritesAt. rewrite app_assoc. setoid_rewrite app_assoc at 2. *)
(*           rewrite !skipn_add. *)
(*           2,3: rewrite app_length; now cbn. *)
(*           cbn. apply valid_iff in H2 as (H2' & H2). apply H2. *)
(*           cbn. lia.  *)
(*       * (* middle*) *)
(*         destruct (nat_eq_dec i (|A|)); [ | destruct (nat_eq_dec i (S (|A|)))].  *)
(*         ++ unfold rewritesAt. rewrite !skipn_app. 2,3:lia.  *)
(*            cbn. now apply rewritesHeadInd_tail_invariant with (s1' := []) (s2' := []). *)
(*         ++ replace (A ++ [c; d; e; f; g] ++ B) with (A ++ [c] ++ [d; e; f; g] ++ B) by now cbn. *)
(*            replace (A' ++ [c'; d'; e'; f'; g'] ++ B') with (A' ++ [c'] ++ [d'; e'; f';g'] ++ B') by now cbn.  *)
(*            unfold rewritesAt. rewrite app_assoc. setoid_rewrite app_assoc at 2. *)
(*            rewrite !skipn_app. 2, 3: rewrite app_length; now cbn.  *)
(*            now apply rewritesHeadInd_tail_invariant with (s1' := []) (s2' := []). *)
(*        ++ assert (i = S (S (|A|))) by lia. clear n n0 l1 l0.  *)
(*           replace (A ++ [c; d; e; f; g] ++ B) with (A ++ [c; d] ++ [e; f; g] ++ B) by now cbn. *)
(*            replace (A' ++ [c'; d'; e'; f'; g'] ++ B') with (A' ++ [c'; d'] ++ [e'; f';g'] ++ B') by now cbn.  *)
(*            unfold rewritesAt. rewrite app_assoc. setoid_rewrite app_assoc at 2. *)
(*            rewrite !skipn_app. 2, 3: rewrite app_length; now cbn.  *)
(*            now apply rewritesHeadInd_tail_invariant with (s1' := []) (s2' := []). *)
(*     * (*lhs*) *)
(*       apply valid_iff in H1 as (H1' & H1). specialize (H1 i).  *)
(*       rewrite app_length in H1; cbn in H1. replace ((|A|) + 2 - 2) with (|A|) in H1 by lia.   *)
(*       replace (A ++ [c; d; e; f; g] ++ B) with (A ++ [c; d] ++ [e; f; g] ++ B) by now cbn. *)
(*       replace (A' ++ [c'; d'; e'; f'; g'] ++ B') with (A' ++ [c'; d'] ++ [e'; f';g'] ++ B') by now cbn. *)
(*       rewrite app_assoc. setoid_rewrite app_assoc at 2.  *)
(*       eapply rewritesAt_rewritesHeadInd_add_at_end.  *)
(*       now apply H1.  *)
(*   Qed.  *)

(*   (*if we start with a string of such a form, then the resulting string will also have this form *) *)
(*   Lemma valid_rewHeadSim_conc_inv (X : Type) pred s' A B (a b c d e : X)  : *)
(*     valid (Sigma := X) pred (A ++ [a; b; c; d; e] ++ B) s' *)
(*     -> exists A' B' (a' b' c' d' e' : X), s' = A' ++ [a'; b'; c'; d'; e'] ++ B' /\ |A| = |A'| /\ |B|= |B'|. *)
(*   Proof.  *)
(*     intros. apply valid_length_inv in H. *)
(*     rewrite <-  (firstn_skipn (|A|) s'). rewrite <- (firstn_skipn 5 (skipn (|A|) s')).  *)
(*     exists (firstn (|A|) s'). *)
(*     specialize (skipn_length (|A|) s') as H1. specialize (firstn_length (|A|) s') as H2.  *)
(*     specialize (firstn_length (5) (skipn (|A|) s')) as H3. *)
(*     specialize (skipn_length (5) (skipn (|A|) s')) as H4.  *)
(*     rewrite H1 in H3, H4. clear H1.  *)
(*     rewrite !app_length in H. cbn [Nat.add length] in H.  *)
(*     assert (Init.Nat.min 5 (|s'| - |A|) = 5)  by lia. rewrite H0 in H3. clear H0.  *)
(*     exists (skipn 5 (skipn (|A|) s')).  *)
(*     remember (firstn 5 (skipn (|A|) s')) as l.  *)
(*     do 5 (destruct l as [ | ? l]; [now cbn in H3 | ]). destruct l; [ | now cbn in H3].  *)
(*     exists x, x0, x1, x2, x3.  *)
(*     repeat split. *)
(*     - rewrite H2. lia.   *)
(*     - rewrite H4. lia.  *)
(*   Qed.  *)

(*   Lemma app_fold (X : Type) (a b c d e: X) (l : list X) : a :: b :: c :: d :: e :: l = [a; b; c; d; e] ++ l.  *)
(*   Proof. now cbn. Qed.  *)

(*   (** *automation for the simulation proofs *) *)

(*   (*brings the goal into a form in which valid_rewHeadSim_center can be applied *) *)
(*   (*precondition: the tape strings have been destructed such that there are at least two symbols available in each direction, both in premise and conclusion *) *)
(*   Ltac normalise_conf_string H := cbn in H; *)
(*     try match type of H with *)
(*     | context[((_) ++ [_]) ++ (inl _) :: _] => do 2 (rewrite <- app_assoc in H); cbn in H *)
(*     | context[((_) ++ [_]) ++ _ :: (inl _) :: _] => rewrite <- app_assoc in H; cbn in H *)
(*     end. *)

(*   Ltac normalise_conf_strings := match goal with *)
(*     | [ |- valid rewHeadSim ?h1 ?h2 ] => let H1 := fresh in let H2 := fresh in *)
(*                                         let H1' := fresh "Heqn" in let H2' := fresh "Heqn" in *)
(*                                         remember h1 as H1 eqn:H1'; remember h2 as H2 eqn:H2'; *)
(*                                         normalise_conf_string H1'; normalise_conf_string H2'; *)
(*                                         subst H1 H2 *)
(*     end.  *)

(*   Ltac normalise_conf_strings_in H := match type of H with *)
(*     | valid rewHeadSim ?h1 ?h2 => let H1 := fresh in let H2 := fresh in *)
(*                                  let H1' := fresh "Heqn" in let H2' := fresh "Heqn" in *)
(*                                  remember h1 as H1 eqn:H1'; remember h2 as H2 eqn:H2'; *)
(*                                  normalise_conf_string H1'; normalise_conf_string H2'; *)
(*                                  subst H1 H2 *)
(*     end.  *)

(*   (*try to eliminate variables from the goal in the context of niltapes, i.e. substitute eqns such as S n = z' so that we have a z' in the goal again *) *)
(*   Ltac clear_niltape_eqns := repeat match goal with *)
(*     | [ H : ?n = z' |- context[?n]] => rewrite !H *)
(*     | [ H : S ?n = z' |- context[inr(inr (?p, |_|)) :: E ?p ?n]] => *)
(*       replace (inr (inr (p, |_|)) :: E p n) with (E p (S n)) by (now cbn); rewrite !H *)
(*     | [H : S (S ?n) = z' |- context[inr(inr (?p, |_|)) :: inr (inr (?p, |_|)) :: E ?p ?n]] => *)
(*       replace (inr (inr (p, |_|)) :: inr (inr (p, |_|)) :: E p n) with (E p (S (S n))) by (now cbn); rewrite !H *)
(*     | [H : S ?n = z' |- context[rev(E ?p ?n) ++ inr (inr (?p, |_|)) :: ?h]] => *)
(*       replace (rev (E p n) ++ (inr (inr (p, |_|)) : Gamma) :: h) with (rev (E p (S n) ++ h)) by (cbn; try rewrite <- app_assoc; easy); rewrite !H *)
(*     | [H : S ?n = z' |- context[(rev (E ?p ?n)) ++ [inr (inr (?p, |_|))] ++ ?h]] => rewrite app_assoc *)
(*     | [H : S ?n = z' |- context[(rev (E ?p ?n) ++ [inr (inr (?p, |_|))]) ++ ?h]] => *)
(*       replace (rev (E p n) ++ [inr (inr (p, |_|)) : Gamma]) with (rev (E p (S n))) by (cbn; try rewrite <- app_assoc; easy); rewrite !H *)
(* end. *)

(*   (*determine if a tape half is blank *) *)
(*    Ltac is_half_blank F := match type of F with [] ≃t(_,_) _ => constr:(true) |  _ => constr:(false) end. *)

(*    (*get the next symbol which will be under the head *) *)
(*    Ltac get_next_headsym' F := match type of F with [] ≃t(_, _) _ => constr:(|_| : stateSigma)  *)
(*                                               | ?σ :: _ ≃t(_, _) _ => constr:(Some σ : stateSigma) *)
(*                                         end. *)
    
(*    Ltac get_next_headsym F1 F2 csym wsym dir := match wsym with *)
(*     | Some ?wsym => match dir with *)
(*                       | L => get_next_headsym' F1 *)
(*                       | R => get_next_headsym' F2 *)
(*                       | N => constr:(Some wsym : stateSigma) *)
(*                     end *)
(*     | None => match dir with *)
(*                   | L => match csym with Some ?csym => get_next_headsym' F1 *)
(*                                   | _ => match is_half_blank F2 with true => get_next_headsym' F1 *)
(*                                                                 | false => constr:(|_| : stateSigma) *)
(*                                         end *)
(*                         end *)
(*                   | R => match csym with Some ?csym => get_next_headsym' F2 *)
(*                                   | _ => match is_half_blank F1 with true => get_next_headsym' F2 *)
(*                                                                   | false =>  constr:(|_| : stateSigma) *)
(*                                         end *)
(*                       end *)
(*                   | N => constr:(csym : stateSigma) *)
(*                 end *)
(*       end.  *)

(*    (*find out the symbol which the TM writes*) *)
(*    (*remember that we take the view that the TM also writes a symbol if it leaves it unchanged*) *)
(*    (*csym = current symbol under head; wsym: symbol given by the transition function *) *)
(*    Ltac get_written_sym csym wsym := match wsym with *)
(*     | Some ?wsym => constr:(Some wsym : stateSigma) *)
(*     | None => match csym with *)
(*             | Some ?csym => constr:(Some csym : stateSigma) *)
(*             | None => constr:(|_| : stateSigma) *)
(*             end *)
(*       end. *)

(*    (*get the direction in which the tape must be shifted *) *)
(*    (*wsym: written sym as computed by get_written_sym *) *)
(*    Ltac get_shift_direction wsym dir F1 F2 := match dir with *)
(*     | L => match wsym with None => match is_half_blank F1 with true => constr:(neutral) *)
(*                                                         | false => constr:(positive) *)
(*                                   end *)
(*                       | Some _ => constr:(positive) *)
(*           end *)
(*     | R => match wsym with None => match is_half_blank F2 with true => constr:(neutral) *)
(*                                                         | false => constr:(negative) *)
(*                                   end *)
(*                       | Some _ => constr:(negative) *)
(*           end *)
(*     | N => constr:(neutral) *)
(*     end.  *)

(*    (*solve the part of the goal where we have to prove that the rewrite is valid *) *)
(*    Ltac solve_stepsim_rewrite_valid Z := apply rewHead_tape_sim; revert Z; try clear_niltape_eqns; cbn; try rewrite <- !app_assoc; auto. *)
(*    Ltac solve_stepsim_rewrite dir Z1 W1 := *)
(*      normalise_conf_strings; apply valid_rewritesHeadInd_center; repeat split; *)
(*      [solve_stepsim_rewrite_valid Z1 | solve_stepsim_rewrite_valid W1 | | | ]; *)
(*      match goal with *)
(*      | [_ :  _ |- simRules _ _ _ _ _ _ ] => eauto 10 with trans *)
(*      end.  *)

(*    Ltac solve_stepsim_repr shiftdir Z2 W2 := exists shiftdir; cbn; (split; [now cbn | split; [apply Z2 | apply W2]]). *)

(*   (*automation for the uniqueness part *) *)
(*   Lemma rev_fold (X : Type) (A B : list X) b: rev A ++ (b::B) = rev (b :: A) ++ B.  *)
(*   Proof.  *)
(*     cbn. rewrite <- app_assoc. now cbn.  *)
(*   Qed.  *)

(*   Lemma rev_polarityRev A : rev A = polarityRev (map polarityFlipGamma A).  *)
(*   Proof.  *)
(*     unfold polarityRev. rewrite map_involution. reflexivity. involution_simpl.  *)
(*   Qed.  *)

(*   (*a rather technical statement which allows us to derive uniqueness for the reversed left tape string  *) *)
(*   Lemma rewHeadSim_unique_left A B A' a b a' b' u p w: valid rewHeadSim (rev A ++ [b; a]) (A' ++ [b'; a']) -> u ≃t(p, w) a :: b :: A -> (forall s, valid rewHeadTape (rev (a :: b :: A)) (rev (a' :: s)) -> s = B) -> b' :: rev A' = B. *)
(*   Proof.  *)
(*     intros.  *)
(*     repeat rewrite rev_fold in H. rewrite app_nil_r in H.  *)
(*     setoid_rewrite <- polarityRev_involution in H at 5.  *)
(*     rewrite rev_polarityRev in H.  *)
(*     eapply rewHeadSim_tape_polarityRev in H.  *)
(*     2: { cbn; apply tape_repr_polarityFlip in H0. cbn in H0. apply H0. } *)
(*     rewrite <- rev_polarityRev in H. rewrite polarityRev_involution in H.  *)
(*     rewrite <- rev_involutive with (l := A') in H.  *)
(*     repeat rewrite rev_fold in H. rewrite app_nil_r in H.  *)
(*     apply H1 in H. easy.  *)
(*   Qed.  *)

(*   Ltac solve_stepsim_uniqueness H F1 F2 Z3 W3 :=  *)
(*     cbn in H; rewrite <- !app_assoc in H; cbn in H;  *)
(*       rewrite app_fold in H;  *)
(*       let X1 := fresh "X1" in let X2 := fresh "X2" in  *)
(*       destruct (valid_rewHeadSim_conc_inv H) as (? & ? & ? & ? & ? & ? & ? & -> & X1 & X2); *)
(*       normalise_conf_strings_in H;  *)
(*       let K1 := fresh "K" in let K2 := fresh "K" in let K3 := fresh "K" in *)
(*       let K4 := fresh "K" in let K5 := fresh "K" in *)
(*       specialize (proj1 (valid_rewritesHeadInd_center simRules _  _ _ _ _ _ _ _ _ _ _ _ _ _) (conj H (conj X1 X2))) as (K1 & K2 & K3 & K4 & K5);  *)
(*       eapply rewHeadSim_trans in K3; [ | eauto | eauto];  *)
(*       eapply rewHeadSim_trans in K4; [ | eauto | eauto]; *)
(*       eapply rewHeadSim_trans in K5; [ | eauto | eauto];  *)
(*       inv K3; inv_trans_prim; inv K4; inv_trans_prim; inv K5; inv_trans_prim; *)
(*       inv_trans_sec; transRules_inv2; simp_eqn;  *)
(*       (specialize (rewHeadSim_unique_left K1 F1 Z3) as ?; *)
(*       simp_eqn; *)
(*       eapply rewHeadSim_tape in K2; [ | eapply F2]; apply W3 in K2;  *)
(*       simp_eqn;  *)
(*       cbn; try rewrite <- !app_assoc; cbn; reflexivity). *)

  (*proof takes roughly 35mins + 4 gigs of RAM... *)
  Lemma stepsim q tp s q' tp' : (q, tp) ≃c s -> (q, tp) ≻ (q', tp') -> (sizeOfTape tp) < z' -> exists s', valid rewHeadSim s s' /\ (forall s'', valid rewHeadSim s s'' -> s'' = s') /\ (q', tp') ≃c s'. 
  Proof. 
  (*   intros H (H0' &  H0) H1. cbn in H0'. unfold sstep in H0. destruct trans eqn:H2 in H0. inv H0. rename p into p'. *)
  (*   apply valid_reprConfig_unfold. *)
  (*   rewrite sizeOfTape_lcr in H1. *)
  (*   destruct H as (ls & qm & rs & -> & H). destruct H as (p & -> & F1 & F2). unfold embedState. *)
  (*   destruct p' as ([wsym | ] & []); destruct tp as [ | ? l1 | ? l0 | l0 ? l1]; cbn in *; destruct_tape_in_tidy F1; destruct_tape_in_tidy F2. *)
  (*   all: try match type of F1 with ?l0 ≃t(_, _) _ => is_var l0; destruct l0 as [ | ? l0]; destruct_tape_in_tidy F1 end. *)
  (*   all: try match type of F1 with _ :: ?l0 ≃t(_, _) _ => destruct l0 as [ | ? l0]; destruct_tape_in_tidy F1 end. *)
  (*   all: try match type of F2 with ?l1 ≃t(_, _) _ => is_var l1; destruct l1 as [ | ? l1]; destruct_tape_in_tidy F2 end. *)
  (*   all: try match type of F2 with _ :: ?l1 ≃t(_, _) _ => destruct l1 as [ | ? l1]; destruct_tape_in_tidy F2 end. *)
    
  (*   Optimize Proof. *)
  (*   all: cbn in H1. *)

  (*   all: *)
  (*     match type of H2 with *)
  (*       | trans (?q, ?csym) = (?q', (?wsym, ?dir)) => *)
  (*         let nextsym := get_next_headsym F1 F2 csym wsym dir in *)
  (*         let writesym := get_written_sym csym wsym in *)
  (*         let shiftdir := get_shift_direction writesym dir F1 F2 in *)
  (*         (*init next tape halves *) *)
  (*         let Z1 := fresh "Z1" in let Z2 := fresh "Z2" in let Z3 := fresh "Z3" in *)
  (*         let W1 := fresh "W1" in let W2 := fresh "W2" in let W3 := fresh "W3" in *)
  (*         let h1 := fresh "h1" in let h2 := fresh "h2" in *)
  (*         cbn in F1; cbn in F2; *)
  (*         match shiftdir with *)
  (*         | R => match type of F1 with *)
  (*               | [] ≃t(?p, ?w) _ => specialize (E_rewrite_blank_rev p shiftdir w) as Z1; *)
  (*                                   specialize (proj1 (@niltape_repr w shiftdir)) as Z2; *)
  (*                                   specialize (@E_rewrite_blank_rev_unique p shiftdir w) as Z3 *)
  (*               | _ => destruct (tape_repr_rem_left F1) as (h1 & Z1 & Z3 & Z2); *)
  (*                     (*need to have one more head symbol in that case *) *)
  (*                     try match type of Z2 with _ :: ?l ≃t(_, _) _ => is_var l; *)
  (*                                                                   destruct l end; destruct_tape_in_tidy Z2 *)
  (*               end; *)
  (*               match writesym with *)
  (*               | Some ?sym => (destruct (tape_repr_add_right sym F2) as (h2 & W1 & W3 & W2)); [cbn; lia | destruct_tape_in_tidy W2] *)
  (*               | None => *)
  (*                   match type of F2 with *)
  (*                   | [] ≃t(?p, ?w) _ => specialize (E_rewrite_blank p shiftdir w) as W1; *)
  (*                                       specialize (proj1 (@niltape_repr w shiftdir)) as W2; *)
  (*                                       specialize (@E_rewrite_blank_unique p shiftdir w) as W3 *)
  (*                   end *)
  (*               end *)
  (*         | L => match type of F2 with *)
  (*               | [] ≃t(?p, ?w) _ => specialize (E_rewrite_blank p shiftdir w) as W1; *)
  (*                                   specialize (proj1 (@niltape_repr w shiftdir)) as W2; *)
  (*                                   specialize (@E_rewrite_blank_unique p shiftdir  w) as W3 *)
  (*                 | _ => destruct (tape_repr_rem_right F2) as (h2 & W1 & W3 & W2); *)
  (*                       (*need to have one more head symbol in that case *) *)
  (*                       try match type of W2 with _ :: ?l ≃t(_, _) _ => is_var l; *)
  (*                                                                     destruct l end; destruct_tape_in_tidy W2 *)
  (*               end; *)
  (*               match writesym with *)
  (*                 Some ?sym => destruct (tape_repr_add_left sym F1) as (h1 & Z1 & Z3 & Z2); [cbn; lia | destruct_tape_in_tidy Z2] *)
  (*               | None => match type of F1 with *)
  (*                       | [] ≃t(?p, ?w) _ => specialize (E_rewrite_blank_rev p shiftdir w) as Z1; *)
  (*                                           specialize (proj1 (@niltape_repr w shiftdir)) as Z2; *)
  (*                                           specialize (@E_rewrite_blank_rev_unique p shiftdir w) as Z3 *)
  (*                   end *)
  (*             end *)
  (*         | N => destruct (tape_repr_stay_left F1) as (h1 & Z1 & Z3 & Z2); destruct_tape_in_tidy Z2; *)
  (*               destruct (tape_repr_stay_right F2) as (h2 & W1 & W3 & W2); destruct_tape_in_tidy W2 *)
  (*         end; *)

  (*       (*instantiate existenials *) *)
  (*       match type of Z2 with _ ≃t(_, _) ?h => exists h end; *)
  (*       exists (inl (q', nextsym) : Gamma); *)
  (*       match type of W2 with _ ≃t(_, _) ?h => exists h end; *)

  (*       (*solve goals, except for the uniqueness goal (factored out due to performance)*) *)
  (*       (split; [solve_stepsim_rewrite shiftdir Z1 W1 | split; [  | solve_stepsim_repr shiftdir Z2 W2]]) *)
  (*   end. *)
    
  (*   Optimize Proof. *)

  (*   all: unfold wo; cbn [Nat.add]; clear_niltape_eqns; intros s H; clear Z1 W1 W2 Z2; clear H1; abstract (solve_stepsim_uniqueness H F1 F2 Z3 W3). *)
  (* Qed. *)
Admitted.

  Lemma haltsim q tp s : (q, tp) ≃c s -> halt q = true -> exists s', valid rewHeadSim s s' /\ (forall s'', valid rewHeadSim s s'' -> s'' = s') /\ (q, tp) ≃c s'. 
  Proof. 
    Admitted.
  (*   intros. apply valid_reprConfig_unfold. *)
  (*   destruct H as (ls & qm & rs & H1 & H2). *)
  (*   destruct H2 as (p & F0 & F1 & F2). *)
  (*   unfold reprTape in F1, F2. unfold embedState in F0. *)
  (*   destruct tp as [ | ? l1 | ? l0 | l0 ? l1]; cbn in *. *)
  (*   all: destruct_tape_in F1; destruct_tape_in F2. *)
  (*   all: try match type of F1 with ?l0 ≃t(_, _) _ => is_var l0; destruct l0 as [ | ? l0]; destruct_tape_in_tidy F1 end. *)
  (*   all: try match type of F1 with _ :: ?l0 ≃t(_, _) _ => destruct l0 as [ | ? l0]; destruct_tape_in_tidy F1 end. *)
  (*   all: try match type of F2 with ?l1 ≃t(_, _) _ => is_var l1; destruct l1 as [ | ? l1]; destruct_tape_in_tidy F2 end. *)
  (*   all: try match type of F2 with _ :: ?l1 ≃t(_, _) _ => destruct l1 as [ | ? l1]; destruct_tape_in_tidy F2 end. *)
  (*   all: specialize (tape_repr_stay_left F1) as (h1 & Z1 & Z3 & Z2). *)
  (*   all: specialize (tape_repr_stay_right F2) as (h2 & W1 & W3 & W2). *)
  (*   all: destruct_tape_in_tidy W2; destruct_tape_in_tidy Z2. *)
  (*   all: match type of Z1 with valid _ _ (rev ?h) => exists h end. *)
  (*   all: exists qm. *)
  (*   all: match type of W1 with valid _ _ ?h => exists h end. *)
  (*   all: subst. *)
  (*   all: split; [solve_stepsim_rewrite neutral Z1 W1 | split; [ |solve_stepsim_repr neutral Z2 W2 ] ]. *)
  (*   (*uniqueness *) *)
  (*   (*mostly matches the corresponding stepsim tactic above, but uses different inversions and needs some additional plumbing with app in Z3*) *)
  (*   all: intros s H; clear Z1 W1 W2 Z2;  *)
  (*     cbn in H; rewrite <- !app_assoc in H; cbn in H;  *)
  (*     rewrite app_fold in H;  *)
  (*     let X1 := fresh "X1" in let X2 := fresh "X2" in  *)
  (*     destruct (valid_rewHeadSim_conc_inv H) as (? & ? & ? & ? & ? & ? & ? & -> & X1 & X2); *)
  (*     normalise_conf_strings_in H;  *)
  (*     let K1 := fresh "K" in let K2 := fresh "K" in let K3 := fresh "K" in *)
  (*     let K4 := fresh "K" in let K5 := fresh "K" in *)
  (*     specialize (proj1 (valid_rewritesHeadInd_center simRules _ _ _ _ _ _ _ _ _ _ _ _ _ _) (conj H (conj X1 X2))) as (K1 & K2 & K3 & K4 & K5);  *)
  (*     eapply rewHeadSim_halt in K3; [ | eauto | eauto];  *)
  (*     eapply rewHeadSim_halt in K4; [ | eauto | eauto]; *)
  (*     eapply rewHeadSim_halt in K5; [ | eauto | eauto];  *)
  (*     haltRules_inv1; simp_eqn; *)
  (*     try rewrite <- app_assoc in Z3; cbn in Z3; try rewrite !rev_fold in Z3; try rewrite app_nil_r in Z3; *)
  (*     (specialize (rewHeadSim_unique_left K1 F1 Z3) as ?; *)
  (*     simp_eqn; *)
  (*     eapply rewHeadSim_tape in K2; [ | eapply F2]; apply W3 in K2;  *)
  (*     simp_eqn;  *)
  (*     cbn; try rewrite <- !app_assoc; cbn; reflexivity). *)
  (* Qed. *)

  
  (** *multi-step simulation *)
  Definition sstepRel s s' := halt (configState s) = false /\ sstep s = s'.

  Notation "s '≻(' k ')' s'" := (relpower sstepRel k s s') (at level 40). 

  (*this is similar to what loopM does, but using the unfolded TM *)
  Notation "s '▷(' k ')' s'" := (s ≻(k) s' /\ halt (configState s') = true) (at level 40).

  Notation "s '▷(≤' k ')' s'" := (exists l, l <= k /\ s ▷(l) s') (at level 40).

  Notation "s '⇝' s'" := (valid rewHeadSim s s') (at level 40). 
  Notation "s '⇝(' k ')' s'" := (relpower (valid rewHeadSim) k s s') (at level 40).

  (*with each step, a Turing machine needs at most one additional cell *)
  Lemma tm_step_size q tp q' tp' l: (q, tp) ≻ (q', tp') -> sizeOfTape tp = l -> sizeOfTape tp' <= S l. 
  Proof. 
    intros. 
    destruct H as (_ & H). unfold sstep in H. destruct tp; destruct trans; destruct p as ([] & []); cbn in *; simp_eqn; rewrite <- H2; cbn in *.
    all: try lia.
    all: repeat match goal with
    | [H : context[midtape ?l _ _]  |- _] => is_var l; destruct l; cbn in *
    | [H : context[midtape _ _ ?l]  |- _] => is_var l; destruct l; cbn in *
    | [H : context[tape_move_left' ?l _ _]  |- _] => is_var l; destruct l; cbn in *
    | [H : context[tape_move_left' _ _ ?l]  |- _] => is_var l; destruct l; cbn in *
    | [H : context[tape_move_right' ?l _ _]  |- _] => is_var l; destruct l; cbn in *
    | [H : context[tape_move_right' _ _ ?l]  |- _] => is_var l; destruct l; cbn in *
    | [H : context[(| _ ++ _ |)] |- _] => rewrite app_length in H
    | [H : context[(| rev _ |)] |- _ ] => rewrite rev_length in H
    | [ |- context[(| _ ++ _|)]] => rewrite app_length
    | [ |- context[(| rev _ |)]] => rewrite rev_length
    end; cbn in * ; try lia.
  Qed. 

  (*Lemma 23 *)
  (*the formulation here is a bit different than in the memo: *)
  (* - we additionally require that sizeOfTape tp < z'. While the statement is true without this restriction, we don't need the stronger version and its proof is a LOT more tedious *)
  Lemma step_inversion q tp s s' : (q, tp) ≃c s -> sizeOfTape tp < z' -> halt q = false -> s ⇝ s' -> exists! q' tp', (q', tp') ≃c s' /\ (q, tp) ≻ (q', tp'). 
  Proof.
    intros. 
    destruct (sstep (q, tp)) as (q', tp') eqn:H3. 
    assert ((q, tp) ≻ (q', tp')) as H4 by auto. 
    specialize (stepsim H H4 H0) as (s'' & F1 & F2 & F3 ). 
    apply F2 in H2.  subst.
    exists q'. split.
    + exists tp'. split.
      * repeat split. apply F3. now cbn. 
      * intros. destruct H2 as (_ & _ & H2); congruence. 
    + intros. destruct H2 as (? & (_ & _ & H2) & _).  congruence. 
  Qed. 

  (*same thing without the uniqueness because of the hassle of dealing with exists! if one doesn't need uniqueness *)
  Lemma step_inversion' q tp s s' : (q, tp) ≃c s -> sizeOfTape tp < z' -> halt q = false -> s ⇝ s' -> exists q' tp', (q', tp') ≃c s' /\ (q, tp) ≻ (q', tp'). 
  Proof. 
    intros. specialize (step_inversion H H0 H1 H2). intros. rewrite <- !unique_existence in H3.
    destruct H3 as ((q' & tp' & (H3 & _ )) & _ ). eauto. 
  Qed. 

  (*Lemma 24 *)
  Lemma halting_inversion q tp s s' : (q, tp) ≃c s -> halt q = true -> s ⇝ s' -> (q, tp) ≃c s'. 
  Proof. 
    intros. specialize (haltsim H H0 ) as (s'' & H2 & H3 & H4). 
    apply H3 in H1. subst. apply H4.  
  Qed. 

  (*Lemma 25 *)
  Lemma multistep_simulation q tp q' tp' l s : (q, tp) ≃c s -> (q, tp) ≻(l) (q', tp') -> z' >= l -> (sizeOfTape tp) <= z' - l -> exists s', s ⇝(l) s' /\ (forall s'', s ⇝(l) s'' -> s'' = s') /\ (q', tp') ≃c s'. 
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
    - destruct b as (q''& tp''). assert (z' >= n) as X by lia. specialize (IH X q'' tp'' q' tp' eq_refl eq_refl). clear X.
      unfold sstepRel in H. 
      assert (sizeOfTape tp < z') as X by lia. specialize (stepsim H1 H X) as (s' & F1 & F2 & F3). clear X.
      specialize (IH s' F3) as (s'' & G1 & G2 & G3). 
      apply tm_step_size with (l := sizeOfTape tp)in H. 2: reflexivity. lia. 
      exists s''. repeat split. 
      + eauto.  
      + intros. inv H0. apply F2 in H6. rewrite H6 in *. clear H6. now apply G2. 
      + apply G3. 
  Qed.

  (*Lemma 26 *)
  Lemma multistep_halt q tp s : (q, tp) ≃c s -> halt q = true -> forall l, exists s', s ⇝(l) s' /\ (forall s'', s ⇝(l) s'' -> s'' = s') /\ (q, tp) ≃c s'. 
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

  (*our final constraint. we don't use the definition via a list of final substrings from the TCSR definition, but instead use this more specific form *)
  (*we will later show that the two notions are equivalent for a suitable list of final substrings*)
  (*there exists the symbol of a halting state in the string s *)
  Definition containsHaltingState s := exists q qs, halt q = true /\ isSpecStateSym q qs /\ qs el s.  
  
  (*Lemma 27 *)
  (*currently differs from the version in the memo: the additional sizeOfTape tp <= z' - j constraint is due to the similar constraint in Lemma 23 *)
  (*the additional assumption z' >= j is needed for the same reason *)
  Lemma multistep_inversion q tp s s' j: (q, tp) ≃c s -> s ⇝(j) s' -> sizeOfTape tp <= z' - j -> z' >= j -> exists q' tp' j', (q', tp') ≃c s' /\ j' <= j /\ (q, tp) ≻(j') (q', tp') /\ sizeOfTape tp' <= sizeOfTape tp + j'. 
  Proof. 
    intros. apply relpower_relpowerRev in H0.
    induction H0 as [ | s y y' j H0 IH].  
    - exists q, tp, 0. rewrite Nat.add_0_r. repeat split; eauto.  
    - assert (sizeOfTape tp <= z' - j) as H4 by lia.  assert (z' >= j) as H5 by lia. 
      specialize (IH H H4 H5) as (q' & tp' & j' & F1 & F2 & F3 & F4). 
      clear H4 H5. 
      destruct (halt q') eqn:H4. 
      + exists q', tp', j'.
        specialize (halting_inversion F1 H4 H3) as H5. eauto. 
      + assert (sizeOfTape tp' < z') as H6 by lia.
        specialize (step_inversion' F1 H6 H4 H3) as (q'' & tp'' & G1 & G2). 
        exists q'', tp'', (S j'). repeat split; eauto. 
        * lia.  
        * apply relpower_relpowerRev. econstructor.
          -- apply relpower_relpowerRev in F3; eauto.
          -- apply G2.  
        * apply tm_step_size with (l := sizeOfTape tp') in G2; [lia | reflexivity ].  
  Qed. 

  (*Lemma 28 *)
  Lemma finalCondition q tp s : (q, tp) ≃c s -> (halt q = true <-> containsHaltingState s). 
  Proof.
    intros; split; intros.
    - destruct H as (ls & qm & rs & -> & H2). exists q, qm. repeat split; eauto. 
      destruct H2 as (p & -> & H3 & H4). unfold isSpecStateSym. unfold embedState. eauto. 
    - destruct H0 as (q' & qs & H1 & H2 & H3). enough (q = q') by congruence. 
      destruct H as (ls & qm & rs & -> & H4). destruct H4 as (p & -> & H5 & H6).
      apply in_app_or in H3; destruct H3 as [ | H3]; [ | apply in_app_or in H3; destruct H3 as [ | H3 ] ].
      + clear H6. destruct H2 as (m & ->). 
        apply in_rev in H. destruct H5 as (_ & _ & ->). apply in_app_iff in H. destruct H as [H | H]. 
        * unfold mapPolarity in H. apply in_map_iff in H as (σ & H & _). congruence. 
        * apply E_alphabet in H. destruct H; congruence.
      + destruct H as [ <- | []]. destruct H2. unfold embedState in H. congruence. 
      + clear H5. destruct H2 as (m & ->).
        destruct H6 as (_ & _ & ->). apply in_app_iff in H3. destruct H3 as [H | H]. 
        * unfold mapPolarity in H. apply in_map_iff in H as (σ & H & _). congruence. 
        * apply E_alphabet in H. destruct H; congruence.
  Qed. 

  (*Theorem 29 *)
  Lemma reprTape_exists u p w : |u| <= w -> exists s, u ≃t(p, w) s. 
  Proof. 
    intros. exists (mapPolarity p u ++ E p (wo + w - |u|)). 
    repeat split.
    + rewrite app_length. unfold mapPolarity. rewrite E_length, map_length. lia. 
    + apply H. 
  Qed. 

  Lemma reprConfig_exists q tp: sizeOfTape tp <= k -> exists s, (q, tp) ≃c s. 
  Proof.
    intros. enough (exists ls qm rs, (q, tp) ≃c (ls, qm, rs)). 
    { destruct H0 as (ls & qm & rs & H0). exists (rev ls ++ [qm] ++ rs). unfold reprConfig. exists ls, qm, rs. eauto. }
    rewrite sizeOfTape_lcr in H. 
    assert (|left tp| <= z') as H1 by (unfold z'; lia). 
    assert (|right tp| <= z') as H2 by (unfold z'; lia). 
    destruct (reprTape_exists neutral H1) as (ls & F1). 
    destruct (reprTape_exists neutral H2) as (rs & F2). 
    exists ls, (inl (q, current tp)), rs. exists neutral. destruct F1 as (? & ? & ?), F2 as (? & ? & ?); repeat split; assumption. 
  Qed. 

  Theorem completeness q tp q' tp' s : sizeOfTape tp <= k -> (q, tp) ≃c s -> (q, tp) ▷(≤t) (q', tp') -> exists s', s ⇝(t) s' /\ (q', tp') ≃c s' /\ containsHaltingState s'. 
  Proof. 
    intros. 
    destruct H1 as (t' & H1 & (H2 & H3)). cbn in H3. 
    assert (z' >= t') as H4 by (unfold z'; lia). 
    assert (sizeOfTape tp <= z' - t') as H5 by (unfold z'; lia). 
    specialize (multistep_simulation H0 H2 H4 H5) as (s' & F1 & _ & F3). 
    specialize (multistep_halt F3 H3 (t - t')) as (s'' & G1 & _ & G3).
    exists s''. repeat split. 
    + replace t with (t' + (t - t')) by lia. eauto using relpower_trans. 
    + apply G3. 
    + eapply finalCondition; eauto. 
  Qed. 

  (*Theorem 30 *)
  Theorem soundness q tp s s' : (q, tp) ≃c s -> sizeOfTape tp <= k -> s ⇝(t) s' -> containsHaltingState s' -> exists q' tp', (q', tp') ≃c s' /\ (q, tp) ▷(≤t) (q', tp') /\ sizeOfTape (tp') <= z. 
  Proof.
    intros.
    assert (sizeOfTape tp <= z' - t) as H3 by (unfold z'; lia). 
    assert (z' >= t) as H4 by (unfold z'; lia). 
    specialize (multistep_inversion H H1 H3 H4) as (q' & tp' & t' & F1 & F2 & F3 & F4). 
    exists q', tp'. repeat split. 
    - apply F1. 
    - exists t'. apply (finalCondition F1) in H2. split; [apply F2 | ]. split; cbn; eauto. 
    - unfold z. lia. 
  Qed. 

  (** *list-based rules *)
  Definition FGamma := FinType (EqType (Gamma)). 
  Definition FstateSigma := FinType (EqType (stateSigma)). 
  Definition Fpolarity := FinType (EqType polarity).

  (*polarity reversion for windows *)
  Definition polarityRevTCSRWinP (x : TCSRWinP Gamma) : TCSRWinP Gamma :=
    match x with {σ1, σ2, σ3}=> {polarityFlipGamma σ3, polarityFlipGamma σ2, polarityFlipGamma σ1} end. 
  Definition polarityRevWin (x : TCSRWin Gamma) : TCSRWin Gamma := {| prem := polarityRevTCSRWinP (prem x); conc := polarityRevTCSRWinP (conc x)|}. 

  Lemma polarityRevWin_involution: involution polarityRevWin. 
  Proof. 
    intros a. destruct a, prem, conc. unfold polarityRevWin. cbn.
    rewrite !polarityFlipGamma_involution. reflexivity.
  Qed. 

  Smpl Add (apply polarityRevWin_involution) : involution.

  (** *list-based rule infrastructure *)
  (*we use a abstract representation of elements of the alphabet Gamma with holes where the elements of the abstract TM alphabets Sigma and states need to be placed *)
  (*the following development is centered around the goal of easily being able to instantiate the abstract fGamma elements with finTypes and with the flat representation using natural numbers *)
  Inductive fstateSigma := blank | someSigmaVar : nat -> fstateSigma | stateSigmaVar : nat -> fstateSigma. 
  Inductive fpolarity := polConst : polarity -> fpolarity | polVar : nat -> fpolarity.
  Definition fpolSigma := prod fpolarity fstateSigma.
  Definition ftapeSigma := sum delim fpolSigma.
  Definition fStates := prod nat fstateSigma.
  Definition fGamma := sum fStates ftapeSigma. 

  Record evalEnv X Y Z W := {
                              polarityEnv : list X;
                              sigmaEnv : list Y;
                              stateSigmaEnv : list Z;
                              stateEnv : list W
                      }.

  (*variables are bound to the elements at the corresponding index *)
  Definition boundVar (X : Type) (l : list X) (n : nat) := n < length l. 
  Section fixEnv. 
    Context {X Y Z W : Type}.
    Context (env : evalEnv X Y Z W). 

    Definition reifySigVar v := nth_error (sigmaEnv env) v.  
    Definition reifyPolarityVar v := nth_error (polarityEnv env) v.
    Definition reifyStateSigmaVar v := nth_error (stateSigmaEnv env) v.
    Definition reifyStateVar v := nth_error (stateEnv env) v. 

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

  End fixEnv. 

  Definition evalEnvFin := evalEnv Fpolarity Sigma FstateSigma states. 
  Definition evalEnvFlat := evalEnv nat nat nat nat.

  (*a reification procedure is canonical if it uses exactly the bound variables *)
  Definition reifyCanonical {X Y Z W M : Type} (reify : evalEnv X Y Z W -> fGamma -> option M) := 
              forall (env : evalEnv X Y Z W) (c : fGamma), bound_Gamma env c <-> exists e, reify env c = Some e. 


  (*option monad in order to ease notation *)
  Definition optReturn := @Some.
  Definition optBind {X Y : Type} (x : option X) (f : X -> option Y) :=
    match x with
    | None => None
    | Some x => f x
    end. 

  (*notations from https://pdp7.org/blog/2011/01/the-maybe-monad-in-coq/ *)
  Notation "A >>= F" := (optBind A F) (at level 40, left associativity).
  Notation "'do' X <- A ; B" := (optBind A (fun X => B)) (at level 200, X ident, A at level 100, B at level 200).

  (*reification to finite types *)
  Definition reifyPolarityFin (env : evalEnvFin) (c : fpolarity) :=
    match c with
    | polConst c => Some c
    | polVar n => nth_error (polarityEnv env) n
    end. 
  Definition reifyStateSigmaFin (env : evalEnvFin) (c : fstateSigma) :=
    match c with
    | blank => Some |_|
    | someSigmaVar v => option_map Some (nth_error (sigmaEnv env) v)
    | stateSigmaVar v => nth_error (stateSigmaEnv env) v
  end. 

  Definition reifyPolSigmaFin (env : evalEnvFin) (c : fpolSigma) :=
    match c with
    | (p, s) => do p <- reifyPolarityFin env p;
                do s <- reifyStateSigmaFin env s;
                optReturn (p, s)
    end. 

  Definition reifyTapeSigmaFin (env : evalEnvFin) (c : ftapeSigma) :=
    match c with
    | inl delimC => Some (inl delimC)
    | inr c => option_map inr (reifyPolSigmaFin env c)
    end.

  Definition reifyStatesFin (env : evalEnvFin) (c : fStates) :=
    match c with
    | (v, s) => do p <- nth_error (stateEnv env) v;
                do s <- reifyStateSigmaFin env s;
                optReturn (p, s)
    end. 

  Definition reifyGammaFin (env : evalEnvFin) (c : fGamma) :=
    match c with
    | inl s => option_map inl (reifyStatesFin env s)
    | inr c => option_map inr (reifyTapeSigmaFin env c)
    end. 


  Lemma reifyGammaFin_canonical : reifyCanonical reifyGammaFin. 
  Proof. 
    unfold reifyCanonical. intros; split; [intros | intros (e & H)] ;  
      repeat match goal with
              | [H : fStates |- _ ] => destruct H; cbn in *
              | [H : fGamma |- _ ] => destruct H; cbn in *
              | [H : fpolarity |- _] => destruct H; cbn in *
              | [H : fpolSigma |- _] => destruct H; cbn in *
              | [H : fstateSigma |- _] => destruct H; cbn in *
              | [H : ftapeSigma |- _] => destruct H; cbn in *
              | [H : delim |- _ ] => destruct H; cbn in *
              | [H : _ /\ _ |- _] => destruct H
              | [H : boundVar _ _ |- _ ] => apply nth_error_Some in H
              | [ |- context[nth_error ?a ?b ]] => destruct (nth_error a b) eqn:?; cbn in *
              | [ |- _ /\ _] => split 
              | _ => match type of H with context[nth_error ?a ?b ] => destruct (nth_error a b) eqn:?; cbn in * end 
              | [H : nth_error _ _ = Some _ |- _ ] => apply MoreBase.nth_error_Some_lt in H
      end; eauto; try congruence. 
  Qed. 

  (*reification to flat representation (natural numbers) *)
  Definition flatPolarity := 3.
  Definition flatDelim := 1. 
  Definition flatDelimC := 0.
  Definition flatSigma := length (elem Sigma). 
  Definition flatstates := length (elem states). 

  Definition flattenPolarity (p : polarity) := index p. 

  Notation flatStateSigma := (flatOption flatSigma).
  Notation flatPolSigma := (flatProd flatPolarity flatStateSigma).
  Notation flatTapeSigma := (flatSum flatDelim flatPolSigma).
  Notation flatStates := (flatProd flatstates flatStateSigma).
  Notation flatGamma := (flatSum flatStates flatTapeSigma). 

  Definition reifyPolarityFlat (env : evalEnvFlat) (c : fpolarity) :=
    match c with
    | polConst c => Some (flattenPolarity c)
    | polVar n => nth_error (polarityEnv env) n
    end. 
  Definition reifyStateSigmaFlat (env : evalEnvFlat) (c : fstateSigma) :=
    match c with
    | blank => Some (flatNone)
    | someSigmaVar v => option_map flatSome (nth_error (sigmaEnv env) v)
    | stateSigmaVar v => nth_error (stateSigmaEnv env) v
  end. 

  Definition reifyPolSigmaFlat (env : evalEnvFlat) (c : fpolSigma) :=
    match c with
    | (p, s) => do p <- reifyPolarityFlat env p;
                do s <- reifyStateSigmaFlat env s;
                optReturn (flatPair flatPolarity flatStateSigma p s)
    end. 

  Definition reifyTapeSigmaFlat (env : evalEnvFlat) (c : ftapeSigma) :=
    match c with
    | inl delimC => Some (flatDelimC)
    | inr c => option_map (flatInr flatDelim) (reifyPolSigmaFlat env c)
    end.

  Definition reifyStatesFlat (env : evalEnvFlat) (c : fStates) :=
    match c with
    | (v, s) => do p <- nth_error (stateEnv env) v;
                do s <- reifyStateSigmaFlat env s;
                optReturn (flatPair flatstates flatStateSigma p s)
    end. 

  Definition reifyGammaFlat (env : evalEnvFlat) (c : fGamma) :=
    match c with
    | inl s => option_map (flatInl) (reifyStatesFlat env s)
    | inr c => option_map (flatInr flatStates) (reifyTapeSigmaFlat env c)
    end. 

  Ltac destruct_fGamma :=
    match goal with
      | [H : fStates |- _ ] => destruct H
      | [H : fGamma |- _ ] => destruct H
      | [H : fpolarity |- _] => destruct H
      | [H : fpolSigma |- _] => destruct H
      | [H : fstateSigma |- _] => destruct H
      | [H : ftapeSigma |- _] => destruct H
      | [H : delim |- _ ] => destruct H
      end. 

  Lemma reifyGammaFlat_canonical : reifyCanonical reifyGammaFlat.
  Proof.
    unfold reifyCanonical.
    intros; split; [intros | intros (e & H)] ;
    repeat match goal with
      | _ => destruct_fGamma; cbn in *
      | [H : _ /\ _ |- _] => destruct H
      | [H : boundVar _ _ |- _ ] => apply nth_error_Some in H
      | [ |- context[nth_error ?a ?b ]] => destruct (nth_error a b) eqn:?; cbn in *
      | [ |- _ /\ _] => split 
      | _ => match type of H with context[nth_error ?a ?b ] => destruct (nth_error a b) eqn:?; cbn in * end 
      | [H : nth_error _ _ = Some _ |- _ ] => apply MoreBase.nth_error_Some_lt in H
      end; eauto; try congruence. 
  Qed.

  (** *We now prove that the outputs of both reification procedures are related via finReprEl *)

  Lemma flattenPolarity_reprEl p : finReprEl flatPolarity (flattenPolarity p) p. 
  Proof. 
    unfold finReprEl. 
    split; [ | split]. 
    - unfold finRepr. unfold flatPolarity. unfold elem. now cbn.
    - destruct p; unfold flatPolarity; cbn; lia. 
    - destruct p; cbn; lia.
  Qed. 

  Definition isFlatListOf (X : finType) (l : list nat) (l' : list X) := l = map index l'. 

  Lemma isFlatListOf_Some1 (T : finType) (T' : nat) (a : list nat) (b : list T) (n : nat) (x : nat):
    finRepr T T' -> isFlatListOf a b -> nth_error a n = Some x -> exists x', nth_error b n = Some x' /\ finReprEl T' x x'.
  Proof. 
    intros. rewrite H0 in H1. rewrite utils.nth_error_map in H1. 
    destruct (nth_error b n); cbn in H1; [ | congruence ]. 
    inv H1. exists e.
    split; [reflexivity | repeat split]. 
    + apply H. 
    + rewrite H. apply index_le. 
  Qed. 

  Definition isFlatEnvOf (a : evalEnvFlat) (b : evalEnvFin) :=
    isFlatListOf (polarityEnv a) (polarityEnv b)
    /\ isFlatListOf (sigmaEnv a) (sigmaEnv b)
    /\ isFlatListOf (stateSigmaEnv a) (stateSigmaEnv b)
    /\ isFlatListOf (stateEnv a) (stateEnv b).

  Lemma Sigma_finRepr : finRepr Sigma flatSigma. 
  Proof. easy. Qed. 

  Lemma states_finRepr : finRepr states flatstates. 
  Proof. easy. Qed. 

  Smpl Create finRepr. 
  Smpl Add (apply Sigma_finRepr) : finRepr.
  Smpl Add (apply states_finRepr) : finRepr.
  Smpl Add (apply finReprElPair) : finRepr.
  Smpl Add (apply finReprElNone) : finRepr. 
  Smpl Add (apply finReprElSome) : finRepr.
  Smpl Add (apply finReprElInl) : finRepr.
  Smpl Add (apply finReprElInr) : finRepr. 

  Smpl Add (apply finReprProd) : finRepr.
  Smpl Add (apply finReprOption) : finRepr.
  Smpl Add (apply finReprSum) : finRepr. 

  Smpl Add (apply flattenPolarity_reprEl) : finRepr. 

  Ltac finRepr_simpl := smpl finRepr; repeat smpl finRepr. 

  Lemma delimC_reprEl : finReprEl flatDelim flatDelimC delimC.  
  Proof. 
    split; [ | split]. 
    - unfold finRepr. auto. 
    - auto. 
    - auto. 
  Qed. 

  Smpl Add (apply delimC_reprEl) : finRepr. 

  (*only the number of elements in an environment is relevant for boundedness *)
  Lemma isFlatEnvOf_bound_Gamma_transfer (envFlat : evalEnvFlat) (envFin : evalEnvFin) (c : fGamma) :
    isFlatEnvOf envFlat envFin -> bound_Gamma envFin c <-> bound_Gamma envFlat c. 
  Proof. 
    intros (H1 & H2 & H3 & H4). 
    destruct c; cbn in *.
    - destruct f; cbn. destruct f; cbn.
      + rewrite H4. unfold boundVar. rewrite map_length. tauto.
      + rewrite H4, H2; unfold boundVar. rewrite !map_length. tauto.
      + rewrite H4, H3; unfold boundVar. rewrite !map_length; tauto.
    - destruct f; cbn; [tauto | ]. 
      destruct f; cbn. destruct f, f0; cbn. 
      all: try rewrite H1; try rewrite H2; try rewrite H3; try rewrite H4.
      all: unfold boundVar; try rewrite !map_length; tauto.  
  Qed. 

  Lemma reifyGamma_reprEl a b d :
    isFlatEnvOf a b -> bound_Gamma a d
    -> exists e1 e2, reifyGammaFin b d = Some e1 /\ reifyGammaFlat a d = Some e2 /\ finReprEl flatGamma e2 e1. 
  Proof.
    intros.
    specialize (proj1 (reifyGammaFlat_canonical _ _ ) H0 ) as (e1 & H1). 
    eapply (isFlatEnvOf_bound_Gamma_transfer ) in H0. 2: apply H. 
    specialize (proj1 (reifyGammaFin_canonical _ _ ) H0) as (e2 & H2). 
    exists e2, e1. split; [apply H2 | split; [ apply H1 | ]]. 
    destruct H as (F1 & F2 & F3 & F4).
    repeat match goal with
      | _ => destruct_fGamma; cbn -[Nat.mul flatSum flatGamma index] in *
      | _ => match type of H1 with context[nth_error ?a ?b ] =>
            let Heqn := fresh "H" "eqn" in 
            let Heqn2 := fresh "H" "eqn" in 
            destruct (nth_error a b) eqn:Heqn; cbn -[Nat.mul flatSum flatGamma index] in *;
              try (eapply isFlatListOf_Some1 in Heqn as (? & Heqn2 & ?);
                    [ | | eauto ];
                    [ setoid_rewrite Heqn2 in H2; cbn -[Nat.mul flatSum flatGamma index] in *
                    | finRepr_simpl]
                  )
            end
            | [H : Some _ = Some _ |- _] => inv H
    end; try congruence. 
    all: eauto; finRepr_simpl; eauto. 
  Qed. 

  (** *reification of rewrite windows *)

  Definition reifyWindow (X Y Z W M: Type) (r : evalEnv X Y Z W -> fGamma -> option M) (env : evalEnv X Y Z W) rule :=
    match rule with {a, b, c} / {d, e, f} =>
                      do a <- r env a;
                      do b <- r env b;
                      do c <- r env c;
                      do d <- r env d;
                      do e <- r env e;
                      do f <- r env f;
                      optReturn ({a, b, c} / {d, e, f})
    end.

  Definition bound_WinP {X Y Z W : Type} (env : evalEnv X Y Z W) (c : TCSRWinP fGamma) :=
    bound_Gamma env (winEl1 c) /\ bound_Gamma env (winEl2 c) /\ bound_Gamma env (winEl3 c). 
  Definition bound_window {X Y Z W : Type} (env : evalEnv X Y Z W) (c : window fGamma) :=
    bound_WinP env (prem c) /\ bound_WinP env (conc c).

  Lemma isFlatEnvOf_bound_window_transfer (envFlat : evalEnvFlat) (envFin : evalEnvFin) (c : window fGamma) :
    isFlatEnvOf envFlat envFin -> (bound_window envFlat c <-> bound_window envFin c). 
  Proof. 
    intros H. destruct c, prem, conc; cbn. unfold bound_window, bound_WinP; cbn.  
    split; intros ((F1 & F2 & F3) & (F4 & F5 & F6)); repeat split.
    all: now apply (isFlatEnvOf_bound_Gamma_transfer _ H). 
  Qed.

  (*for canonical reification procedures, reifyWindow works as intended *)
  Lemma reifyWindow_Some (X Y Z W M : Type) (r : evalEnv X Y Z W -> fGamma -> option M) (env : evalEnv X Y Z W) rule :
    reifyCanonical r
    -> (bound_window env rule <-> exists w, reifyWindow r env rule = Some w). 
  Proof.
    intros. split.
    + intros ((H1 & H2 & H3) & (H4 & H5 & H6)).
      unfold reifyWindow. 
      destruct rule, prem, conc; cbn in *. 
      apply H in H1 as (? & ->).
      apply H in H2 as (? & ->).
      apply H in H3 as (? & ->).
      apply H in H4 as (? & ->).
      apply H in H5 as (? & ->).
      apply H in H6 as (? & ->).
      cbn. eauto.
    + intros (w & H1). 
      unfold bound_window, bound_WinP.
      destruct rule, prem, conc. cbn in *.
      repeat match type of H1 with
              | context[r ?h0 ?h1] => let H := fresh "H" in destruct (r h0 h1) eqn:H
      end; cbn in *; try congruence. 
      repeat split; apply H; eauto. 
  Qed. 

  (*lifting of finReprEl to rewrite windows *)
  Definition isFlatWinPOf (X : finType) (x : nat)(b : TCSRWinP nat) (a : TCSRWinP X) :=
    finReprEl x (winEl1 b) (winEl1 a) /\ finReprEl x (winEl2 b) (winEl2 a) /\ finReprEl x (winEl3 b) (winEl3 a).  

  Definition isFlatWindowOf (X : finType) (x : nat) (b : window nat) (a : window X):=
    isFlatWinPOf x (prem b) (prem a) /\ isFlatWinPOf x (conc b) (conc a) . 

  (*the output of reifyWindow is related via isFlatWindowOf for the two reification procedures *)
  Lemma reifyWindow_isFlatWindowOf envFlat envFin rule :
    bound_window envFlat rule -> isFlatEnvOf envFlat envFin -> exists e1 e2, reifyWindow reifyGammaFlat envFlat rule = Some e1 /\ reifyWindow reifyGammaFin envFin rule = Some e2 /\ isFlatWindowOf flatGamma e1 e2. 
  Proof.
    intros.
    specialize (proj1 (isFlatEnvOf_bound_window_transfer _ H0) H) as H'.
    destruct (proj1 (reifyWindow_Some _ _ reifyGammaFin_canonical) H') as (win & H1).  
    clear H'. 
    destruct (proj1 (reifyWindow_Some _ _ reifyGammaFlat_canonical) H) as (win' & H2).
    exists win', win. split; [apply H2 | split; [apply H1 | ]]. 
    destruct rule, prem, conc.
    cbn in H1, H2. 
    destruct H as ((F1 & F2 & F3) & (F4 & F5 & F6)); cbn in *. 
    repeat match goal with
    | [H : bound_Gamma _ _ |- _] =>
      let H1 := fresh "H" in let H2 := fresh "H" in
        destruct (reifyGamma_reprEl H0 H) as (? & ? & H1 & H2 & ?);
        rewrite H1 in *; rewrite H2 in *;
        clear H1 H2 H
    end. 
    cbn in *. inv H1. inv H2. 
    split; (split; [ | split]); cbn; eauto.
  Qed. 

  (*list_prod: cons every element of the first list to every element of the second list*)
  Fixpoint list_prod (X : Type) (l : list X) (l' : list (list X)) : list (list X) :=
    match l with [] => []
            | (h :: l) => map (fun l => h :: l) l' ++ list_prod l l'
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

  (*an environment containing all combinations of n elements is created by iterating list_prod*)
  Definition mkVarEnv (X : Type) (l : list X) (n : nat) :=
    it (fun acc => list_prod l acc ++ acc) n [[]].

  Lemma in_mkVarEnv_iff (X : Type) (l : list X) (n : nat) (l' : list X) :
    l' el mkVarEnv l n <-> |l'| <= n /\ l' <<= l. 
  Proof.
    revert l'. 
    induction n; intros l'; cbn. 
    - split.
      + intros [<- | []]. eauto.
      + intros (H1 & H2); destruct l'; [eauto | cbn in H1; lia]. 
    - rewrite in_app_iff. rewrite in_list_prod_iff. split.
      + intros [(? & ? & -> & H1 & H2) | H1].
        * unfold mkVarEnv in IHn. apply IHn in H2 as (H2 & H3).
          split; [now cbn | cbn; intros a [-> | H4]; eauto ].  
        * apply IHn in H1 as (H1 & H2). split; eauto. 
      + intros (H1 & H2).
        destruct (nat_eq_dec (|l'|) (S n)). 
        * destruct l'; cbn in *; [congruence | ].
          apply incl_lcons in H2 as (H2 & H3).
          assert (|l'| <= n) as H1' by lia. clear H1. 
          specialize (proj2 (IHn l') (conj H1' H3)) as H4.
          left. exists x, l'. eauto. 
        * right. apply IHn. split; [lia | eauto]. 
  Qed. 

  Definition tupToEvalEnv (X Y Z W : Type) (t : (list X) * (list Y) * (list Z) * (list W)) :=
    match t with
    | (t1, t2, t3, t4) => Build_evalEnv t1 t2 t3 t4
    end.

  (*this is now lifted to evalEnv *)
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

  (*instantiate all rules - the resulting list is ordered by rules *)

  Definition makeRules' (X Y Z W M : Type) (reify : evalEnv X Y Z W -> fGamma -> option M)  (l : list (evalEnv X Y Z W)) rule :=
    filterSome (map (fun env => reifyWindow reify env  rule) l).

  Definition makeRules (X Y Z W M : Type) (reify : evalEnv X Y Z W -> fGamma -> option M) (allX : list X) (allY : list Y) (allZ : list Z) (allW : list W) n1 n2 n3 n4 (rules : list (window fGamma)) :=
    let listEnv := makeAllEvalEnv allX allY allZ allW n1 n2 n3 n4 in
    concat (map (makeRules' reify listEnv) rules).

  Lemma in_makeRules'_iff (X Y Z W M : Type) (reify : evalEnv X Y Z W -> fGamma -> option M) (l : list (evalEnv X Y Z W)) rule window :
    window el makeRules' reify l rule <-> exists env, env el l /\ Some window = reifyWindow reify env rule. 
  Proof.
    unfold makeRules'. rewrite in_filterSome_iff. rewrite in_map_iff. split.
    - intros (? & H1 & H2). exists x. now rewrite H1. 
    - intros (env & H1 & ->). now exists env. 
  Qed. 

  Lemma in_makeRules_iff (X Y Z W M : Type) (reify : evalEnv X Y Z W -> fGamma -> option M) (allX : list X) (allY : list Y) (allZ : list Z) (allW : list W) n1 n2 n3 n4 rules window :
    window el makeRules reify allX allY allZ allW n1 n2 n3 n4 rules <-> exists env rule, rule el rules /\ env el makeAllEvalEnv allX allY allZ allW n1 n2 n3 n4 /\ Some window = reifyWindow reify env rule. 
  Proof.
    unfold makeRules. rewrite in_concat_iff. split.
    - intros (l' & H1 & (rule & <- & H2)%in_map_iff). 
      apply in_makeRules'_iff in H1 as (env & H3 & H4).
      exists env, rule. eauto.
    - intros (env & rule & H1 & H2 & H3).
      setoid_rewrite in_map_iff.
      exists (makeRules' reify (makeAllEvalEnv allX allY allZ allW n1 n2 n3 n4) rule). 
      split.
      + apply in_makeRules'_iff. eauto.
      + eauto.  
  Qed. 

  Definition makeRulesFin := makeRules reifyGammaFin. 
  Definition makeRulesFlat := makeRules reifyGammaFlat. 

  Definition list_finReprEl (X : finType) (x : nat) (A : list nat) (B : list X)  :=
    (forall n, n el A -> exists a, finReprEl x n a /\ a el B) /\ (forall b, b el B -> exists n, finReprEl x n b /\ n el A). 

  Lemma isFlatListOf_list_finReprEl (X : finType) (x : nat) (A : list nat) (B : list X) :
    finRepr X x
    -> isFlatListOf A B
    -> list_finReprEl x A B. 
  Proof.
    intros. rewrite H0; clear H0. unfold list_finReprEl. split.
    - intros. apply in_map_iff in H0 as (x' & <- & H0).
      exists x'. split; [ repeat split | apply H0].
      + apply H.
      + rewrite H. apply index_le. 
    - intros. exists (index b). split; [ | apply in_map_iff; eauto]. 
      split; [ apply H| split; [ | reflexivity]]. 
      rewrite H. apply index_le. 
  Qed.  

  Definition list_isFlatEnvOf (envFlatList : list evalEnvFlat) (envFinList : list evalEnvFin) :=
    (forall envFlat, envFlat el envFlatList -> exists envFin, isFlatEnvOf envFlat envFin /\ envFin el envFinList)
    /\ (forall envFin, envFin el envFinList -> exists envFlat, isFlatEnvOf envFlat envFin /\ envFlat el envFlatList).

  Lemma isFlatListOf_incl1 (X : finType) (fin : list X) flat l:
    isFlatListOf flat fin -> l <<= flat -> exists l', isFlatListOf (X := X) l l' /\ l' <<= fin.
  Proof.
    intros. revert fin H. induction l; cbn in *; intros. 
    - exists []; split; eauto. unfold isFlatListOf. now cbn.
    - apply incl_lcons in H0 as (H0 & H1).
      apply IHl with (fin := fin) in H1 as (l' & H2 & H3). 
      2: apply H. 
      rewrite H in H0. apply in_map_iff in H0 as (a' & H4 & H5).
      exists (a' :: l'). split. 
      + unfold isFlatListOf. cbn. now rewrite <- H4, H2. 
      + cbn. intros ? [-> | H6]; eauto.
  Qed.

  Lemma isFlatListOf_incl2 (X : finType) (fin : list X) flat l':
    isFlatListOf flat fin -> l' <<= fin -> exists l, isFlatListOf (X := X) l l' /\ l <<= flat.
  Proof.
    intros.
    exists (map index l'). split.
    - reflexivity.
    - induction l'; cbn. 
      + eauto.
      + apply incl_lcons in H0 as (H0 & H1).
        apply IHl' in H1. intros ? [<- | H2].
        * rewrite H. apply in_map_iff; eauto. 
        * now apply H1.  
  Qed. 

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

  Definition list_isFlatWindowOf (windowFlatList : list (window nat)) (windowFinList : list (window Gamma)) :=
    (forall w, w el windowFlatList -> exists w', isFlatWindowOf flatGamma w w' /\ w' el windowFinList) /\ (forall w', w' el windowFinList -> exists w, isFlatWindowOf flatGamma w w' /\ w el windowFlatList). 

  Lemma makeRules'_isFlatWindowOf  (envFlatList : list evalEnvFlat) (envFinList : list evalEnvFin) rule :
    list_isFlatEnvOf envFlatList envFinList ->
    list_isFlatWindowOf (makeRules' reifyGammaFlat envFlatList rule) (makeRules' reifyGammaFin envFinList rule).
  Proof. 
    intros. split; intros. 
    - apply in_makeRules'_iff in H0 as (env & H1 & H2).
      symmetry in H2.
      apply H in H1 as (env' & H3 & H4). 
      assert (exists w, reifyWindow reifyGammaFlat env rule = Some w) by eauto.
      eapply (reifyWindow_Some env rule reifyGammaFlat_canonical) in H0. 
      eapply isFlatEnvOf_bound_window_transfer  in H0 as H0'. 
      2: apply H3. 
      specialize (proj1 (reifyWindow_Some env' rule reifyGammaFin_canonical) H0') as (w' & H1). 
      exists w'. split.
      + destruct (reifyWindow_isFlatWindowOf H0 H3) as (? & ? & F1 & F2 & F3).  
        rewrite F1 in H2. rewrite F2 in H1. inv H2. inv H1. apply F3. 
      + apply in_makeRules'_iff. exists env'. eauto.
  - apply in_makeRules'_iff in H0 as (env & H1 & H2). 
    symmetry in H2.
      apply H in H1 as (env' & H3 & H4). 
      assert (exists w, reifyWindow reifyGammaFin env rule = Some w) by eauto.
      eapply (reifyWindow_Some env rule reifyGammaFin_canonical) in H0. 
      eapply isFlatEnvOf_bound_window_transfer  in H0 as H0'. 
      2: apply H3. 
      specialize (proj1 (reifyWindow_Some env' rule reifyGammaFlat_canonical) H0') as (w & H1). 
      exists w. split.
      + destruct (reifyWindow_isFlatWindowOf H0' H3) as (? & ? & F1 & F2 & F3).  
        rewrite F1 in H1. rewrite F2 in H2. inv H2. inv H1. apply F3. 
      + apply in_makeRules'_iff. exists env'. eauto.
  Qed. 

  Lemma makeRules_isFlatWindowOf (Afin : list polarity) (Bfin : list Sigma) (Cfin : list stateSigma) (Dfin : list states) (Aflat Bflat Cflat Dflat : list nat) n1 n2 n3 n4 rules :
    isFlatListOf Aflat Afin
    -> isFlatListOf Bflat Bfin
    -> isFlatListOf Cflat Cfin
    -> isFlatListOf Dflat Dfin
    -> list_isFlatWindowOf (makeRulesFlat Aflat Bflat Cflat Dflat n1 n2 n3 n4 rules) (makeRulesFin Afin Bfin Cfin Dfin n1 n2 n3 n4 rules).
  Proof. 
    intros. split. 
    - intros. unfold makeRulesFlat, makeRulesFin, makeRules in H3. 
      apply in_concat_iff in H3 as (windows & H3 & H4). 
      apply in_map_iff in H4 as (rule & <- & H5). 
      specialize (makeAllEvalEnv_isFlatEnvOf n1 n2 n3 n4 H H0 H1 H2) as F.
      apply (makeRules'_isFlatWindowOf rule) in F.
      apply F in H3 as (w' & F1 & F2). exists w'.  
      split; [ apply F1 | ]. 
      unfold makeRulesFin, makeRules. apply in_concat_iff. 
      eauto 10.
    - intros. unfold makeRulesFin, makeRules in H3. 
      apply in_concat_iff in H3 as (windows & H3 & H4). 
      apply in_map_iff in H4 as (rule & <- & H5). 
      specialize (makeAllEvalEnv_isFlatEnvOf n1 n2 n3 n4 H H0 H1 H2) as F.
      apply (makeRules'_isFlatWindowOf rule) in F.
      unfold list_isFlatWindowOf in F. 
      apply F in H3 as (w & F1 & F2). exists w.  
      split; [ apply F1 | ]. 
      unfold makeRulesFin, makeRulesFlat, makeRules. apply in_concat_iff. 
      eauto 10. 
  Qed. 
 
  Lemma finType_enum_list_finReprEl (T : finType) : list_finReprEl (length (elem T))  (seq 0 (length (elem T))) (elem T). 
  Proof. 
    unfold list_finReprEl. split.
    - intros. apply in_seq in H. destruct (nth_error (elem T) n ) eqn:H1.  
      + exists e. split; [ | now apply nth_error_In in H1 ].
        split; [ | split].
        * easy. 
        * easy. 
        * apply nth_error_nth in H1. rewrite <- H1. apply getPosition_nth. 2: easy.
          apply dupfree_elements.   
      + destruct H. cbn in H0. apply nth_error_Some in H0. congruence. 
    - intros. exists (getPosition (elem T) b). apply In_nth with (d := b) in H as (n & H1 & <-). split.
      + split; [ | split]. 
        * easy. 
        * rewrite getPosition_nth; auto. apply dupfree_elements. 
        * reflexivity.
      + rewrite getPosition_nth; [ | | assumption].
        * apply in_seq.  lia. 
        * apply dupfree_elements. 
  Qed. 

  Lemma isFlatWindowOf_map_index (X : finType) (x : nat) (win : window X) (win' : window nat) :
    isFlatWindowOf x win' win -> (prem win' : list nat) = map index (prem win) /\ (conc win' : list nat) = map index (conc win). 
  Proof. 
    intros ((H1 & H2 & H3) & (F1 & F2 & F3)). 
    destruct win. destruct prem, conc. cbn in *. 
    cbn [TCSR.winEl1 TCSR.winEl2 TCSR.winEl3] in *.
    repeat match goal with
            | [H : finReprEl _ _ _ |- _] => rewrite (proj2 (proj2 H)); clear H
    end. 
    destruct win', prem, conc. now cbn. 
  Qed. 

  Lemma rewritesHeadList_flat_agree rulesFin rulesFlat finStr finStr' flatStr flatStr' :
    isFlatListOf flatStr finStr
    -> isFlatListOf flatStr' finStr'
    -> list_isFlatWindowOf rulesFlat rulesFin 
    -> (rewritesHeadList rulesFin finStr finStr' <-> rewritesHeadList rulesFlat flatStr flatStr'). 
  Proof. 
    intros. unfold rewritesHeadList. split; intros (rule & H2 & H3).
    - apply H1 in H2 as (rule' & F1 & F2). exists rule'. split; [apply F2 | ]. 
      unfold rewritesHead, prefix in *. destruct H3 as ((b1 & ->) & (b2 & ->)). 
      unfold isFlatListOf in H, H0.
      rewrite map_app in H, H0. split.
      + exists (map index b1). rewrite H. enough (map index (prem rule) = prem rule') as H2.
        { now setoid_rewrite H2. }
        destruct rule; cbn. destruct prem. 
        apply isFlatWindowOf_map_index in F1. 
        rewrite (proj1 F1). now cbn. 
      + exists (map index b2). rewrite H0. enough (map index (conc rule) = conc rule') as H2. 
        { now setoid_rewrite H2. }
        destruct rule; cbn. destruct conc.
        apply isFlatWindowOf_map_index in F1.
        rewrite (proj2 F1). now cbn. 
    - apply H1 in H2 as (rule' & F1 & F2). exists rule'. split; [ apply F2 | ].
      unfold rewritesHead, prefix in *. destruct H3 as ((b1 & ->) & (b2 & ->)).
      unfold isFlatListOf in H, H0. split.
      + symmetry in H. apply map_eq_app in H as (finStr1  & finStr2 & -> & ? & ?). 
        exists finStr2.
        enough (finStr1 = prem rule') as H3 by (now setoid_rewrite H3).
        apply isFlatWindowOf_map_index in F1. destruct F1 as (F1 & _).  rewrite F1 in H. 
        apply Prelim.map_inj in H; [easy | unfold injective; apply injective_index]. 
      + symmetry in H0. apply map_eq_app in H0 as (finStr1  & finStr2 & -> & ? & ?). 
        exists finStr2.
        enough (finStr1 = conc rule') as H3 by (now setoid_rewrite H3).
        apply isFlatWindowOf_map_index in F1. destruct F1 as (_ & F1). rewrite F1 in H0. 
        apply Prelim.map_inj in H0; [easy | unfold injective; apply injective_index].
  Qed. 

  Lemma valid_flat_agree rulesFin rulesFlat finStr finStr' flatStr flatStr' :
    isFlatListOf flatStr finStr
    -> isFlatListOf flatStr' finStr'
    -> list_isFlatWindowOf rulesFlat rulesFin 
    -> valid (rewritesHeadList rulesFin) finStr finStr' <-> valid (rewritesHeadList rulesFlat) flatStr flatStr'. 
  Proof.
    intros. 
    split.
    - intros H2. revert flatStr flatStr' H0 H. induction H2; intros.
      + rewrite H, H0; cbn; constructor 1.  
      + rewrite H3, H0. cbn [map]. constructor.
        * now eapply IHvalid.
        * rewrite map_length. auto.
      + rewrite H3, H0. cbn [map]. constructor 3. 
        * now eapply IHvalid.
        * eapply rewritesHeadList_flat_agree.
          -- rewrite <- H3. apply H3. 
          -- rewrite <- H0. apply H0. 
          -- apply H1. 
          -- apply H. 
    - intros H2. revert finStr finStr' H0 H. induction H2; intros. 
      + destruct finStr; [ | now unfold isFlatListOf in H].
        destruct finStr'; [ | now unfold isFlatListOf in H0].
        constructor. 
      + unfold isFlatListOf in H0, H3. 
        destruct finStr; cbn [map] in H3; [ congruence | ].
        destruct finStr'; cbn [map] in H0; [congruence | ]. 
        inv H0; inv H3. constructor 2. 
        2: now rewrite map_length in H. 
        apply IHvalid; easy. 
      + unfold isFlatListOf in H0, H3.
        destruct finStr; cbn [map] in H3; [ congruence | ].
        destruct finStr'; cbn [map] in H0; [congruence | ]. 
        inv H0; inv H3. constructor 3. 
        * eapply IHvalid; easy.
        * eapply rewritesHeadList_flat_agree. 
          4: apply H.
          -- easy.
          -- easy. 
          -- apply H1. 
  Qed. 

  Notation "f $ x" := (f x) (at level 60, right associativity, only parsing).

  

  (*general results for agreement *)
  Definition rules_list_ind_agree {X : Type} (p : X -> X -> X -> X -> X -> X -> Prop) (l : list (window X)) :=
    forall x1 x2 x3 x4 x5 x6, p x1 x2 x3 x4 x5 x6 <-> {x1, x2, x3} / {x4, x5, x6} el l. 

  Lemma agreement_rewritesHead {X : Type} (p : X -> X -> X -> X -> X -> X -> Prop) (l : list (window X)) :
    rules_list_ind_agree p l -> forall s1 s2, (rewritesHeadInd p s1 s2 <-> rewritesHeadList l s1 s2). 
  Proof. 
    intros; split; intros. 
    + inv H0. exists ({x1, x2, x3} / {x4, x5, x6}). split.
      * apply H, H1. 
      * split; unfold prefix; cbn; eauto. 
    + destruct H0 as (r & H1 & ((b & ->) & (b' & ->))). 
      destruct r, prem, conc; cbn. constructor. apply H, H1.  
  Qed.

  (*definition of list-based rules *)
  Definition mtrRules : list (window fGamma):=
    [
      {inr $ inr (polVar 0, someSigmaVar 0), inr (inr (polVar 0, someSigmaVar 1)), inr (inr (polVar 0, someSigmaVar 2))} / {inr (inr (polConst positive, someSigmaVar 3)), inr (inr (polConst positive, someSigmaVar 0)), inr (inr (polConst positive, someSigmaVar 1))};
      {inr (inr (polVar 0, blank)), inr (inr (polVar 0, blank)), inr (inr (polVar 0, blank))} / {inr (inr (polConst positive, someSigmaVar 0)), inr (inr (polConst positive, blank)), inr (inr (polConst positive, blank))};
      { inr (inr (polVar 0, someSigmaVar 0)), inr (inr (polVar 0, blank)), inr (inr (polVar 0, blank))} / {inr (inr (polConst positive, someSigmaVar 1)), inr (inr (polConst positive, someSigmaVar 0)), inr (inr (polConst positive, blank))};
      { inr (inr (polVar 0, blank)), inr (inr (polVar 0, blank)), inr (inr (polVar 0, blank))} / {inr (inr (polConst positive, blank)), inr (inr (polConst positive, blank)), inr (inr (polConst positive, blank))};
      { inr (inr (polVar 0, someSigmaVar 0)), inr (inr (polVar 0, someSigmaVar 1)), inr (inr (polVar 0, blank)) } / {inr (inr (polConst positive, someSigmaVar 2)), inr (inr (polConst positive, someSigmaVar 0)), inr (inr (polConst positive, someSigmaVar 1))};
      { inr (inr (polVar 0, blank)), inr (inr (polVar 0, blank)), inr (inr (polVar 0, someSigmaVar 0))} / { inr (inr (polConst positive, blank)), inr (inr (polConst positive, blank)), inr (inr (polConst positive, blank))};
      { inr (inr (polVar 0, blank)), inr (inr (polVar 0, someSigmaVar 0)), inr (inr (polVar 0, someSigmaVar 1))} / { inr (inr (polConst positive, blank)), inr (inr (polConst positive, blank)), inr (inr (polConst positive, someSigmaVar 0))};
      { inr (inr (polVar 0, someSigmaVar 0)), inr (inr (polVar 0, someSigmaVar 1)), inr (inr (polVar 0, someSigmaVar 2))} / {inr (inr (polConst positive, blank)), inr (inr (polConst positive, someSigmaVar 0)), inr (inr (polConst positive, someSigmaVar 1))}
    ].

  Definition mtiRules : list (window fGamma) :=
    [
      {inr (inr (polVar 0, stateSigmaVar 0)), inr (inr (polVar 0, stateSigmaVar 1)), inr (inr (polVar 0, stateSigmaVar 2))} / {inr (inr (polConst neutral, stateSigmaVar 0)), inr (inr (polConst neutral, stateSigmaVar 1)), inr (inr (polConst neutral, stateSigmaVar 2))};
        {inr (inl (delimC)), inr (inr (polVar 0, blank)), inr (inr (polVar 0, blank))} / {inr (inl (delimC)), inr (inr (polVar 1, blank)), inr (inr (polVar 1, blank))};
        {inr (inr (polVar 0, blank)), inr (inr (polVar 0, blank)), inr (inl delimC)} / {inr (inr (polVar 1, blank)), inr (inr (polVar 1, blank)), inr (inl delimC)}
    ].

  Definition finMTRRules := makeRulesFin (elem Fpolarity) (elem Sigma) (elem FstateSigma) (elem states) 1 4 0 0 mtrRules. 
  Definition finMTIRules := makeRulesFin (elem Fpolarity) (elem Sigma) (elem FstateSigma) (elem states) 2 0 4 0 mtiRules.
  Definition finMTLRules := map polarityRevWin finMTRRules. 

  Definition finTapeRules := finMTRRules ++ finMTIRules ++ finMTLRules. 

  Ltac destruct_or H := match type of H with
                        | ?a \/ ?b => destruct H as [H | H]; try destruct_or H
                          end.

  Lemma singleton_incl (X : Type) (a : X) (h : list X) :
    [a] <<= h <-> a el h. 
  Proof. 
    split; intros. 
    - now apply H. 
    - now intros a' [-> | []]. 
  Qed. 

  Lemma duoton_incl (X : Type) (a b : X) (h : list X) : 
    [a; b] <<= h <-> a el h /\ b el h.
  Proof. 
    split; intros.
    - split; now apply H. 
    - destruct H. now intros a' [-> | [-> | []]]. 
  Qed.

  Ltac force_in := match goal with
                    | [ |- ?a el ?a :: ?h] => now left
                    | [ |- ?a el ?b :: ?h] => right; force_in
                    | [ |- [?a] <<= ?h] => apply singleton_incl; force_in

                    end. 

  Lemma stateSigma_incl (l : list stateSigma) : l <<= elem (FstateSigma). 
  Proof. 
    unfold elem. cbn. 
    intros [] _.
    - right. eauto.  
    - now left. 
  Qed. 

  (*various tactics used for the prove of agreement *)
  Ltac solve_agreement_incl :=
    match goal with
      | [ |- [] <<= _] => eauto
      | [ |- ?a <<= elem Sigma] => eauto
      | [ |- [?p] <<= [negative; positive; neutral]] => destruct p; force_in
      | [ |- ?p el [negative; positive; neutral]] => destruct p; force_in
      | [ |- [?a; ?b] <<= ?h] => apply duoton_incl; split; solve_agreement_incl 
      | [ |- ?a <<= elem FstateSigma] => apply stateSigma_incl 
      | [ |- ?a <<= toOptionList (elem Sigma)] => apply stateSigma_incl
      | [ |- _ <= _] => lia
    end. 

  Ltac solve_agreement_in_env :=
    split; [force_in | split; [ apply in_makeAllEvalEnv_iff; cbn; repeat split; solve_agreement_incl| easy] ]. 

  Ltac destruct_var_env H :=
    repeat match type of H with
      | |?h| <= 0 => is_var h; destruct h; cbn in H; [clear H | now apply Nat.nle_succ_0 in H]
      | |?h| <= S ?n => is_var h; destruct h; cbn in H; [clear H | apply le_S_n in H]; destruct_var_env H
      end. 

  (*solve: an existential goal *)
  (*given a list of elements l, try to instantiate the existential with an element of l and then solve the remaining goal with cont *)
  Ltac rec_exists l cont:=
    match l with
    | [] => fail
    | ?a :: ?l => exists a; cont
    | ?a :: ?l => rec_exists l cont
    end. 

  Ltac solve_agreement_tape := unfold mtrRules, mtiRules; 
        match goal with
        | [ |- ex (fun r => r el ?h /\ _) ] => rec_exists h ltac:(solve_agreement_in_env)
        end.

  Lemma agreement_mtr: rules_list_ind_agree shiftRightRules finMTRRules. 
  Proof.
    unfold rules_list_ind_agree; intros; split. 
    - intros. rewHeadTape_inv2; apply in_makeRules_iff. 
      + exists (Build_evalEnv [p] [σ1; σ2; σ3; σ4] [] []). solve_agreement_tape. 
      + exists (Build_evalEnv [p] [σ1; σ1; σ1; σ1] [] []). solve_agreement_tape. 
      + exists (Build_evalEnv [p] [] [] []). solve_agreement_tape. 
      + exists (Build_evalEnv [p] [σ1; σ2] [] []). solve_agreement_tape. 
      + exists (Build_evalEnv [p] [σ1; σ2; σ3] [] []). solve_agreement_tape. 
      + exists (Build_evalEnv [p] [σ1] [] []). solve_agreement_tape. 
      + exists (Build_evalEnv [p] [σ1; σ2] [] []). solve_agreement_tape. 
      + exists (Build_evalEnv [p] [σ1; σ2; σ3] [] []). solve_agreement_tape. 
    - intros. apply in_makeRules_iff in H as (env & rule & H1 & H2 & H3).  
      destruct env. apply in_makeAllEvalEnv_iff in H2. 
      destruct H2 as ((F1 & _) & (F2 & _) & (F3 & _) & (F4 & _)). 
      destruct_var_env F1; destruct_var_env F3; destruct_var_env F4; destruct_var_env F2.  
      all: cbn in H1; destruct_or H1; subst; cbn in H3; inv H3; eauto. 
  Qed. 

  Lemma mtrRules_polarityRev γ1 γ2 γ3 γ4 γ5 γ6 :
    {~γ1, ~γ2, ~γ3} / {~γ4, ~γ5, ~γ6} el finMTRRules <-> {γ3, γ2, γ1} / {γ6, γ5, γ4} el finMTLRules. 
  Proof. 
    unfold finMTLRules. split; intros.
    - apply in_map_iff.
      exists ({~γ1, ~γ2, ~γ3} / {~γ4, ~γ5, ~γ6}). 
      split; [ | apply H]. 
      unfold polarityRevWin. cbn. rewrite !polarityFlipGamma_involution. reflexivity.
    - apply in_map_iff in H as (r & H1 & H2).
      apply involution_invert_eqn2 in H1. 2: involution_simpl.
      unfold polarityRevWin in H1. cbn in H1. subst; eauto.
  Qed. 

  Lemma agreement_mtl γ1 γ2 γ3 γ4 γ5 γ6 :
    shiftRightRules (~γ1) (~γ2) (~γ3) (~γ4) (~γ5) (~γ6) <-> {γ3, γ2, γ1} / {γ6, γ5, γ4} el finMTLRules.
  Proof. 
    split. 
    - intros. apply mtrRules_polarityRev. now apply agreement_mtr.
    - intros. apply mtrRules_polarityRev in H. now apply agreement_mtr.
  Qed. 

  Lemma agreement_mti: rules_list_ind_agree identityRules finMTIRules. 
  Proof. 
    unfold rules_list_ind_agree; intros. split.
    - intros. rewHeadTape_inv2; apply in_makeRules_iff. 
      + exists (Build_evalEnv [p] [] [m1; m2; m3] []). solve_agreement_tape. 
      + exists (Build_evalEnv [p; p'] [] [] []). solve_agreement_tape. 
      + exists (Build_evalEnv [p; p'] [] [] []). solve_agreement_tape. 
    - intros. apply in_makeRules_iff in H as (env & rule & H1 & H2 & H3).  
      destruct env. apply in_makeAllEvalEnv_iff in H2. 
      destruct H2 as ((F1 & _) & (F2 & _) & (F3 & _) & (F4 & _)). 
      destruct_var_env F1; destruct_var_env F3; destruct_var_env F4; destruct_var_env F2.  
      all: cbn in H1; destruct_or H1; subst; cbn in H3; inv H3; eauto.
  Qed. 

  Lemma agreement_tape : rules_list_ind_agree tapeRules finTapeRules.  
  Proof. 
    split; intros. 
    - unfold finTapeRules. rewrite !in_app_iff. inv H.
      + apply agreement_mtl in H0; eauto. 
      + apply agreement_mtr in H0; eauto. 
      + apply agreement_mti in H0; eauto. 
    - unfold finTapeRules in H. rewrite !in_app_iff in H. destruct_or H. 
      + apply agreement_mtr in H; eauto. 
      + apply agreement_mti in H; eauto. 
      + apply agreement_mtl in H; eauto. 
  Qed. 

  (** *agreement for transitions *)
  (*for the transition rules, the current and next state as well the read and written symbols are fixed *)
  (*still, we model them as variables, but do not instantiate them with all possible environments, but only with environments where these variables are fixed *)
  (*for that, we first generate the environments and then add the values of the constant variables *)

  (*add states and read/written symbols *)
  Definition transEnvAddSM (X Y Z W : Type) (q q' : W) (m m' : Z) (env : evalEnv X Y Z W) :=
    Build_evalEnv (polarityEnv env) (sigmaEnv env) (m :: m' :: stateSigmaEnv env) (q :: q' :: stateEnv env). 

  (*only add states (used for the None/None case) *)
  Definition transEnvAddS (X Y Z W : Type) (q q' : W) (env : evalEnv X Y Z W) :=
    Build_evalEnv (polarityEnv env) (sigmaEnv env) (stateSigmaEnv env) (q :: q' :: stateEnv env).

  (*the environment env should contain q, q'; m, m' at the head *)
  Definition makeSomeRight (X Y Z W M : Type) (q q' : W) (m m' : Z) (r : evalEnv X Y Z W -> fGamma -> option M) (env : evalEnv X Y Z W) :=
    let env := transEnvAddSM q q' m m' env in
    map (reifyWindow r env)
      [{inr $ inr (polVar 0, stateSigmaVar 2), inl (0, stateSigmaVar 0), inr $ inr (polVar 0, stateSigmaVar 3)} / {inr $ inr (polConst positive, stateSigmaVar 4), inl (1, stateSigmaVar 2), inr $ inr (polConst positive, stateSigmaVar 1)};
          {inr $ inr (polVar 0, stateSigmaVar 2), inr $ inr (polVar 0, stateSigmaVar 3), inl (0, stateSigmaVar 0)} / {inr $ inr (polConst positive, stateSigmaVar 4), inr $ inr (polConst positive, stateSigmaVar 2), inl (1, stateSigmaVar 3)};
        {inl (0, stateSigmaVar 0), inr $ inr (polVar 0, stateSigmaVar 2), inr $ inr (polVar 0, stateSigmaVar 3)} / {inl (1, stateSigmaVar 4), inr $ inr (polConst positive, stateSigmaVar 1), inr $ inr (polConst positive, stateSigmaVar 2)}].
  
  Definition makeSomeLeft (X Y Z W M : Type) (q q' : W) (m m' : Z) (r : evalEnv X Y Z W -> fGamma -> option M) (env : evalEnv X Y Z W) :=
    let env := transEnvAddSM q q' m m' env in  
                                  map (reifyWindow r env)
                                    [{inr $ inr (polVar 0, stateSigmaVar 2), inl (0, stateSigmaVar 0), inr $ inr (polVar 0, stateSigmaVar 3)} / {inr $ inr (polConst negative, stateSigmaVar 1), inl (1, stateSigmaVar 3), inr $ inr (polConst negative, stateSigmaVar 4)}; 
                                     {inl (0, stateSigmaVar 0), inr $ inr (polVar 0, stateSigmaVar 2), inr $ inr (polVar 0, stateSigmaVar 3)} / {inl (1, stateSigmaVar 2), inr $ inr (polConst negative, stateSigmaVar 3), inr $ inr (polConst negative, stateSigmaVar 4)};
                                     {inr $ inr (polVar 0, stateSigmaVar 2), inr $ inr (polVar 0, stateSigmaVar 3), inl (0, stateSigmaVar 0)} / {inr $ inr (polConst negative, stateSigmaVar 3), inr $ inr (polConst negative, stateSigmaVar 1), inl (1, stateSigmaVar 4)}]. 

  Definition makeSomeStay (X Y Z W M: Type) (q q' : W) (m m' : Z) (r : evalEnv X Y Z W -> fGamma -> option M) (env : evalEnv X Y Z W) :=
    let env := transEnvAddSM q q' m m' env in
                                  map (reifyWindow r env)
                                    [{inr $ inr (polVar 0, stateSigmaVar 2), inl (0, stateSigmaVar 0), inr $ inr (polVar 0, stateSigmaVar 3)} / {inr $ inr (polConst neutral, stateSigmaVar 2), inl (1, stateSigmaVar 1), inr $ inr (polConst neutral, stateSigmaVar 3)};
                                     {inl (0, stateSigmaVar 0), inr $ inr (polVar 0, stateSigmaVar 2), inr $ inr (polVar 0, stateSigmaVar 3)} / {inl (1, stateSigmaVar 1), inr $ inr (polConst neutral, stateSigmaVar 2), inr $ inr (polConst neutral, stateSigmaVar 3)};
                                     {inr $ inr (polVar 0, stateSigmaVar 2), inr $ inr (polVar 0, stateSigmaVar 3), inl (0, stateSigmaVar 0)} / {inr $ inr (polConst neutral, stateSigmaVar 2), inr $ inr (polConst neutral, stateSigmaVar 3), inl (1, stateSigmaVar 1)}].

  (*the none rules are a bit more complicated again *)

  Definition makeNoneRight (X Y Z W M : Type) (q q' : W) (r : evalEnv X Y Z W -> fGamma -> option M) (env : evalEnv X Y Z W) :=
    let env := transEnvAddS q q' env in
    map (reifyWindow r env)
        [
          {inr $ inr (polVar 0, blank), inl (0, blank), inr $ inr (polVar 0, stateSigmaVar 0)} / {inr $ inr (polConst neutral, blank), inl (1, blank), inr $ inr (polConst neutral, stateSigmaVar 0)};
            {inr $ inr (polVar 0, someSigmaVar 0), inl (0, blank), inr $ inr (polVar 0, blank)} / {inr $ inr (polConst positive, stateSigmaVar 0), inl (1, someSigmaVar 0), inr $ inr (polConst positive, blank)};
            {inr $ inr (polVar 0, blank), inr $ inr (polVar 0, blank), inl (0, blank)} / {inr $ inr (polVar 1, blank), inr $ inr (polVar 1, blank), inl (1, blank)};
            {inr $ inr (polVar 0, blank), inr $ inr (polVar 0, someSigmaVar 0), inl (0, blank)} / {inr $ inr (polVar 1, blank), inr $ inr (polVar 1, blank), inl (1, someSigmaVar 0)};
            {inr $ inr (polVar 0, someSigmaVar 0), inr $ inr (polVar 0, someSigmaVar 1), inl (0, blank)} / {inr $ inr (polConst positive, stateSigmaVar 0), inr $ inr (polConst positive, someSigmaVar 0), inl (1, someSigmaVar 1)};
            {inl (0, blank), inr $ inr (polVar 0, blank), inr $ inr (polVar 0, blank)} / {inl (1, stateSigmaVar 0), inr $ inr (polVar 1, blank), inr $ inr (polVar 1, blank)};
            {inl (0, blank), inr $ inr (polVar 0, someSigmaVar 0), inr $ inr (polVar 0, stateSigmaVar 0)} / {inl (1, blank), inr $ inr (polVar 1, someSigmaVar 0), inr $ inr (polVar 1, stateSigmaVar 0)}
        ].

  Definition makeNoneLeft (X Y Z W M : Type) (q q' : W) (r : evalEnv X Y Z W -> fGamma -> option M) (env : evalEnv X Y Z W) :=
    let env := transEnvAddS q q' env in
    map (reifyWindow r env)
        [
          {inr $ inr (polVar 0, stateSigmaVar 0), inl (0, blank), inr $ inr (polVar 0, blank)} / {inr $ inr (polConst neutral, stateSigmaVar 0), inl (1, blank), inr $ inr (polConst neutral, blank)};
            {inr $ inr (polVar 0, blank), inl (0, blank), inr $ inr (polVar 0, someSigmaVar 0)} / {inr $ inr (polConst negative, blank), inl (1, someSigmaVar 0), inr $ inr (polConst negative, stateSigmaVar 0)};
            {inl (0, blank), inr $ inr (polVar 0, blank), inr $ inr (polVar 0, blank)} / {inl (1, blank), inr $ inr (polVar 1, blank), inr $ inr (polVar 1, blank)};
            {inl (0, blank), inr $ inr (polVar 0, someSigmaVar 0), inr $ inr (polVar 0, blank)} / {inl (1, someSigmaVar 0), inr $ inr (polVar 1, blank), inr $ inr (polVar 1, blank)};
            {inl (0, blank), inr $ inr (polVar 0, someSigmaVar 0), inr $ inr (polVar 0, someSigmaVar 1)} / {inl (1, someSigmaVar 0), inr $ inr (polConst negative, someSigmaVar 1), inr $ inr (polConst negative, stateSigmaVar 0)};
            {inr $ inr (polVar 0, blank), inr $ inr (polVar 0, blank), inl (0, blank)} / {inr $ inr (polVar 1, blank), inr $ inr (polVar 1, blank), inl (1, stateSigmaVar 0)};
            {inr $ inr (polVar 0, stateSigmaVar 0), inr $ inr (polVar 0, someSigmaVar 0), inl (0, blank)} / {inr $ inr (polConst neutral, stateSigmaVar 0), inr $ inr (polConst neutral, someSigmaVar 0), inl (1, blank)}
        ].

  Definition makeNoneStay (X Y Z W M : Type) (q q' : W) (r : evalEnv X Y Z W -> fGamma -> option M) (env : evalEnv X Y Z W) :=
    let env := transEnvAddS q q' env in
    map (reifyWindow r env)
        [
          {inr $ inr (polVar 0, stateSigmaVar 0), inl (0, blank), inr $ inr (polVar 0, blank)} / {inr $ inr (polConst neutral, stateSigmaVar 0), inl (1, blank), inr $ inr (polConst neutral, blank)};
            {inr $ inr (polVar 0, blank), inl (0, blank), inr $ inr (polVar 0, stateSigmaVar 0)} / {inr $ inr (polConst neutral, blank), inl (1, blank), inr $ inr (polConst neutral, stateSigmaVar 0)};
            {inl (0, blank), inr $ inr (polVar 0, someSigmaVar 0), inr $ inr (polVar 0, stateSigmaVar 0)} / {inl (1, blank), inr $ inr (polConst neutral, someSigmaVar 0), inr $ inr (polConst neutral, stateSigmaVar 0)};
            {inl (0, blank), inr $ inr (polVar 0, blank), inr $ inr (polVar 0, blank)} / {inl (1, blank), inr $ inr (polConst neutral, blank), inr $ inr (polConst neutral, blank)};
            {inr $ inr (polVar 0, stateSigmaVar 0), inr $ inr (polVar 0, someSigmaVar 0), inl (0, blank)} / {inr $ inr (polConst neutral, stateSigmaVar 0), inr $ inr (polConst neutral, someSigmaVar 0), inl (1, blank)};
            {inr $ inr (polVar 0, blank), inr $ inr (polVar 0, blank), inl (0, blank)} / {inr $ inr (polConst neutral, blank), inr $ inr (polConst neutral, blank), inl (1, blank)}
        ].

  Definition makeHalt (X Y Z W M : Type) (q : W) (r : evalEnv X Y Z W -> fGamma -> option M) (env : evalEnv X Y Z W) :=
    let env := transEnvAddS q q env in
    map (reifyWindow r env)
        [
          {inr $ inr (polVar 0, stateSigmaVar 0), inl (0, stateSigmaVar 1), inr $ inr (polVar 0, stateSigmaVar 2)} / {inr $ inr (polConst neutral, stateSigmaVar 0), inl (1, stateSigmaVar 1), inr $ inr (polConst neutral, stateSigmaVar 2)};
            {inr $ inr (polVar 0, stateSigmaVar 0), inr $ inr (polVar 0, stateSigmaVar 1), inl (0, stateSigmaVar 2)} / {inr $ inr (polConst neutral, stateSigmaVar 0), inr $ inr (polConst neutral, stateSigmaVar 1), inl (1, stateSigmaVar 2)};
            {inl (0, stateSigmaVar 0), inr $ inr (polVar 0, stateSigmaVar 1), inr $ inr (polVar 0, stateSigmaVar 2)} / {inl (1, stateSigmaVar 0), inr $ inr (polConst neutral, stateSigmaVar 1), inr $ inr (polConst neutral, stateSigmaVar 2)}
        ].

  (*the environments which assign values to the non-constant variables of the transition rules *)
  Definition baseEnv := makeAllEvalEnv (elem Fpolarity) (elem Sigma) (elem FstateSigma) (elem states) 1 0 3 0. 
  Definition baseEnvNone := makeAllEvalEnv (elem Fpolarity) (elem Sigma) (elem FstateSigma) (elem states) 2 2 2 0. 
  Definition baseEnvHalt := makeAllEvalEnv (elem Fpolarity) (elem Sigma) (elem FstateSigma) (elem states) 1 0 3 0. 

  (*given a state and a current symbol, generate the rules for the corresponding transition *)
  Definition generateRulesForFinNonHalt (q : states) (m : stateSigma) :=
    filterSome (match m, (trans (q, m)) with
    | _, (q', (Some σ, L)) => concat (map (makeSomeRight q q' m (Some σ) reifyGammaFin) baseEnv)
    | _, (q', (Some σ, R)) => concat (map ( makeSomeLeft q q' m (Some σ) reifyGammaFin) baseEnv)
    | _, (q', (Some σ, N)) => concat (map ( makeSomeStay q q' m (Some σ) reifyGammaFin) baseEnv)
    | Some σ, (q', (None, L)) => concat (map (makeSomeRight q q' (Some σ) (Some σ) reifyGammaFin) baseEnv)
    | Some σ, (q', (None, R)) => concat (map (makeSomeLeft q q' (Some σ) (Some σ) reifyGammaFin) baseEnv)
    | Some σ, (q', (None, N)) => concat (map (makeSomeStay q q' (Some σ) (Some σ) reifyGammaFin) baseEnv)
    | None, (q', (None, L)) => concat (map (makeNoneRight q q' reifyGammaFin) baseEnvNone)
    | None, (q', (None, R)) => concat (map (makeNoneLeft q q' reifyGammaFin) baseEnvNone)
    | None, (q', (None, N)) => concat (map (makeNoneStay q q' reifyGammaFin) baseEnvNone)
    end).

  (*given a state, generate the rules needed for halting states *)
  Definition generateRulesForFinHalt (q : states) :=
    filterSome (concat (map (fun env =>  makeHalt q reifyGammaFin env) baseEnvHalt)).
  (*given a state, generate either transition rules or halting rules for it *)
  Definition generateRulesForFin (q : states) :=
    if halt q then generateRulesForFinHalt q else
      concat (map (fun m => generateRulesForFinNonHalt q m) (elem FstateSigma)). 
  (*generate rules for all states*)
  Definition finStateRules := concat (map generateRulesForFin (elem states)).  

  (** *proof of transition agreement *)
  (*We first define the inductive rules structured in a different way, in order for it to resemble the structure of the list-based rules *)
  (*(writing the list-based rules in a way which resembles the inductive predicates is not possible in an elegant way) *)

  (* bundling predicates *)
  (*we first group together according to the shift direction: left/right/stay *)

  Inductive etransSomeLeft : states -> states -> stateSigma -> stateSigma -> transRule :=
  | etransSomeLeftLeftC q q' (a b : stateSigma)  γ1 γ2 γ3 γ4 γ5 γ6: transSomeLeftLeft q q' a γ1 γ2 γ3 γ4 γ5 γ6 -> etransSomeLeft q q' a b γ1 γ2 γ3 γ4 γ5 γ6
  | etransSomeLeftRightC q q' (a b : stateSigma)  γ1 γ2 γ3 γ4 γ5 γ6 : transSomeLeftRight q q' a b γ1 γ2 γ3 γ4 γ5 γ6 -> etransSomeLeft q q' a b γ1 γ2 γ3 γ4 γ5 γ6
  | etransSomeLeftCenterC q q' (a b : stateSigma)  γ1 γ2 γ3 γ4 γ5 γ6 : transSomeLeftCenter q q' a b γ1 γ2 γ3 γ4 γ5 γ6 -> etransSomeLeft q q' a b γ1 γ2 γ3 γ4 γ5 γ6. 

  Hint Constructors etransSomeLeft : trans. 

  Inductive etransSomeRight : states -> states -> stateSigma -> stateSigma -> transRule :=
  | etransSomeRightLeftC q q' (a b: stateSigma)  γ1 γ2 γ3 γ4 γ5 γ6: transSomeRightLeft q q' a b γ1 γ2 γ3 γ4 γ5 γ6 -> etransSomeRight q q' a b γ1 γ2 γ3 γ4 γ5 γ6
  | etransSomeRightRightC q q' (a b : stateSigma)  γ1 γ2 γ3 γ4 γ5 γ6 : transSomeRightRight q q' a γ1 γ2 γ3 γ4 γ5 γ6 -> etransSomeRight q q' a b γ1 γ2 γ3 γ4 γ5 γ6
  | etransSomeRightCenterC q q' (a b : stateSigma)  γ1 γ2 γ3 γ4 γ5 γ6 : transSomeRightCenter q q' a b γ1 γ2 γ3 γ4 γ5 γ6 -> etransSomeRight q q' a b γ1 γ2 γ3 γ4 γ5 γ6. 

  Hint Constructors etransSomeRight : trans. 

  Inductive etransSomeStay : states -> states -> stateSigma -> stateSigma -> transRule :=
  | etransSomeStayLeftC q q' (a b: stateSigma) γ1 γ2 γ3 γ4 γ5 γ6: transSomeStayLeft q q' a b γ1 γ2 γ3 γ4 γ5 γ6 -> etransSomeStay q q' a b γ1 γ2 γ3 γ4 γ5 γ6
  | etransSomeStayRightC q q' (a b: stateSigma) γ1 γ2 γ3 γ4 γ5 γ6 : transSomeStayRight q q' a b γ1 γ2 γ3 γ4 γ5 γ6 -> etransSomeStay q q' a b γ1 γ2 γ3 γ4 γ5 γ6
  | etransSomeStayCenterC q q' (a b: stateSigma) γ1 γ2 γ3 γ4 γ5 γ6 : transSomeStayCenter q q' a b γ1 γ2 γ3 γ4 γ5 γ6 -> etransSomeStay q q' a b γ1 γ2 γ3 γ4 γ5 γ6. 

  Hint Constructors etransSomeStay : trans.

  Inductive etransNoneLeft : states -> states -> transRule :=
  | etransNoneLeftLeftC q q' γ1 γ2 γ3 γ4 γ5 γ6: transNoneLeftLeft q q' γ1 γ2 γ3 γ4 γ5 γ6 -> etransNoneLeft q q' γ1 γ2 γ3 γ4 γ5 γ6
  | etransNoneLeftRightC q q' γ1 γ2 γ3 γ4 γ5 γ6 : transNoneLeftRight q q' γ1 γ2 γ3 γ4 γ5 γ6 -> etransNoneLeft q q' γ1 γ2 γ3 γ4 γ5 γ6
  | etransNoneLeftCenterC q q' γ1 γ2 γ3 γ4 γ5 γ6 : transNoneLeftCenter q q' γ1 γ2 γ3 γ4 γ5 γ6 -> etransNoneLeft q q' γ1 γ2 γ3 γ4 γ5 γ6. 

  Hint Constructors etransNoneLeft : trans. 

  Inductive etransNoneRight : states -> states -> transRule :=
  | etransNoneRightLeftC q q' γ1 γ2 γ3 γ4 γ5 γ6: transNoneRightLeft q q' γ1 γ2 γ3 γ4 γ5 γ6 -> etransNoneRight q q' γ1 γ2 γ3 γ4 γ5 γ6
  | etransNoneRightRightC q q' γ1 γ2 γ3 γ4 γ5 γ6 : transNoneRightRight q q' γ1 γ2 γ3 γ4 γ5 γ6 -> etransNoneRight q q' γ1 γ2 γ3 γ4 γ5 γ6
  | etransNoneRightCenterC q q' γ1 γ2 γ3 γ4 γ5 γ6 : transNoneRightCenter q q' γ1 γ2 γ3 γ4 γ5 γ6 -> etransNoneRight q q' γ1 γ2 γ3 γ4 γ5 γ6. 

  Hint Constructors etransNoneRight : trans. 

  Inductive etransNoneStay : states -> states -> transRule :=
  | etransNoneStayLeftC q q'  γ1 γ2 γ3 γ4 γ5 γ6: transNoneStayLeft q q' γ1 γ2 γ3 γ4 γ5 γ6 -> etransNoneStay q q' γ1 γ2 γ3 γ4 γ5 γ6
  | etransNoneStayRightC q q' γ1 γ2 γ3 γ4 γ5 γ6 : transNoneStayRight q q' γ1 γ2 γ3 γ4 γ5 γ6 -> etransNoneStay q q' γ1 γ2 γ3 γ4 γ5 γ6
  | etransNoneStayCenterC q q' γ1 γ2 γ3 γ4 γ5 γ6 : transNoneStayCenter q q' γ1 γ2 γ3 γ4 γ5 γ6 -> etransNoneStay q q' γ1 γ2 γ3 γ4 γ5 γ6.

  Hint Constructors etransNoneStay : trans. 

  Inductive etransRules : states -> stateSigma -> transRule :=
  | etransXSomeStay q m σ q' γ1 γ2 γ3 γ4 γ5 γ6: trans (q, m) = (q', (Some σ, N)) -> etransSomeStay q q' m (Some σ) γ1 γ2 γ3 γ4 γ5 γ6 -> etransRules q m γ1 γ2 γ3 γ4 γ5 γ6
  | etransXSomeLeft q m σ q' γ1 γ2 γ3 γ4 γ5 γ6: trans (q, m) = (q', (Some σ, R)) -> etransSomeLeft q q' m (Some σ) γ1 γ2 γ3 γ4 γ5 γ6 -> etransRules q m γ1 γ2 γ3 γ4 γ5 γ6
  | etransXSomeRight q m σ q' γ1 γ2 γ3 γ4 γ5 γ6: trans (q, m) = (q', (Some σ, L)) -> etransSomeRight q q' m (Some σ) γ1 γ2 γ3 γ4 γ5 γ6 -> etransRules q m γ1 γ2 γ3 γ4 γ5 γ6
  | etransSomeNoneStay q σ q' γ1 γ2 γ3 γ4 γ5 γ6: trans (q, Some σ) = (q', (None, N)) -> etransSomeStay q q' (Some σ) (Some σ) γ1 γ2 γ3 γ4 γ5 γ6 -> etransRules q (Some σ) γ1 γ2 γ3 γ4 γ5 γ6
  | etransSomeNoneLeft q σ q' γ1 γ2 γ3 γ4 γ5 γ6: trans (q, Some σ) = (q', (None, R)) -> etransSomeLeft q q' (Some σ) (Some σ) γ1 γ2 γ3 γ4 γ5 γ6 -> etransRules q (Some σ) γ1 γ2 γ3 γ4 γ5 γ6
  | etransSomeNoneRight q σ q' γ1 γ2 γ3 γ4 γ5 γ6: trans (q, Some σ) = (q', (None, L)) -> etransSomeRight q q' (Some σ) (Some σ) γ1 γ2 γ3 γ4 γ5 γ6 -> etransRules q (Some σ) γ1 γ2 γ3 γ4 γ5 γ6
  | etransNoneNoneStay q q' γ1 γ2 γ3 γ4 γ5 γ6: trans (q, None) = (q', (None, N)) -> etransNoneStay q q' γ1 γ2 γ3 γ4 γ5 γ6 -> etransRules q None γ1 γ2 γ3 γ4 γ5 γ6
  | etransNoneNoneLeft q q' γ1 γ2 γ3 γ4 γ5 γ6: trans (q, None) = (q', (None, R)) -> etransNoneLeft q q' γ1 γ2 γ3 γ4 γ5 γ6 -> etransRules q None γ1 γ2 γ3 γ4 γ5 γ6
  | etransNoneNoneRight q q' γ1 γ2 γ3 γ4 γ5 γ6: trans (q, None) = (q', (None, L)) -> etransNoneRight q q' γ1 γ2 γ3 γ4 γ5 γ6 -> etransRules q None γ1 γ2 γ3 γ4 γ5 γ6.

  Hint Constructors etransRules : trans.

  Inductive ehaltRules : states -> transRule :=
  | ehaltCenter q (m1 m2 : stateSigma) m p : ehaltRules q (inr (inr (p, m1))) (inl (q, m)) (inr (inr (p, m2))) (inr (inr (neutral, m1))) (inl (q, m)) (inr (inr (neutral, m2)))
  | ehaltRight q (m1 m2 m : stateSigma) p : ehaltRules q (inr (inr (p, m1))) (inr (inr (p, m2))) (inl (q, m)) (inr (inr (neutral, m1))) (inr (inr (neutral, m2))) (inl (q, m)) 
  | ehaltLeft q (m1 m2 m : stateSigma) p : ehaltRules q (inl (q, m)) (inr (inr (p, m1))) (inr (inr (p, m2))) (inl (q, m)) (inr (inr (neutral, m1))) (inr (inr (neutral, m2))).
  Hint Constructors ehaltRules : trans. 

  Inductive estateRules : transRule :=
  | etransNonHaltC q m γ1 γ2 γ3 γ4 γ5 γ6 : halt q = false -> etransRules q m γ1 γ2 γ3 γ4 γ5 γ6 -> estateRules γ1 γ2 γ3 γ4 γ5 γ6
  | etransHaltC q γ1 γ2 γ3 γ4 γ5 γ6 : halt q = true -> ehaltRules q γ1 γ2 γ3 γ4 γ5 γ6 -> estateRules γ1 γ2 γ3 γ4 γ5 γ6. 

  Hint Constructors estateRules : trans. 

  Definition esimRules γ1 γ2 γ3 γ4 γ5 γ6 := estateRules γ1 γ2 γ3 γ4 γ5 γ6 \/ tapeRules γ1 γ2 γ3 γ4 γ5 γ6. 
  Hint Unfold esimRules : trans. 

  Notation erewHeadSim := (rewritesHeadInd esimRules).   

  Ltac erewHeadSim_inv := 
    repeat match goal with
             | [H : esimRules _ _ _ _ _ _ |- _] => inv H
             | [H : erewHeadSim _ _ |- _ ] => inv H
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

  Lemma etrans_trans_agreement s1 s2 : erewHeadSim s1 s2 <-> rewHeadSim s1 s2. 
  Proof. 
  (*   split. *)
  (*   - intros. inv H.  *)
  (*     erewHeadSim_inv; try destruct m; eauto 7 with trans. *)
  (*   - intros. inv H. destruct H0 as [H0 | [H0 | H0]].  *)
  (*     + transRules_inv2; eauto 7 with trans.  *)
  (*     + haltRules_inv1; eauto 7 with trans. *)
  (*     + eauto with trans.  *)
  (* Qed.   *)
    Admitted. 

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

  Lemma in_concat_map_iff (X Y : Type) (f : X -> list Y) (l : list X) y : y el concat (map f l) <-> exists x, x el l /\ y el f x. 
  Proof. 
    split; intros. 
    - apply in_concat_iff in H as (? & H1 & (? & <- & H3)%in_map_iff). eauto. 
    - apply in_concat_iff. destruct H as (x & H1 & H2). exists (f x). eauto. 
  Qed. 

  Ltac solve_agreement_trans :=
    split;
    [ apply in_makeAllEvalEnv_iff; repeat split; cbn; solve_agreement_incl
      |
      unfold makeSomeStay, makeSomeLeft, makeSomeRight, makeNoneStay, makeNoneLeft, makeNoneRight;
        apply in_map_iff;
      match goal with
      | [ |- ex (fun x => _ /\ x el ?h)] => rec_exists h ltac:(cbn; split; [reflexivity | now eauto])
      end
    ].

  Lemma agreement_nonhalt q m γ1 γ2 γ3 γ4 γ5 γ6: {γ1, γ2, γ3} / {γ4, γ5, γ6} el generateRulesForFinNonHalt q m <-> etransRules q m γ1 γ2 γ3 γ4 γ5 γ6. 
  Proof. 
    split; intros. 
    - apply in_filterSome_iff in H. destruct m; destruct trans eqn:H0; destruct p, o;
      destruct m;
      apply in_concat_iff in H as (l' & H1 & H);
      apply in_map_iff in H as ([] & <- & H2); 
      unfold makeNoneRight, makeNoneLeft, makeNoneStay, makeSomeRight, makeSomeLeft, makeSomeStay in H1;
      apply in_map_iff in H1 as (? & H4 & H1);
      cbn in H1;
      apply in_makeAllEvalEnv_iff in H2 as ((F1 & _) & (F2 & _) & (F3 & _) & (F4 & _));
      destruct_or H1; try rewrite <- H1 in *;
      try match goal with [H : False |- _] => destruct H end;
      list_destruct_length; cbn in H4;
      match goal with
      | [H : None = Some _ |- _] => congruence
      | [H : optReturn _ = Some _ |- _] => inv H
      end; eauto 7 with trans.
    - erewHeadSim_inv; unfold generateRulesForFinNonHalt.
      1-18: try destruct m.
      all: rewrite H0;
      apply in_filterSome_iff; apply in_concat_map_iff. 
      (*some things are easy to automate, some aren't... *)
      * exists (Build_evalEnv [p] [] [m1; m2] []). solve_agreement_trans.
      * exists (Build_evalEnv [p] [] [m1; m2] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2; m3] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2; m3] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2; m3] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2; m3] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2; m3] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2; m3] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2; m3] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2; m3] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2; m3] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2; m3] []). solve_agreement_trans.
      * exists (Build_evalEnv [p] [] [m1; m2; m3] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2; m3] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2] []). solve_agreement_trans.
      * exists (Build_evalEnv [p] [] [m1; m2; m3] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2; m3] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2; m3] []). solve_agreement_trans.
      * exists (Build_evalEnv [p] [] [m1; m2; m3] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2; m3] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2; m3] []). solve_agreement_trans.
      * exists (Build_evalEnv [p] [σ] [m] []). solve_agreement_trans.
      * exists (Build_evalEnv [p] [] [] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [σ] [m] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p; p'] [] [] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p; p'] [σ] [] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [σ1; σ2] [m] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p; p'] [] [m] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [σ] [m1] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [σ] [m] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p; p'] [] [m] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p; p'] [σ] [m] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p; p'] [] [] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p; p'] [σ] [] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [σ1; σ2] [m1] []). solve_agreement_trans.
      * exists (Build_evalEnv [p] [] [m] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [σ] [m] []). solve_agreement_trans. 
   Qed.  
          
  Lemma agreement_halt q γ1 γ2 γ3 γ4 γ5 γ6: {γ1, γ2, γ3} / {γ4, γ5, γ6} el generateRulesForFinHalt q <-> ehaltRules q γ1 γ2 γ3 γ4 γ5 γ6.
  Proof.
     split; intros. 
     - apply in_filterSome_iff in H. 
      apply in_concat_iff in H as (l' & H1 & H);
      apply in_map_iff in H as ([] & <- & H2). 
      unfold makeHalt in H1. 
      apply in_map_iff in H1 as (? & H4 & H1);
      cbn in H1.
      apply in_makeAllEvalEnv_iff in H2 as ((F1 & _) & (F2 & _) & (F3 & _) & (F4 & _)).
      destruct_or H1; try rewrite <- H1 in *;
      try match goal with [H : False |- _] => destruct H end;
      list_destruct_length; cbn in H4;
      match goal with
      | [H : None = Some _ |- _] => congruence
      | [H : optReturn _ = Some _ |- _] => inv H
      end; eauto with trans.
    - erewHeadSim_inv; 
      unfold generateRulesForFinHalt; apply in_filterSome_iff; apply in_concat_map_iff. 
      + exists (Build_evalEnv [p] [] [m1; m; m2] []). solve_agreement_trans. 
      + exists (Build_evalEnv [p] [] [m1; m2; m] []). solve_agreement_trans. 
      + exists (Build_evalEnv [p] [] [m; m1; m2] []). solve_agreement_trans. 
  Qed. 

  Lemma agreement_transition γ1 γ2 γ3 γ4 γ5 γ6 :
    {γ1, γ2, γ3} / {γ4, γ5, γ6} el finStateRules <-> estateRules γ1 γ2 γ3 γ4 γ5 γ6. 
  Proof. 
    split. 
    - intros. unfold finStateRules in H.
      apply in_concat_map_iff in H as (q & _ & H). 
      unfold generateRulesForFin in H.
      destruct halt eqn:H1. 
      + econstructor 2; [apply H1 | ]. apply agreement_halt, H. 
      + apply in_concat_map_iff in H as (m & _ & H).
        econstructor 1; [apply H1 | ].
        apply agreement_nonhalt, H.
    - intros. unfold finStateRules. apply in_concat_map_iff.
      inv H.
      + apply agreement_nonhalt in H1.
        exists q; split; [apply elem_spec | ].
        unfold generateRulesForFin. rewrite H0. 
        apply in_concat_map_iff.
        exists m; split; [apply elem_spec | apply H1]. 
      + exists q; split; [apply elem_spec | ]. 
        unfold generateRulesForFin. rewrite H0. 
        apply agreement_halt, H1. 
  Qed. 

  Definition allFinSimRules := finTapeRules ++ finStateRules.

  Lemma rewHead_agreement_all' a b: rewritesHeadList allFinSimRules a b <-> erewHeadSim a b.
  Proof. 
    split; intros.
    - inv H. destruct H0 as (H1 & H2). 
      unfold allFinSimRules in H1. apply in_app_iff in H1.
      destruct H1 as [H1 | H1]. 
      + destruct x, prem, conc.
        destruct H2 as ((? & -> ) & (? & ->)). cbn. 
        constructor. constructor 2.
        apply agreement_tape, H1. 
      + destruct x, prem, conc.  
        destruct H2 as ((? & ->) & (? & ->)).
        constructor. econstructor 1. apply agreement_transition, H1. 
    - inv H. inv H0. 
      + apply agreement_transition in H as H1.
        exists ({x1, x2, x3} / {x4, x5, x6}). unfold allFinSimRules.
        split; [apply in_app_iff; right; apply H1 | ].
        split; unfold prefix; cbn; eauto. 
      + apply agreement_tape in H as H1.
        exists ({x1, x2, x3} / {x4, x5, x6}). unfold allFinSimRules. 
        split; [apply in_app_iff; left; apply H1 | ].
        split; unfold prefix; cbn; eauto.
   Qed. 

  Lemma rewHead_agreement_all a b : rewritesHeadList allFinSimRules a b <-> rewHeadSim a b. 
  Proof.
    split; intros. 
    - now apply etrans_trans_agreement, rewHead_agreement_all'. 
    - now apply rewHead_agreement_all', etrans_trans_agreement. 
  Qed. 

  (*strings representing configs *)
  Definition stringForTapeHalf (s : list Sigma) := mapPolarity neutral s ++ E neutral (z - |s|).  
  Definition stringForConfig (q : states) (s : tape Sigma) :=
    match s with
    | niltape _ => rev (stringForTapeHalf []) ++ [inl (q, None)] ++ stringForTapeHalf [] 
    | leftof h s => rev (stringForTapeHalf []) ++ [inl (q, None)] ++ stringForTapeHalf (h :: s)
    | rightof h s => rev (stringForTapeHalf (h :: s)) ++ [inl (q, None)] ++ stringForTapeHalf []   
    | midtape l c r => rev (stringForTapeHalf l) ++ [inl (q, Some c)] ++ stringForTapeHalf r
    end. 

  Lemma stringForTapeHalf_reprTape s : |s| <= z' -> s ≃t(neutral) stringForTapeHalf s.
  Proof. 
    intros.  repeat split. 
    - destruct s. 
      + cbn. rewrite E_length. lia. 
      + unfold stringForTapeHalf, mapPolarity. rewrite app_length, map_length, E_length. 
        cbn [length] in *. unfold z, wo, z' in *. lia. 
    - lia. 
  Qed. 

  Lemma stringForConfig_reprConfig q s : sizeOfTape s <= z' -> (q, s) ≃c stringForConfig q s. 
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


  (*initial strings *)
  Definition isValidInput (s : list Sigma) := |s| <= k. 

  Definition initialTapeForString (s : list Sigma) :=
    match s with
      | [] => niltape Sigma
      | x::s => leftof x s
    end. 

  Definition initialString (s : list Sigma) := stringForConfig start (initialTapeForString s). 

  Definition isValidInitialString (s : list Gamma) :=
    exists s', s = initialString s' /\ isValidInput s'. 

  Lemma initialString_reprConfig s : isValidInput s -> (start, initialTapeForString s) ≃c initialString s. 
  Proof. 
    intros. unfold initialString. apply stringForConfig_reprConfig.
    unfold isValidInput in H. destruct s; cbn in *; unfold z'; lia.  
  Qed. 

  Definition haltingStates := filter (fun x => halt x) (elem states). 
  Definition finalSubstrings : list (list Gamma) := map (fun e => [inl e]) (prodLists haltingStates (elem FstateSigma)). 

  Lemma In_explicit (X : Type) (x : X) (l : list X) :
    x el l <-> exists s1 s2, l = s1 ++ [x] ++ s2. 
  Proof. 
    induction l; cbn. 
    - split; [tauto | intros (s1 & s2 & H)].
      destruct s1; cbn in H; congruence. 
    - split. 
      + intros [-> | (s1 & s2 & ->)%IHl]. 
        * exists [], l0. eauto. 
        * exists (a :: s1), s2; eauto. 
      + intros ([] & s2 & H). 
        * inv H. eauto. 
        * inv H. right; apply IHl.
          exists l1, s2. eauto. 
  Qed. 

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

  Lemma relpower_extensional (X : Type) (R R': X -> X -> Prop) :
    (forall x y, R x y <-> R' x y) -> forall n x y, relpower R n x y <-> relpower R' n x y. 
  Proof. 
    intros H. induction n. 
    - split; intros H0; inv H0; eauto. 
    - split; intros H0; inv H0.
      + apply H in H2. apply IHn in H3. eauto. 
      + apply H in H2. apply IHn in H3. eauto. 
  Qed. 

  Lemma relpower_loop_agree l q tape q' tape':
    relpower sstepRel l (q, tape) (q', tape')
    -> halt (configState (q', tape')) = true
    -> loop (step (M := TM)) (haltConf (M := TM)) (mk_mconfig q [|tape|]) l = Some (mk_mconfig q' [|tape'|]).
  Proof. 
     revert q tape q' tape'. 
     induction l; cbn; intros. 
     - inv H. unfold haltConf. cbn. rewrite H0. reflexivity. 
     - inv H. destruct b as (q'' & tape''). eapply IHl in H3.
       2: cbn; apply H0.  
       destruct H2 as (F1 & F2). unfold haltConf. cbn in *. rewrite F1. 
       setoid_rewrite <- (@sstep_agree2 (TM.states TM) Sigma (@TM.trans Sigma 1 TM) (TM.start TM) (@TM.halt Sigma 1 TM) (mk_mconfig q [|tape|])). 
       cbn. destruct TM.trans. inv F2. cbn. apply H3. 
  Qed. 

  Lemma loop_relpower_agree q tape q' tape' n: 
    loopM (mk_mconfig q [|tape|]) n = Some (mk_mconfig q' [|tape'|]) 
     -> (q, tape) ▷(≤ n) (q', tape').
  Proof. 
    revert q tape q' tape'.  
     induction n; intros; cbn in *; unfold haltConf in H; cbn in H; destruct halt eqn:H1; [ | congruence | | ].
    - inv H. exists 0. eauto.  
    - inv H. exists 0. repeat split; [lia | eauto | eauto]. 
    - specialize (@sstep_agree1 states Sigma (@TM.trans Sigma 1 TM) start halt (q, tape)) as H2. 
      cbn [mconfig_for_sconfig] in H2. 
      destruct (step (mk_mconfig q [|tape|])) as (q''  &tape'') eqn:H3. 
      setoid_rewrite H3 in H2. 
      revert H H3 H2. 
      apply VectorDef.caseS' with (v := tape''). clear tape''.
      intros tape'' t0. 
      apply VectorDef.case0 with (v := t0).  
      intros H H3 H2. 
      apply IHn in H as (l & F1 & F2 & F3).  
      exists (S l). repeat split .
      + lia. 
      + econstructor. 2: apply F2. unfold sstepRel. rewrite <- H2. cbn. eauto. 
      + apply F3. 
  Qed. 
  
  Lemma loopM_halt sig l (M : mTM sig l) (c : TM.mconfig sig (TM.states M) l) n (q' : TM.states M) tape' : loopM c n = Some (mk_mconfig q' tape') -> TM.halt q' = true.
  Proof. 
    intros. revert c q' tape' H. induction n; intros; cbn in H. 
    + unfold haltConf in H. destruct c. cbn in H. destruct (TM.halt cstate) eqn:H1; [ | congruence]. 
      inv H. eauto.  
    + destruct c. unfold haltConf in H. cbn in H. destruct (TM.halt cstate) eqn:H1. 
      * inv H. eauto. 
      * eapply IHn, H. 
  Qed.

  Lemma simulation : forall s, isValidInput s -> TCSRLang (Build_TCSR (initialString s) allFinSimRules finalSubstrings  t) <-> exists f, loopM (initc TM ([|initialTapeForString s|])) t = Some f.
  Proof. 
    intros. split; intros. 
    - destruct H0 as (finalStr & H1 & H2). cbn [steps init windows final ] in H1, H2.
      erewrite relpower_extensional in H1.
      2: eapply valid_congruent, rewHead_agreement_all.
      specialize (@soundness start (initialTapeForString s) (initialString s) finalStr) as H3. 
      edestruct H3 as (q' & tape' & F1 & ((l & F2 & F3 & F4) & F)). 
      + apply initialString_reprConfig, H. 
      + destruct s; cbn; unfold isValidInput in H; cbn in H; lia. 
      + apply H1.
      + apply finalSubstrings_correct. apply H2. 
      + exists (mk_mconfig q' [|tape'|]). 
        clear H1 H2 H3. 
        apply loop_monotone with (k1 := l); [ | apply F2]. 
        clear F2. 
        unfold initc. 
        apply relpower_loop_agree; eauto. 
    - destruct H0 as ((q' & tape') & H0).  
      unfold TCSRLang. 
      revert H0. 
      eapply VectorDef.caseS' with (v := tape').  
      clear tape'.  intros tape' t0.
      eapply VectorDef.case0 with (v := t0). 
      intros H0. clear t0. 
      cbn [windows steps init final].
      edestruct (@completeness start (initialTapeForString s) q' tape' (initialString s)) as (s' & F1 & F2 & F3). 
      + destruct s; cbn; unfold isValidInput in H; cbn in *; lia. 
      + apply initialString_reprConfig, H. 
      + apply loop_relpower_agree, H0. 
      + exists s'.  split. 
        * eapply relpower_extensional; [apply valid_congruent, rewHead_agreement_all | apply F1]. 
        * apply finalSubstrings_correct, F3. 
  Qed.  

  Lemma reduction_to_inter : (exists s, isValidInput s /\ TCSRLang (Build_TCSR (initialString s) allFinSimRules finalSubstrings t)) <-> (exists s, isValidInput s /\ exists f, loopM (initc TM ([|initialTapeForString s|])) t = Some f). 
  Proof. 
    split; (intros (s & H); exists s; split; [ tauto | now apply simulation]).
  Qed. 
          
End fixTM. 



