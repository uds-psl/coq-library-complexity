From Complexity.NP.SAT.CookLevin Require Import TCC.
From Complexity.Libs.CookPrelim Require Import MorePrelim.
From Undecidability.Shared.Libs.PSL Require Import Base FinTypes. 
Require Import Lia. 

(** * Adding preludes to P-3-CC instances *)
(** We introduce preludes for TCC instances (for simplicity, we restrict ourselves to the propositional variant PTCC) *)

(** Preludes allow us to reduce the problem "∃ init, P init ∧ PTCCLang (instance(init))" to "PTCCLang (instance')", where 
  instance is a PTCC instance which lacks an initial string and P is an arbitrary predicate on initial strings. 
  A prelude is a set of covering cards together with a new initial string which generates a new string.
  
  If we can find a set of covering cards and an initial string as well as a number of steps t' such that the initial string
  can go in t' steps to exactly those strings satisfying P, we can do the above reduction by adding the new cards, fixing 
  the initial string and adding t' to the number of steps of instance. 

  In order to ensure that the new covering cards and the old ones do not interfere, we require their alphabets to be disjoint
  (but of course, the prelude needs to make steps to strings of the old alphabet; it just is not allowed to make steps *from* 
  strings of the old alphabet). 
  In this formalisation, this constraint is mostly enforced syntactically by taking the new alphabet to be the sum of 
  the prelude alphabet and the old alphabet.
  *)

(** Remark: One can also see preludes of providing a limited form of compositionality; for instance, one can also show that preludes allow one to reduce an existential question to another (possibly simpler) existential question (see below).
  *)

Section defExPTCC. 
  (** original instance lacking an initial string*)
  Variable (Sigma : finType). 
  (* we do not directly assume Sigma to be a finType in order to be able to use the definitions not depending on Sigma being a finType for ordinary Types *)

  Variable (p : Sigma -> Sigma -> Sigma -> Sigma -> Sigma -> Sigma -> Prop). 
  Variable (finalCondition : list (list Sigma)). 
  Variable (t : nat). 

  (** instead of an initial string, we have an initial condition and a length l*)
  Variable (initCond: list Sigma -> Prop). 
  Variable (l : nat).

  (** the question now is: does there exist x0 satisfying initCond such that it ends up in a final state? *)
  Definition ExPTCC := exists x0, |x0| = l /\ initCond x0 /\ PTCCLang (Build_PTCC x0 p finalCondition t). 
End defExPTCC.

Section fixPTCCInstance. 
  Variable (Sigma : Type). 

  Variable (ESigma : eq_dec Sigma). 
  Variable (FSigma : finTypeC (EqType Sigma)). 

  Variable (p : Sigma -> Sigma -> Sigma -> Sigma -> Sigma -> Sigma -> Prop). 
  Variable (finalCondition : list (list Sigma)). 
  Variable (t : nat). 

  Variable (initCond: list Sigma -> Prop). 
  Variable (l : nat).

  (** otherwise, vacuous rewrites destroy everything *)
  Variable (A0 : l >= 3). 

  (** a prelude generates initial strings satisfying initCond *)
  Variable (Sigma' : Type). 
  Variable (eSigma' : eq_dec Sigma').
  Variable (FSigma' : finTypeC (EqType Sigma')). 

  Notation combSigma := (sum Sigma Sigma').
  Variable (p' : Sigma' -> Sigma' -> Sigma' -> combSigma -> combSigma -> combSigma -> Prop). 
  (** We prove the following results not for a fixed initial string, but for a string satisfying initialPred.
    This allows us to compose multiple preludes, each reducing to a simpler ExPTCC instance.
  *)
  Variable (initialPred : list Sigma' -> Prop).   
  Variable (t' : nat). 

  Definition isOrigString (s : list combSigma) := exists s', s = map inl s'.  
  Definition isPreludeString (s : list combSigma) := exists s', s = map inr s'. 

  Inductive liftPrelude : cardPred combSigma := 
    | liftPreludeC (a b c : Sigma') (d e f : combSigma) : p' a b c d e f -> liftPrelude (inr a) (inr b) (inr c) d e f. 

  Inductive liftOrig : cardPred combSigma := 
    | liftOrigC (a b c d e f : Sigma) : p a b c d e f -> liftOrig (inl a) (inl b) (inl c) (inl d) (inl e) (inl f).  

  Hint Constructors liftPrelude liftOrig : core. 

  Definition combP a b c d e f := liftPrelude a b c d e f \/ liftOrig a b c d e f.
  Hint Unfold combP : core. 

  Definition validPreludeInitial s := length s = l /\ initialPred s. 

  (** The prelude rules always produce a string that is a valid initial string for the original instance, up to the injection inl *)
  Variable (A1: forall init x0, validPreludeInitial init -> relpower (valid (coversHeadInd liftPrelude)) t' (map inr init) x0 -> isOrigString x0). 

  (** Disjointness: string is not produced too early *)
  Variable (A2 : forall init k x, validPreludeInitial init -> k < t' -> relpower (valid (coversHeadInd liftPrelude)) k (map inr init) x -> isPreludeString x).  

  (** Completeness *)
  Variable (A3 : forall x0, initCond x0 /\ |x0| = l -> exists init, validPreludeInitial init /\ relpower (valid (coversHeadInd liftPrelude)) t' (map inr init) (map inl x0)). 

  (** Soundness *)
  Variable (A4 : forall init x0, validPreludeInitial init -> relpower (valid (coversHeadInd liftPrelude)) t' (map inr init) x0 -> exists x0', x0 = map inl x0' /\ initCond x0'). 

  Lemma liftPrelude_subs_combP : cardPred_subs liftPrelude combP. 
  Proof. 
    unfold cardPred_subs. intros. inv H. eauto. 
  Qed. 

  Hint Constructors valid : core. 

  Ltac inv_eqn_map := repeat match goal with 
    | [H : _ :: ?a = map _ ?s |- _] => is_var s; destruct s; cbn in H; [congruence | inv H]
    | [H : [] = map _ ?s |- _] => is_var s; destruct s; cbn in H; [ clear H| congruence]
  end. 

  Section fixInitial.
    Variable (initialString : list Sigma').
    Context {Hinitial : validPreludeInitial initialString}.

    Lemma relpower_inr_liftPrelude' n b: 
      n < t' 
      -> relpower (valid (coversHeadInd combP)) n (map inr initialString) b 
      -> relpower (valid (coversHeadInd liftPrelude)) n (map inr initialString) b /\ isPreludeString b.
    Proof. 
      intros H0 H. clear A0 A1 A3 A4. 
      remember (map inr initialString). 
      (** we use the version of relpower defined by adding transitions at the tail of a chain since we need to keep A2, which requires the initialString at the head (otherwise, we could not apply the IH) *)
      apply relpower_relpowerRev in H. setoid_rewrite relpower_relpowerRev. 
      induction H as [ ? | ? ? ? ? H IH H1]; cbn; subst. now eauto.
      edestruct IH as (IH' & (? & ->)); clear IH. lia. reflexivity. 
      assert (valid (coversHeadInd liftPrelude) (map inr x) y') as H3.   
      { 
        clear IH' H. remember (map inr x) as x' eqn:H. revert x H. 
        induction H1 as [ | ? ? ? ? H IH H2 | ? ? ? ? H IH H2]; cbn; intros; eauto; inv_eqn_map. 
        + constructor 2; [eapply IH; reflexivity | auto]. 
        + constructor 3; [eapply IH; reflexivity | clear IH]. 
          inv H2. inv_eqn_map.
          inv H3;  [eauto |  ]. inv H1. 
      }
      split. 
      * apply relpowerRevS with (y := map inr x); [ apply IH' | apply H3]. 
      * (*we use A2 to derive that b is a preludeString *)
        assert (relpower (valid (coversHeadInd liftPrelude)) (S n) (map inr initialString) y') as H2. 
        { apply relpower_relpowerRev. eauto. }
        now apply A2 in H2. 
    Qed.  

    Corollary relpower_inr_liftPrelude n b : 
      n <= t' 
      -> relpower (valid (coversHeadInd combP)) n (map inr initialString) b 
      -> relpower (valid (coversHeadInd liftPrelude)) n (map inr initialString) b.
    Proof. 
      intros. clear A0 A1 A3 A4. destruct (lt_dec n t') as [l0 | l0]. 
      - eapply relpower_inr_liftPrelude' in H0; [ | apply l0]. tauto. 
      - assert (n = t') by lia. clear H l0. destruct n. 
        + inv H0. auto. 
        + assert (n < t') as H2 by lia. apply relpower_relpowerRev in H0. inversion H0. 
          apply relpower_relpowerRev in H3. apply relpower_inr_liftPrelude' in H3 as (H3 & (? & ->)); subst; [ | apply H2].
          apply relpower_relpowerRev. econstructor; [ apply relpower_relpowerRev, H3 | ]. 
          clear H2 H3 H0 A2. remember (map inr x0) as x1 eqn:Heqn. revert x0 Heqn. induction H4; intros.  
          * eauto. 
          * inv_eqn_map; constructor; eauto.
          * inv_eqn_map; constructor 3; [eauto | ]. inv H. inv_eqn_map. inv H1; [ eauto | ]. inv H. 
    Qed. 

    Lemma relpower_inl_liftOrig n s b : 
      |s| >= 3  
      -> relpower (valid (coversHeadInd combP)) n (map inl s) b 
      -> relpower (valid (coversHeadInd liftOrig)) n (map inl s) b /\ isOrigString b. 
    Proof. 
      clear A0 A1 A2 A3 A4. intros H0 H. remember (map inl s) as s' eqn:Heqn. 
      enough (relpower (valid (coversHeadInd liftOrig)) n s' b /\ isOrigString b) by tauto. 
      revert s H0 Heqn. 
      induction H as [? | ? ? ? ? H H0 IH]; intros s H1 Heqn. 
      - subst; split; unfold isOrigString; eauto. 
      - assert (valid (coversHeadInd liftOrig) a b /\ isOrigString b) as (H2 & (? & ->)). 
        { 
          clear IH H0. revert s H1 Heqn. unfold isOrigString. 
          induction H as [ | ? ? ? ? H IH H0 | ? ? ? ? H IH H0]; intros.
          + eauto. 
          + inv_eqn_map. rewrite map_length in H0; cbn in H1; lia.   
          + inv_eqn_map. inv H0. inv_eqn_map. inv H3; inv H0.
            destruct s4; cbn in *. 
            -- apply valid_length_inv in H; destruct s2; [ | cbn in H; congruence]. 
               split.
               ++ constructor 3. constructor 2; cbn; eauto.  eauto.
               ++ exists [d; e; f]; eauto. 
            -- edestruct (IH (s0::s3::s1::s4)) as (H2 & (? & H3)); [now cbn | now cbn | inv_eqn_map ]. 
               split; [eauto | ]. exists (d :: s5 :: s6 :: x); eauto.  
        } 
        subst. 
        edestruct (IH) as (IH1 & IH2). 
        2: { reflexivity. }
        + apply valid_length_inv in H. rewrite !map_length in H. lia. 
        + split; [ | apply IH2]. apply relpowerS with (b := map inl x); [ apply H2 |apply IH1].  
    Qed. 

    (** important intermediate result for the proof: we can split a sequence of t' + t rewrite steps into t' rewrite steps of the prelude and t rewrite steps of the original CC instance *)
    Lemma relpower_comb_split sf : 
      relpower (valid (coversHeadInd combP)) (t' + t) (map inr initialString) sf 
      -> exists x0, relpower (valid (coversHeadInd liftPrelude)) t' (map inr initialString) x0 
                    /\ relpower (valid (coversHeadInd liftOrig)) t x0 sf /\ isOrigString sf.
    Proof. 
      clear A3 A4. 
      intros (z & H1 & H2)%relpower_add_split. 
      exists z. apply relpower_inr_liftPrelude in H1; [ | auto]. split. 
      - apply H1. 
      - specialize (A1 Hinitial H1) as (? & ->). eapply relpower_inl_liftOrig. 
        + clear H2 A2. 
          apply relpower_valid_length_inv in H1. rewrite !map_length in H1. rewrite <-H1, (proj1 Hinitial). lia. 
        + apply H2. 
    Qed. 
  End fixInitial. 

  (** we need to be able to go back from liftOrig to p*)
  Lemma valid_liftOrig_isOrigString a b : |a| >= 3 -> valid (coversHeadInd liftOrig) a b -> isOrigString b. 
  Proof. 
    clear A1 A2 A3 A4 A0. intros H. induction 1 as [ | ? ? ? ? H0 IH H1 | ? ? ? ? H0 IH H1]; unfold isOrigString. 
    - exists []; eauto.
    - cbn in H; lia. 
    - cbn in H. inv H1. destruct s1. 
      + apply valid_length_inv in H0. destruct s2; [ | cbn in H0; congruence]. 
        inv H3. exists [d; e; f]; eauto. 
      + cbn in *. edestruct IH as (? & ->); [ lia| ]. inv H3. 
        exists (d :: x0); eauto. 
  Qed. 

  Lemma liftOrig_valid_p x x': valid (coversHeadInd liftOrig) (map inl x) (map inl x') -> valid (coversHeadInd p) x x'.
  Proof. 
    clear A1 A2 A3 A4 A0. 
    remember (map inl x) as x0 eqn:eqnx0. remember (map inl x') as x0' eqn:eqnx0'. 
    induction 1 as [ | ? ? ? ? H IH H0 | ? ? ? ? H IH H0] in x, x', eqnx0, eqnx0' |- *; inv_eqn_map. 
    - eauto. 
    - constructor; [ | rewrite map_length in H0; apply H0]. now apply IH.
    - constructor 3. 
      + inv H0; inv_eqn_map. inv H2. eauto. 
      + inv H0; inv_eqn_map. inv H2. eauto. 
  Qed. 

  Lemma liftOrig_relpower_p n x sf : 
    |x| >= 3
    -> relpower (valid (coversHeadInd liftOrig)) n (map inl x) (map inl sf) 
    -> relpower (valid (coversHeadInd p)) n x sf. 
  Proof. 
    clear A1 A2 A3 A4 A0. intros H0 H. remember (map inl x) as x' eqn:Hx'. remember (map inl sf) as sf' eqn:Hsf'. 
    revert x sf H0 Hx' Hsf'. 
    induction H as [ | ? ? ? ? H H0 IH]; intros. 
    - subst; apply map_injective in Hsf'; [ subst; auto| unfold injective; intros; congruence]. 
    - assert (|a| >= 3) as H2. { subst. rewrite map_length. apply H1. } 
      specialize (valid_liftOrig_isOrigString H2 H) as (? & ->). econstructor. 
      + subst. apply liftOrig_valid_p, H.  
      + eapply IH; [ | reflexivity | eauto].  
        subst. apply valid_length_inv in H. now rewrite !map_length in H.  
  Qed. 

  Lemma relpower_valid_map_inl x0 xt m: relpower (valid (coversHeadInd p)) m x0 xt -> relpower (valid (coversHeadInd combP)) m (map inl x0) (map inl xt).
  Proof. 
    intros H. induction H as [ | ? ? ? ? H H0 IH]. 
    - constructor. 
    - econstructor. 2: apply IH. 
      clear H0 IH. induction H as [ | ? ? ? ? H IH H0 | ? ? ? ? H IH H0].
       + cbn; constructor. 
       + cbn; constructor; [ apply IH | rewrite map_length; apply H0]. 
       + cbn; constructor 3; [apply IH | ]. inv H0. cbn; eauto.  
  Qed.

  Lemma lift_final sf : satFinal finalCondition sf <-> satFinal (map (map inl) finalCondition : list (list combSigma)) (map inl sf). 
  Proof. 
    split. 
    - intros H. unfold satFinal in *. destruct H as (subs & H1 & H2). exists (map inl subs). 
      split. 
      + apply in_map_iff. eauto.  
      + unfold substring. destruct H2 as (b1 & b2 & H2). 
        exists (map inl b1), (map inl b2). now rewrite H2, !map_app. 
    - unfold satFinal in *. intros H.
      destruct H as (subs & H1 & H2). apply in_map_iff in H1 as (subs' & <- & H1).
      exists subs'; split; [apply H1 | ]. 
      unfold substring in *. destruct H2 as (b1 & b2 & H). 
      apply map_eq_app in H as (b1' & b & H & -> & H2). 
      symmetry in H2. apply map_eq_app in H2 as (b' & b2' & -> & H2 & ->). 
      exists b1', b2'. enough (subs' = b') by (subst; reflexivity). 
      apply map_injective in H2; [apply H2 | unfold injective; congruence].
  Qed.

  (** Reduction to ExPTCC *)
  (** This result enables one to reduce an ExPTCC instance to another (potentially simpler) ExPTCC instance *)
  Lemma red_to_exptpr : ExPTCC p finalCondition t initCond l <-> ExPTCC combP (map (map inl) finalCondition) (t' + t) (fun s => exists s', s = map inr s' /\ initialPred s') l. 
  Proof. 
    split; intros H. 
    - destruct H as (x0 & H1 & H2 & H3). 
      destruct (A3 (conj H2 H1)) as (init & F1 & F2). 
      exists (map inr init). 
      split; [ rewrite map_length; apply F1 | split; [ exists init; split; [easy | apply F1] | ] ]. 
      destruct H3 as (G1 & (sf & G2 & G3)). 
      split. 
      {unfold PTCC_wellformed. cbn. rewrite map_length. unfold validPreludeInitial in F1. lia. }
      exists (map inl sf). 
      cbn; split. 
      + eapply relpower_trans. 
        * eapply relpower_monotonous. 
          { eapply valid_monotonous. eapply coversHeadInd_monotonous. apply liftPrelude_subs_combP. }
          apply F2.  
        * cbn in G2. now apply relpower_valid_map_inl. 
      + now apply lift_final. 
    - destruct H as (x0 & H1 & H2 & H3). 
      destruct H2 as (initialString & -> & H2). rewrite map_length in H1.
      destruct H3 as (H3 & sf & Hv & Hf). cbn in *.
      assert (validPreludeInitial initialString) as Hi by easy.
      apply (@relpower_comb_split initialString Hi) in Hv as (x0 & H4 & H5 & H6). 
      specialize (A1 Hi H4) as (x0' & ->). exists x0'. split; [ | split]. 
      + apply relpower_valid_length_inv in H4. rewrite !map_length in H4. cbn. lia.
      + apply (A4 Hi) in H4. destruct H4 as (? & H4' & H4). 
        apply map_injective in H4'; [subst; apply H4 | unfold injective; intros; congruence  ]. 
      + unfold PTCCLang. split. 
        1: { 
          unfold PTCC_wellformed. cbn. 
          apply relpower_valid_length_inv in H4. rewrite !map_length in H4. cbn. lia. 
        }
        cbn. destruct H6 as (sf' & ->). exists sf'. split. 
        * eapply liftOrig_relpower_p, H5. 
          apply relpower_valid_length_inv in H4. rewrite !map_length in H4. lia.
        * now apply lift_final. 
  Qed. 
End fixPTCCInstance.

(** We now specialise to the case where the initial condition on the prelude string is fixed to equality with a given string, 
  i.e. we reduce an ExPTCC instance to a full PTCC instance
*)
Section fixPrelude. 
  Variable (Sigma : Type). 

  (**We do not directly assume Sigma to be a finType in order to be able to use the definitions not depending on Sigma being a finType for ordinary Types *)
  Variable (ESigma : eq_dec Sigma). 
  Variable (FSigma : finTypeC (EqType Sigma)). 

  Variable (p : Sigma -> Sigma -> Sigma -> Sigma -> Sigma -> Sigma -> Prop). 
  Variable (finalCondition : list (list Sigma)). 
  Variable (t : nat). 

  Variable (initCond: list Sigma -> Prop). 
  Variable (l : nat).

  (** Otherwise, vacuous rewrites destroy everything *)
  Variable (A0 : l >= 3). 

  (** A prelude generates initial strings satisfying initCond *)
  Variable (Sigma' : Type). 
  Variable (eSigma' : eq_dec Sigma').
  Variable (FSigma' : finTypeC (EqType Sigma')). 

  Notation combSigma := (sum Sigma Sigma').
  Variable (p' : Sigma' -> Sigma' -> Sigma' -> combSigma -> combSigma -> combSigma -> Prop). 

  (** We specialise to a fixed initial string *)
  Variable (initialString : list Sigma').
  Variable (t' : nat). 

  Hint Constructors liftPrelude liftOrig : core. 
  Hint Unfold combP : core. 

  Notation liftPrelude := (liftPrelude p').
  Notation combP := (combP p p').

  (** The prelude rules always produce a string that is a valid initial string for the original instance, up to the injection inl *)
  Variable (A1: forall x0, relpower (valid (coversHeadInd liftPrelude)) t' (map inr initialString) x0 -> isOrigString x0). 

  (** disjointness: string is not produced too early *)
  Variable (A2 : forall k x, k < t' -> relpower (valid (coversHeadInd liftPrelude)) k (map inr initialString) x -> isPreludeString x).  

  (** completeness *)
  Variable (A3 : forall x0, initCond x0 /\ |x0| = l -> relpower (valid (coversHeadInd liftPrelude)) t' (map inr initialString) (map inl x0)). 

  (** soundness *)
  Variable (A4 : forall x0, relpower (valid (coversHeadInd liftPrelude)) t' (map inr initialString) x0 -> exists x0', x0 = map inl x0' /\ initCond x0'). 

  Variable (A5 : length initialString = l). 

  (** We use the results of the previous section. For that, we setup the initial condition and prove the assumptions the previous section has. *)
  Definition preludeInitialPred s := s = initialString. 

  Notation validPreludeInitial := (validPreludeInitial l preludeInitialPred). 

  Fact A1p init x0 : validPreludeInitial init -> relpower (valid (coversHeadInd liftPrelude)) t' (map inr init) x0 -> isOrigString x0.
  Proof. 
    intros [H1 ->]. easy.
  Qed. 

  Fact A2p init k x: validPreludeInitial init -> k < t' -> relpower (valid (coversHeadInd liftPrelude)) k (map inr init) x -> isPreludeString x.
  Proof. 
    intros [H1 ->]. easy. 
  Qed. 

  Fact A3p x0: initCond x0 /\ |x0| = l -> exists init, validPreludeInitial init /\ relpower (valid (coversHeadInd liftPrelude)) t' (map inr init) (map inl x0).
  Proof. 
    intros [H1 H2]. exists initialString. split; [ | easy]. split; [easy | reflexivity]. 
  Qed. 

  Fact A4p init x0: validPreludeInitial init -> relpower (valid (coversHeadInd liftPrelude)) t' (map inr init) x0 -> exists x0', x0 = map inl x0' /\ initCond x0'.
  Proof. 
    intros [H1 ->]. easy. 
  Qed. 

  Fact initialString_validPreludeInitial : validPreludeInitial initialString. 
  Proof. easy. Qed. 

  (** The main result *)
  Lemma prelude_ok : ExPTCC p finalCondition t initCond l <-> PTCCLang (Build_PTCC (map inr initialString) combP (map (map inl) finalCondition) (t' + t)). 
  Proof. 
    split. 
    - intros (x0 & H1 & H2 & (_ & sf & F1 & F2)). cbn in *. split. 
      1 : { unfold PTCC_wellformed. cbn. rewrite map_length, A5. lia. }
      exists (map inl sf). cbn. split. 
      + eapply relpower_trans.
        * eapply relpower_monotonous. 
          { eapply valid_monotonous. eapply coversHeadInd_monotonous. apply liftPrelude_subs_combP. }
          apply A3. eauto. 
        * now apply relpower_valid_map_inl.
      + now apply lift_final. 
    - intros (_ & sf & F1 & F2). cbn in *. unfold ExPTCC. 
      (*we need to split up F1 into the prelude and original part *)
      apply (@relpower_comb_split Sigma p t initCond l A0 Sigma' p' preludeInitialPred t' A1p A2p initialString initialString_validPreludeInitial) in F1 as (x0 & H1 & H2 & H3). 
      specialize (A1 H1) as (x & ->). exists x. split; [ | split]. 
      + apply relpower_valid_length_inv in H2. rewrite map_length in H2. 
        apply relpower_valid_length_inv in H1. rewrite !map_length in H1. rewrite <- A5, H1. easy. 
      + apply A4 in H1. destruct H1 as (? & H1 & H4). apply map_injective in H1; [subst; apply H4 | ]. 
        unfold injective. intros. congruence. 
      + unfold PTCCLang. split. 
        1: { 
          unfold PTCC_wellformed. cbn. 
          apply relpower_valid_length_inv in H1. rewrite !map_length in H1. lia. }
        cbn. destruct H3 as (sf' & ->). exists sf'. split. 
        * clear F2 A2 A3 A4. eapply liftOrig_relpower_p, H2. 
          apply relpower_valid_length_inv in H1.  rewrite !map_length in H1. lia.
        * now eapply lift_final. 
  Qed. 
End fixPrelude. 
