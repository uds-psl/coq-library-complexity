From Undecidability.TM Require Import TM.
From Undecidability.L.Complexity Require Import MorePrelim. 
Require Import Lia. 

(** * Simpler definitions for single-tape Turing machines. *)
(** We introduce easier definitions for single-tape Turing machines where the single tape is not wrapped in a singleton vector.
    We also define a relpower-based computation relation (instead of using loopM). 
    (This is motivated by the fact that it is easier to reason inductively about a relpower-based relation.)
*)

Section TM_single. 
  (** We use a variant of the Turing machine definitions fixed to a single tape *)

  Variable (Sigma : finType).
  Variable (TM : mTM Sigma 1). 

  Local Notation mstates := (@TM.states Sigma 1 TM). 
  Local Notation mtrans := (@TM.trans Sigma 1 TM). 
  Local Notation start := (@TM.start Sigma 1 TM). 
  Local Notation halt := (@TM.halt Sigma 1 TM). 

  Definition strans (a : mstates * option Sigma) : (mstates * (option Sigma * move)) :=
    let (q, t) := a in let (q', ac) := mtrans (q, [| t |]) in (q', Vector.nth ac Fin.F1). 
                                                                                            
  Definition sconfig := (mstates * tape Sigma)%type. (* single-tape configuration*)
  Implicit Type (c : sconfig). 
  Definition sstep  (trans : mstates * option Sigma -> mstates * (option Sigma * move)) c : sconfig := let (q, tp) := c in let (q', act) := trans (q, current tp) in (q', doAct tp act).

  Definition mconfig_for_sconfig c := let (q, tp) := c in mk_mconfig q [| tp |].
  Definition sconfig_for_mconfig (c : mconfig Sigma mstates 1) := let (q, tps) := c in (q, Vector.nth tps Fin.F1).

  Lemma vec_case1 (X : Type) (v : Vector.t X 1) : exists x, v = [|x|].
  Proof. 
    eapply Vector.caseS' with (v0:=v).
    intros. revert t. apply Vector.case0. easy.
  Qed. 

  (** Agreement for single computation steps *)
  Lemma sstep_agree1 c : sconfig_for_mconfig (@step Sigma 1 TM (mconfig_for_sconfig c)) = sstep strans c.
  Proof. 
    destruct c. cbn.
    destruct mtrans eqn:H1. unfold sconfig_for_mconfig.
    unfold step. unfold doAct_multi. cbn. unfold current_chars. cbn. setoid_rewrite H1. 
    specialize(vec_case1 t0) as (? & ->). 
    erewrite Vector.nth_map2 with (p2 := Fin0) (p3 := Fin0). 2-3: reflexivity. cbn. reflexivity.  
  Qed. 

  Lemma sstep_agree2 (c : mconfig Sigma mstates 1) : mconfig_for_sconfig (sstep strans (sconfig_for_mconfig c)) = step (c : mconfig Sigma (states TM) 1).  
  Proof.
    destruct c. cbn. unfold step. cbn. unfold current_chars.
    assert ([| current ctapes[@Fin0]|] = Vector.map (current (sig := Sigma)) ctapes). 
    { specialize (vec_case1 ctapes) as (? & ->). easy.  }
    rewrite H. destruct mtrans eqn:H1. 
    cbn. 
    specialize (vec_case1 t) as (? & ->). 
    specialize (vec_case1 ctapes) as (? & ->).
    cbn. reflexivity. 
  Qed. 

  Definition configState c := match c with (q, _) => q end. 
  Definition sstepRel s s' := halt (configState s) = false /\ sstep strans s = s'.

  Notation "s '≻' s'" := (sstepRel s s') (at level 50).
  Notation "s '≻(' k ')' s'" := (relpower sstepRel k s s') (at level 40). 

  (** This is similar to what loopM does*)
  Notation "s '▷(' k ')' s'" := (s ≻(k) s' /\ halt (configState s') = true) (at level 40).
  Notation "s '▷(≤' k ')' s'" := (exists l, l <= k /\ s ▷(l) s') (at level 40).

  (** Agreement of loop and relpower *)
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
       setoid_rewrite <- (sstep_agree2 (mk_mconfig q [|tape|])). 
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
    - specialize (sstep_agree1 (q, tape)) as H2. 
      cbn [mconfig_for_sconfig] in H2. 
      destruct (step (mk_mconfig q [|tape|])) as (q''  &tape'') eqn:H3. 
      revert H H3 H2. 
      specialize (vec_case1 tape'') as (? & ->).
      intros H H3 H2. 
      apply IHn in H as (l & F1 & F2 & F3).  
      exists (S l). repeat split .
      + lia. 
      + econstructor. 2: apply F2. unfold sstepRel. rewrite <- H2. cbn. eauto. 
      + apply F3. 
  Qed. 
  
  Lemma loopM_halt sig l (M : mTM sig l) (c : TM.mconfig sig (TM.states M) l) n (q' : TM.states M) tape' : 
    loopM c n = Some (mk_mconfig q' tape') -> TM.halt q' = true.
  Proof. 
    intros. revert c q' tape' H. induction n; intros; cbn in H. 
    + unfold haltConf in H. destruct c. cbn in H. destruct (TM.halt cstate) eqn:H1; [ | congruence]. 
      inv H. eauto.  
    + destruct c. unfold haltConf in H. cbn in H. destruct (TM.halt cstate) eqn:H1. 
      * inv H. eauto. 
      * eapply IHn, H. 
  Qed.

  (** A Turing machine can only use one additional cell per computational step. *)
  Lemma tm_step_size q tp q' tp' l: (q, tp) ≻ (q', tp') -> sizeOfTape tp = l -> sizeOfTape tp' <= S l. 
  Proof. 
    intros. 
    destruct H as (_ & H). unfold sstep in H. destruct tp; destruct strans; destruct p as ([] & []); cbn in *; inv H; subst;  cbn in *.
    all: try lia. 
    all: repeat match goal with
    | [ |- context[midtape ?l _ _] ] => is_var l; destruct l; cbn in *
    | [ |- context[midtape _ _ ?l] ] => is_var l; destruct l; cbn in *
    | [ |- context[tape_move_left' ?l _ _]] => is_var l; destruct l; cbn in *
    | [ |- context[tape_move_left' _ _ ?l]] => is_var l; destruct l; cbn in *
    | [ |- context[tape_move_right' ?l _ _]] => is_var l; destruct l; cbn in *
    | [ |- context[tape_move_right' _ _ ?l]] => is_var l; destruct l; cbn in *
    | [ |- context[(| _ ++ _ |)] ] => rewrite app_length in H
    | [ |- context[(| rev _ |)] ] => rewrite rev_length in H
    | [ |- context[(| _ ++ _|)]] => rewrite app_length
    | [ |- context[(| rev _ |)]] => rewrite rev_length
    end; cbn in * ; try lia.
  Qed. 
End TM_single.


