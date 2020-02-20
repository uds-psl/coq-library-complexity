From Undecidability Require Import TM.Prelim.
From Undecidability Require Import TM.TM.
From Undecidability Require Import TM.Code.ProgrammingTools.


(** This file is meant as an entry point for the hyperlinks in the paper. For [Check]s, just click them to get to the lemma. *)

From Undecidability.TM Require Import Basic.Mono Basic.Null Compound.Multi.
Section PrimitiveMachines.

  Check Mono.ReadChar_Sem.
  
  Check Mono.Write_Sem.
  
  Check Mono.Move_Sem.
  
  Check Multi.Nop_Sem.

End PrimitiveMachines.


From Undecidability.TM Require Import Univ.StepTM PrettyBounds.UnivBounds PrettyBounds.UnivSpaceBounds.
From Undecidability Require Import Univ.LookupAssociativeListTM.
From Undecidability Require Import Basic.Duo.
From Undecidability Require Import Code.CaseFin Code.CaseList Code.CasePair.
From Undecidability Require Import Univ.LookupAssociativeListTM.

Require Import PslBase.Bijection. (* [injective] *)

Section UniversalMachine.


  Variable (sigM : finType).

  Notation sigGraph := (sigList (sigPair (sigPair (option sigM) sigState) (sigPair (option sigM * move) sigState))).

  (** The alphabet of [Univ] *)
  Variable (sig : finType).
  Variable (retr_sigGraph_sig : Retract sigGraph sig).
  Variable (retr_sigTape_sig : Retract sigM sig).

  (** Encoding of the current state number *)
  Local Definition retr_sigCurrentStateNumber_sigGraph : Retract sigNat sigGraph :=
    Retract_sigList_X (Retract_sigPair_X _ (Retract_sigPair_Y _ (Retract_sigPair_Y _ _))).
  Local Definition retr_sigCurrentStateNumber_sig : Retract sigNat sig :=
    ComposeRetract retr_sigGraph_sig retr_sigCurrentStateNumber_sigGraph.

  (** Encoding of the current state (= halt bit + number) *)
  Local Definition retr_sigCurrentState_sigGraph : Retract sigState sigGraph :=
    Retract_sigList_X (Retract_sigPair_X _ (Retract_sigPair_Y _ (Retract_id _))).
  Local Definition retr_sigCurrentState_sig : Retract sigState sig := ComposeRetract retr_sigGraph_sig retr_sigCurrentState_sigGraph.

  (** Encoding of final bit of the current state *)
  Local Definition retr_sigCurrentStateFinal_sigGraph : Retract bool sigGraph :=
    Retract_sigList_X (Retract_sigPair_X _ (Retract_sigPair_Y _ (Retract_sigPair_X _ _))).
  Local Definition retr_sigCurrentStateFinal_sig : Retract bool sig := ComposeRetract retr_sigGraph_sig retr_sigCurrentStateFinal_sigGraph.

  (** Encoding of the next state *)
  Local Definition retr_sigNextState_sigGraph : Retract sigState sigGraph := Retract_sigList_X (Retract_sigPair_Y _ _).
  Local Definition retr_sigNextState_sig : Retract sigState sig := ComposeRetract retr_sigGraph_sig retr_sigNextState_sigGraph.

  (** Encoding the current symbol *)
  Local Definition retr_sigCurrentSymbol_sigGraph : Retract (option sigM) sigGraph := Retract_sigList_X (Retract_sigPair_X _ (Retract_sigPair_X _ _)).
  Local Definition retr_sigCurrentSymbol_sig: Retract (option sigM) sig := ComposeRetract retr_sigGraph_sig retr_sigCurrentSymbol_sigGraph.

  (** Encoding of actions *)
  Local Definition retr_act_sigGraph : Retract (option sigM * move) sigGraph := _.
  Local Definition retr_act_sig : Retract (option sigM * move) sig := ComposeRetract retr_sigGraph_sig retr_act_sigGraph.

  (** Encoding of the keys for [Lookup] ([option sig * Q]) *)
  Local Definition retr_key_sigGraph : Retract _ sigGraph := Retract_sigList_X (Retract_sigPair_X _ (Retract_id _)).
  Local Definition retr_key_sig : Retract _ sig := ComposeRetract retr_sigGraph_sig retr_key_sigGraph.

  (** Encoding of the value for [Lookup] ([option sig * Q]) *)
  Local Definition retr_value_sigGraph : Retract _ sigGraph := Retract_sigList_X (Retract_sigPair_Y _ (Retract_id _)).
  Local Definition retr_value_sig : Retract _ sig := ComposeRetract retr_sigGraph_sig retr_value_sigGraph.

  
  Local Instance Encode_graph : codable sigGraph (list ((option sigM * (bool * nat)) * ((option sigM * move) * (bool * nat)))) :=
    (Encode_list
       (Encode_pair (Encode_pair (Encode_Finite _) (Encode_pair Encode_bool Encode_nat))
                    (Encode_pair (Encode_Finite _) (Encode_pair Encode_bool Encode_nat)))).

  
  Definition Univ_Rel_pretty : pRel sig^+ unit 6 :=
    fun tin '(_, tout) =>
      forall (M : mTM sigM 1),
        let c := (size (graph_of_TM M) + 1) in
        forall (tp : tape sigM) (q : states M) (s1 s2 : nat) s3 s4 s5,
        tin[@Fin0] = mapTape (fun s => inr (Retr_f (Retract := retr_sigTape_sig) s)) tp ->
        tin[@Fin1] ≃(retr_sigGraph_sig; s1) (graph_of_TM M) ->
        tin[@Fin2] ≃(retr_sigCurrentState_sig; s2) (halt q, index q) ->
        isRight_size tin[@Fin3]  s3 -> isRight_size tin[@Fin4] s4 -> isRight_size tin[@Fin5] s5 ->
        exists k (oconf : mconfig sigM (states M) 1),
          loopM (mk_mconfig q [|tp|]) k = Some oconf /\
          tout[@Fin0] = mapTape (fun s => inr (Retr_f (Retract := retr_sigTape_sig) s)) (ctapes oconf)[@Fin0] /\
          tout[@Fin1]  ≃(retr_sigGraph_sig; s1) (graph_of_TM M) /\
          tout[@Fin2]  ≃(retr_sigCurrentState_sig;  max c s2 + Univ_nice.number_of_states M +2) (halt (cstate oconf), index (cstate oconf)) /\
          isRight_size tout[@Fin3] (max c s3) /\
          isRight_size tout[@Fin4] (max c s4) /\
          isRight_size tout[@Fin5] (max c s5).


  Lemma Univ_Realise_pretty : (Univ _ _) ⊨ Univ_Rel_pretty.
  Proof.
    eapply Realise_monotone.
    { apply Univ_Realise. }
    unfold Univ_Rel_pretty,Univ_Rel.
    unfold containsWorkingTape,containsTrans_size,containsState_size.
    intros tin [l tout].
    refine (Morphisms_Prop.all_impl_morphism _ _ _);intros M;hnf.
    refine (Morphisms_Prop.all_impl_morphism _ _ _);intros tp;hnf.
    refine (Morphisms_Prop.all_impl_morphism _ _ _);intros q;hnf.
    refine (Morphisms_Prop.all_impl_morphism _ _ _);intros s1;hnf.
    refine (Morphisms_Prop.all_impl_morphism _ _ _);intros s2;hnf.

    intros H s3 s4 s5.
    specialize (H [| s3;s4;s5|]).
    
    intros H1 H2 H3 ? ? ?.
    specialize (H H1 H2 H3).
    modpon H.
    {intros i. destruct_fin i. all:cbn. all:easy. }

    destruct H as (k&[tout' s']&?&?&?&?&Hout).
    edestruct (destruct_vector1 s') as (s''&->).
    eexists k, (mk_mconfig tout' [|s''|]).

    specialize (Univ_size_nice H) as (?&H'''1&H'''2&H''1&H''2&H''3).
    
    specialize (Hout Fin0) as H'0;cbn in H'0.
    specialize (Hout Fin1) as H'1;cbn in H'1.
    specialize (Hout Fin2) as H'2;cbn in H'2.

    unfold Univ_size_bound in *.

    repeat eapply conj.
    -assumption.
    -assumption.
    -eapply tape_contains_size_ext with (1:= H7) (2:=eq_refl).
     rewrite H'''1. easy. 
    -eapply tape_contains_size_ext with (1:= H8) (2:=eq_refl).
     specialize (H'''2 s2).
     rewrite !UnivSpaceBounds.Encode_state_hasSize in H'''2.
     assert (Htmp:=state_index_lt q). apply Nat.lt_le_incl in Htmp. rewrite Htmp in H'''2.
     clear - H'''2.
     remember (Univ_nice.number_of_states M).
     remember (size (graph_of_TM M) + 1).
     remember ((Univ_size tp q k)[@Fin2] s2). Lia.nia.
    -eapply isRight_size_monotone;[exact (Hout _)| ].
     rewrite H''1. cbn -[graph_of_TM size]. reflexivity.
    -eapply isRight_size_monotone;[exact (Hout _)| ].
     rewrite H''2. cbn -[graph_of_TM size]. reflexivity.
    -eapply isRight_size_monotone;[exact (Hout _)| ].
     rewrite H''3. cbn -[graph_of_TM size]. reflexivity.
  Qed.

  

  Definition Univ_T_pretty M : tRel sig^+ 6 :=
    let c := proj1_sig (Univ_nice.Univ_steps_nice M) in
    fun tin k =>
        exists (tp : tape sigM) (q : states M) (k' : nat) (q' : states M) (tp' : tape sigM),
        tin[@Fin0] = mapTape (fun s => inr (Retr_f (Retract := retr_sigTape_sig) s)) tp /\
        tin[@Fin1] ≃(retr_sigGraph_sig) (graph_of_TM M) /\
        tin[@Fin2] ≃(retr_sigCurrentState_sig) (halt q, index q) /\
        isRight tin[@Fin3] /\ isRight tin[@Fin4] /\ isRight tin[@Fin5] /\
        loopM (mk_mconfig q [|tp|]) k' = Some (mk_mconfig q' [|tp'|]) /\
        c* (1+k') * size (graph_of_TM M) <= k.


  (** This lemma ransforms the lemma we proofed in Coq to the more readable version in the paper. *)
  Lemma Univ_Terminates_pretty M: projT1 (Univ _ _) ↓ Univ_T_pretty M.
  Proof.
    eapply TerminatesIn_monotone.
    {apply Univ_Terminates. }
    unfold Univ_T_pretty,Univ_T.
    unfold containsWorkingTape,containsTrans,containsState.
    intros tin k.
    intros H. exists M. revert H.
    apply Morphisms_Prop.ex_impl_morphism;intro tp;hnf.
    apply Morphisms_Prop.ex_impl_morphism;intro q;hnf.
    apply Morphisms_Prop.ex_impl_morphism;intro k';hnf.
    apply Morphisms_Prop.ex_impl_morphism;intro q';hnf.
    apply Morphisms_Prop.ex_impl_morphism;intro tp';hnf.

    intros (?&?&?&?&?&?&?&Heq).
    repeat eapply conj.
    1-3,5:easy.
    -intros i. destruct_fin i. all:easy.
    -assert (Heq':=proj2_sig (Univ_nice.Univ_steps_nice M)).
     unfold PrettyBounds.dominatedWith in Heq'.
     rewrite Heq'.
     rewrite <- Heq, Encode_nat_hasSize. now rewrite <-mult_assoc.
  Qed.

End UniversalMachine.
