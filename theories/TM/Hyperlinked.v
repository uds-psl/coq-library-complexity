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

  Definition Univ_T_pretty : tRel sig^+ 6 :=
    fun tin k =>
      exists (M : mTM sigM 1),
        let c := proj1_sig (Univ_nice.Univ_steps_nice M) in
        exists (tp : tape sigM) (q : states M) (k' : nat) (q' : states M) (tp' : tape sigM),
        tin[@Fin0] = mapTape (fun s => inr (Retr_f (Retract := retr_sigTape_sig) s)) tp /\
        tin[@Fin1] ≃(retr_sigGraph_sig) (graph_of_TM M) /\
        tin[@Fin2] ≃(retr_sigCurrentState_sig) (halt q, index q) /\
        isRight tin[@Fin3] /\ isRight tin[@Fin4] /\ isRight tin[@Fin5] /\
        loopM (mk_mconfig q [|tp|]) k' = Some (mk_mconfig q' [|tp'|]) /\
        c* (size k' * size (graph_of_TM M)) <= k.


  (** This lemma ransforms the lemma we proofed in Coq to the more readable version in the paper. *)
  Lemma Univ_Terminates_pretty : projT1 (Univ _ _) ↓ Univ_T_pretty.
  Proof.
    eapply TerminatesIn_monotone.
    {apply Univ_Terminates. }
    unfold Univ_T_pretty,Univ_T.
    unfold containsWorkingTape,containsTrans,containsState.
    intros tin k.
    apply Morphisms_Prop.ex_impl_morphism;intro M;hnf.
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
     rewrite <- Heq. reflexivity.
  Qed.

End UniversalMachine.
