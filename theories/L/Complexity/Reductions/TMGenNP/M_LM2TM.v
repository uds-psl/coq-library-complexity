From Undecidability.L.Complexity Require Import NP.
From Undecidability.TM Require TM ProgrammingTools CaseList CaseBool Code.Decode Code.DecodeList.
From Undecidability.TM Require Import TM SizeBounds.

From Undecidability.L.Complexity  Require Import TMGenNP_fixed_mTM UpToCNary.

From Undecidability.L.AbstractMachines Require Import FlatPro.Programs.
     
Unset Printing Coercions.

From Undecidability.LAM Require Alphabets.

From Coq Require Import Lia Ring Arith.

From Undecidability.L.Complexity  Require Import GenNP_is_hard LMGenNP TMGenNP_fixed_mTM M_Boollist_to_Enc.
Check fun M =>
  restrictBy (LMHaltsOrDiverges _) (LMGenNP (list bool)) ⪯p (restrictBy (HaltsOrDiverges_fixed_mTM M) (TMGenNP_fixed_mTM M)).

From Undecidability Require Import Code.ListTM_concat_repeat.

From Undecidability.LAM Require HaltingProblem.

Import DecodeList Decode.
Module LMtoTM.
  Section sec.
    Import ProgrammingTools Combinators HaltingProblem.

    Variable (sig : finType).
    
    Context `{retr__LAM : Retract sigStep sig}
            `{retr__list : Retract (sigList bool) sig}.

    
    Definition retr__listHClos : Retract (sigList Alphabets.sigHClos) sig
      := ComposeRetract retr__LAM retr_closures_step.

    Definition retr__Heap : Retract Alphabets.sigHeap sig
    := ComposeRetract retr__LAM retr_heap_step.

    Definition retr__HClos : Retract Alphabets.sigHClos sig :=
      ComposeRetract retr__listHClos _.
        
    Definition retr__pro : Retract Alphabets.sigPro sig.
    Proof.
      eapply ComposeRetract. apply retr__HClos. easy.
    Defined.

    Definition retr__nat : Retract sigNat sig.
    Proof. 
      eapply ComposeRetract. 2:apply JumpTargetTM.retr_nat_prog. apply retr__pro.
    Defined.
    

     (*
    Print HaltingProblem.Loop_Rel.
    ignoreParam
      (fun tin tout : Vector.t (tape (boundary + HaltingProblem.sigStep)) 11 =>
         forall (T V : list LM_heap_def.HClos) (H : LM_heap_def.Heap) (s0 s1 s2 : nat) (sr : Vector.t nat 8),
           tin[@Fin0] ≃(Retract_inl Alphabets.sigHeap (Retract_id (sigList Alphabets.sigHClos)); s0) T ->
           tin[@Fin1] ≃(Retract_inl Alphabets.sigHeap (Retract_id (sigList Alphabets.sigHClos)); s1) V ->
           tin[@Fin2] ≃(Retract_inr (sigList Alphabets.sigHClos) (Retract_id Alphabets.sigHeap); s2) H ->
           (forall i : Fin.t 8, isRight_size tin[@FinR 3 i] sr[@i]) ->
           exists (T' V' : list LM_heap_def.HClos) (H' : LM_heap_def.Heap) (k : nat),
             let size := HaltingProblem.Loop_size T V H k in
             LM_heap_def.steps_k k (T, V, H) (T', V', H') /\
             LM_heap_def.halt_state (T', V', H') /\
             match T' with
             | [] =>
               tout[@Fin0] ≃(Retract_inl Alphabets.sigHeap (Retract_id (sigList Alphabets.sigHClos)); size[@Fin0] s0) [] /\
               tout[@Fin1] ≃(Retract_inl Alphabets.sigHeap (Retract_id (sigList Alphabets.sigHClos)); size[@Fin1] s1) V' /\
               tout[@Fin2] ≃(Retract_inr (sigList Alphabets.sigHClos) (Retract_id Alphabets.sigHeap); size[@Fin2] s2) H' /\
               (forall i : Fin.t 8, isRight_size tout[@FinR 3 i] (size[@FinR 3 i] sr[@i]))
             | _ :: _ => True
             end)
      : pRel (HaltingProblem.sigStep) ^+ unit 11
        *)
    
    Definition Rel : pRel (sig ^+) bool 11 :=
      fun tin '(y,tout) =>
        forall (P:Pro),
        tin[@Fin1] ≃(retr__pro) P ->
        (forall i : Fin.t 9, isRight tin[@FinR 2 i])
        -> match y with
            false => ~ exists (bs:list bool), tin[@Fin0] ≃ bs
          | true => exists (bs : list bool),
                   tin[@Fin0] ≃ bs
                   /\ exists sigma' k, ARS.evaluatesIn LM_heap_def.step k (initLMGen P (compile (Computable.enc (rev bs)))) sigma'
          end.
(* initLMGen = n s c : list Tok => ([(0, s ++ c ++ [appT])], [], []) *)
    Import M_Boollist_to_Enc ListTM Alphabets StepTM.

    Definition M : pTM sig ^+ bool 11 :=
      If (LiftTapes (CheckTapeContains.M (CheckEncodeList.M (I:=_))) [|Fin0|])
         (Return (F:=FinType (EqType unit)) (LiftTapes (BoollistToEnc.M (sig:=sig) (retr__Pro := retr__pro) (retr__nat := retr__nat)) [|Fin0;Fin2;Fin3;Fin4 |];; (* 0:right, 2:compile (enc (rev b)), 3,4:right*)
                  LiftTapes (ChangeAlphabet (WriteValue (encode [appT])) retr__pro) [| Fin3|];; (*3:[appT]*)
                  LiftTapes (ChangeAlphabet (App' _) retr__pro) [|Fin2;Fin3|];; (*3:compile (rev b)++[appT]*)         
                  LiftTapes (ChangeAlphabet (App' _) retr__pro) [|Fin1;Fin3|];; (*3:P++compile (rev b)++[appT]*)
                  LiftTapes (ChangeAlphabet (WriteValue (encode (@nil (LM_heap_def.HClos)))) retr__listHClos) [| Fin0|];; (*0:[]*)
                  LiftTapes (ChangeAlphabet (WriteValue (encode 0)) (StepTM.retr_nat_step_clos_ad retr__listHClos)) [| Fin5|];; (*5:0*)
                  LiftTapes (StepTM.ConsClos retr__listHClos) [|Fin0;Fin5;Fin3 |];; (* 0: initLMGen, 5,3:right *)
                  LiftTapes (Reset _) [|Fin1|];;LiftTapes (Reset _) [|Fin2|];;(*1,2: right*)
(*1,2: empty*)
                  LiftTapes (ChangeAlphabet (WriteValue (encode (@nil (LM_heap_def.HClos)))) retr__listHClos) [| Fin1|];; (*1:[]*)
                  LiftTapes (ChangeAlphabet (WriteValue (encode (@nil (LM_heap_def.HEntr)))) retr__Heap) [| Fin2|];; (*2:[]*)
                  ChangeAlphabet HaltingProblem.Loop retr__LAM )
                 true)
         (Return Nop false)
    .
    
    (*MOVE*)
    Ltac fin_inst_all H :=
      match type of H with
        forall i : Fin.t 0 , _ => clear H
      | forall i : Fin.t (S ?n) , @?P i =>
        let tmp := fresh "_tmp" in
        let H':= fresh H in
        rename H into _tmp; 
        assert (H':= tmp Fin0);
        assert (H:= fun i => tmp (Fin.FS i));clear tmp;
        fin_inst_all H
      end.

    
    Definition Ter time: tRel sig^+ 11 :=
      (fun tin k =>
         exists (P:Pro) steps__LM,
           tin[@Fin1] ≃(retr__pro) P /\
           (forall i : Fin.t 9, isRight tin[@FinR 2 i])
           /\ (((~exists bs, tin[@Fin0] ≃ bs) /\ steps__LM = 0)
             \/
             exists (bs : list bool),
               tin[@Fin0] ≃ bs
               /\ exists sigma', ARS.evaluatesIn LM_heap_def.step steps__LM (initLMGen P (compile (Computable.enc (rev bs)))) sigma')
           /\ time (steps__LM,sizeOfmTapes tin) <= k).
    
    Definition _Terminates :
      { time : UpToC (fun '(steps,size) => steps+size  + 1)
               & projT1 M ↓ Ter time}.
    Proof.
      eexists_UpToC time.
      eapply TerminatesIn_monotone.
      { unfold M. TM_Correct.
        all: eauto 2 using App'_Terminates,App'_Realise,BoollistToEnc.Realises,ConsClos_Realise,ConsClos_Terminates,Loop_Terminates.
        all: try now (notypeclasses refine (@Reset_Terminates _ _ _ _ _);shelve).
        all: try now (notypeclasses refine (@Reset_Realise _ _ _ _ _);shelve).
        1:notypeclasses refine (CheckTapeContains.Realises _ _).
        3:notypeclasses refine (CheckTapeContains.Terminates _ _).
        4:apply CheckEncodeList.Terminates.
        1,3:apply CheckEncodeList.Realises;now destruct x. now apply list_encode_prefixInjective,DecodeBool.bool_encode_prefixInjective.
        apply BoollistToEnc.Terminates. 
      }
      intros tin k H. hnf in H. destruct H as (P&steps__LM&HP&Hrem&Hsteps&Hk).
      cbn -[plus mult]. infTer 5.
      1:erewrite length_tape_local_right,right_sizeOfTape; rewrite <- Hk.
      2:{ intros tout b [[[Hb1] Hb2] Hrem']. fin_inst_all Hrem. TMSimp.
          destruct Hb1 as [(bs&Hbs) | ]. 2: now apply Nat.le_0_l.
          assert (Hlebs : length bs <= sizeOfmTapes tin).
          { clear - Hbs. rewrite <- sizeOfmTapes_upperBound with (t:=tin[@Fin0]). 2:now eapply vect_nth_In.
           destruct Hbs as (rem&->). cbn.  rewrite encode_list_concat. repeat (autorewrite with list;cbn).
           Import MoreList.
           rewrite length_concat. rewrite map_map;cbn. rewrite sumn_map_c. nia. } 
          modpon Hb2;[]. infTer 3. 2:easy.
          {hnf. cbn. TMSimp. exists bs. repeat simple apply conj. easy. 1-3:try isRight_mono. 
           erewrite UpToC_le. rewrite Hlebs. reflexivity. }
          intros t1 _ (HP'&Hrem_1). specialize (HP' bs). TMSimp. modpon HP'.
          infTer 5. TMSimp_goal. intros t2 _ (Ht2&Ht2Rem). specialize (Ht2 [appT]). modpon Ht2.
          TMSimp.
          (** TODO: size of compile?*)
          infTer 5. 
          {hnf;cbn. eexists (compile (Computable.enc (rev bs))),[appT]. repeat simple apply conj. 1-2:simpl_surject;try contains_ext.
            assert (H':=proj2_sig (BaseCode.App'_steps_nice _) (compile (Computable.enc (rev bs)))).
              hnf in H'. rewrite H'. admit.
          }
          intros t3 _ (Ht3&Ht3Rem). specialize (Ht3 (compile (Computable.enc (rev bs))) [appT]). modpon Ht3;[].
          infTer 5. admit.
          intros t4 _ (Ht4&Ht4Rem). specialize (Ht4 P (compile (Computable.enc (rev bs)) ++ [appT])). TMSimp.
          modpon Ht4; [].
          infTer 5. intros t5 _ (Ht5&Ht5Rem). specialize Ht5 with (x:=[]). modpon Ht5;[].
          infTer 5. intros t6 _ (Ht6&Ht6Rem). specialize (Ht6 0). TMSimp. modpon Ht6;[].
          infTer 5. admit.
          intros t7 _ (Ht7&Ht7Rem). modpon Ht7 . TMSimp.
          (*

             rewrite sze admit. } reflexivity. etransitivity. exact H'.  H'. cbn.  } intros t2 _ (Ht2&Ht2Rem). TMSimp. modpon Ht2;[].
          unfold ConcatRepeat.Ter. cbn. 
          infTer 5. 1:{ repeat simple apply conj. 1,2,3:now contains_ext.  rewrite UpToC_le. reflexivity. }
          intros t3 _ (Ht3&Ht3Rem). TMSimp. modpon Ht3;[]. rewrite app_nil_r in Ht4. 
          infTer 5. now contains_ext. intros t4 _ (Htp4&Ht4Rem). TMSimp. modpon Htp4;[].
          infTer 5. intros t5 _ (Htp5&Ht5Rem). TMSimp. modpon Htp5;[].
          infTer 5. 1:{unfold App'_T. cbn. eexists _,_.  repeat simple apply conj. 1,2:simpl_surject;now contains_ext.
                       eassert (H':=proj2_sig (App'_steps_nice _) enc_bool_nil). hnf in H'. rewrite H'. reflexivity.
          }
          intros t6 _ Ht6. modpon Ht6;[]. TMSimp.
          infTer 4. now contains_ext.
          { eassert (H':=proj2_sig (Reset_steps_nice) _ _ _ enc_bool_nil). hnf in H'. erewrite H'. reflexivity. }
          intros t7 _ Htp7. modpon Htp7;[]. hnf. TMSimp. 
          do 2 eexists. repeat simple apply conj. 1,2:now contains_ext. now isRight_mono.
          rewrite UpToC_le. reflexivity.
      }
      - rewrite <- Hl. set (l:=length bs). [time]:intros l.  unfold time. reflexivity.
      -unfold time. solve [smpl_upToC_solve].
    Qed. *)
    Abort.
    (*)
    Definition Terminates := projT2 _Terminates.
    *)
    
    Definition Realises : M ⊨ Rel.
    Proof.
      unfold M. eapply Realise_monotone.
      { TM_Correct.
        1:{  notypeclasses refine (CheckTapeContains.Realises _ _).
             eapply CheckEncodeList.Realises. now destruct x.
             now eapply list_encode_prefixInjective,DecodeBool.bool_encode_prefixInjective. }
        now apply BoollistToEnc.Realises.
        all:try now simple apply App'_Realise.
        now apply ConsClos_Realise.
        all:try now (notypeclasses refine (@Reset_Realise _ _ _ _ _);shelve).
        now simple apply Loop_Realise.
      }
      intros tin (yout,tout) H. hnf in H|-*. cbn in H.
      intros P HP HRem.
      destruct H as [H|H].
      2:{destruct H as (?&H&->&_&->). destruct H as (([Hx]&Hx')&Hrem). inv Hx. easy. }
      destruct H as (t1&Hcond&H). destruct Hcond as (([Hx]&Hx')&Hrem).
      (*fin_inst_all HRem. cbn [FinR] in *.   *)  
      modpon Hx'. inv Hx'.
      inv Hx. destruct H0 as (bs&Hx). TMSimp. modpon H.
      eexists bs. split. contains_ext.
      specialize (H0 [appT]). modpon H0;[]. modpon H2;[].
      progress TMSimp. modpon H3;[].
      specialize (H4 []). modpon H4;[].
      specialize (H5 0);[]. specialize (HRem Fin3) as ?. modpon H5;[].
      specialize (H6 [] (P ++ (compile (Computable.enc (rev bs))) ++ [appT]) 0).
      modpon H6;[]. modpon H7;[]. modpon H8;[].
      specialize (H9 []). modpon H9;[].
      specialize (H10 []). modpon H10;[].
      specialize (H11 (fst (fst (initLMGen P (compile (Computable.enc (rev bs)))))) [] []).
      cbn in H11. rewrite !surjectTapes_nth in H11. revert H11. TMSimp_goal. intros H11.
      modpon H11. 1:{ instantiate (1:= [|_;_;_;_;_;_;_;_|]). intros i. specialize (HRem (Fin.FS i)).
                      rewrite surjectTapes_nth.
                      destruct_fin i;cbn. all:simpl_surject. all:TMSimp_goal. all:try isRight_mono.
      }
      destruct H11 as (T'&V'&H'&k&Hred&HHalt&_).
      exists (T',V',H'),k. split. exact Hred. exact HHalt.
    Qed.
    
  End sec.
End LMtoTM.
