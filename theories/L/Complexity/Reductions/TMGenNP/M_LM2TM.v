From Undecidability.L.Complexity Require Import NP.
From Undecidability.TM Require TM_facts ProgrammingTools CaseList CaseBool Code.Decode Code.DecodeList.
From Undecidability.TM Require Import TM SizeBounds.

From Undecidability.L.Complexity  Require Import UpToCNary.

From Undecidability.L.AbstractMachines Require Import FlatPro.Programs FlatPro.Computable.Compile.
     
Unset Printing Coercions.

From Undecidability.L.AbstractMachines.TM_LHeapInterpreter Require Alphabets.

From Coq Require Import Lia Ring Arith.

From Undecidability.L.Complexity  Require Import LMGenNP TMGenNP_fixed_mTM M_Boollist_to_Enc.

From Undecidability Require Import Code.ListTM_concat_repeat.

From Undecidability.L.AbstractMachines.TM_LHeapInterpreter Require M_LHeapInterpreter.

Import DecodeList Decode.
Module LMtoTM.
  Section sec.
    Import ProgrammingTools Combinators M_LHeapInterpreter.

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
                  ChangeAlphabet M_LHeapInterpreter.Loop retr__LAM )
                 true)
         (Return Nop false).
 
    
    Definition Ter time: tRel sig^+ 11 :=
      (fun tin k =>
         exists (P:Pro) steps__LM,
           tin[@Fin1] ≃(retr__pro) P /\
           (forall i : Fin.t 9, isRight tin[@FinR 2 i])
           /\ (((~exists (bs : list bool), tin[@Fin0] ≃ bs) /\ steps__LM = 0)
             \/
             exists (bs : list bool),
               tin[@Fin0] ≃ bs
               /\ exists sigma', ARS.evaluatesIn LM_heap_def.step steps__LM (initLMGen P (compile (Computable.enc (rev bs)))) sigma')
           /\ time (steps__LM,sizeOfmTapes tin) <= k).

    Import MoreList.

    Lemma size_compile_list_bool:
      (fun bs : list bool => Code.size (compile (Computable.enc (rev bs)))) <=c (fun bs => length bs + 1).
    Proof.
      From Undecidability.L.AbstractMachines.TM_LHeapInterpreter Require Import SizeAnalysis LMBounds_Loop.
      evar (c:nat). exists c. intros xs.
      rewrite size_le_sizeP. unfold sizeP;rewrite sizeP_size,Lists.size_list.
      rewrite map_rev,<-sumn_rev. rewrite MoreBase.sumn_le_bound.
      2:{ intros ? ([]&<-&?)%in_map_iff. all:cbv. reflexivity. nia. }
      rewrite map_length. ring_simplify. [c]:exact 54. unfold Lists.c__listsizeNil. nia.
    Qed.

    
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

    
 
    Definition _Terminates :
      { time : UpToC ((fun '(steps, size) => (steps + 1) * (steps + size + 1) ^3 ))
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
        1,3:apply CheckEncodeList.Realises;now destruct x.
        now apply list_encode_prefixInjective,DecodeBool.bool_encode_prefixInjective.
        apply BoollistToEnc.Terminates. 
      }
      intros tin k H. hnf in H. destruct H as (P&steps__LM&HP&Hrem&Hsteps&Hk).
      cbn -[plus mult]. infTer 5.
      1:erewrite length_tape_local_right,right_sizeOfTape; rewrite <- Hk.
      2:{ intros tout b [[[Hb1] Hb2] Hrem']. fin_inst_all Hrem. TMSimp.
          destruct Hb1 as [(bs&Hbs) | ]. 2: now apply Nat.le_0_l.
          destruct Hsteps as [ [[] _] | Hsteps].
          { eexists. contains_ext. }
          destruct Hsteps as (bs'&Hbs'&Hsteps).
          replace bs' with bs in *.
          2:{
            destruct Hbs as [? Hbs]. destruct Hbs' as [? Hbs']. rewrite Hbs' in Hbs. inv Hbs.
            rewrite !map_map in H1. eapply app_inv_tail, map_injective in H1.
            2:{ intros ? ? [= ]. now eapply retract_f_injective. }
            apply encode_list_injective in H1. easy. apply Encode_bool_injective.
          }
          clear bs' Hbs'.
          assert (Hlebs : length bs <= sizeOfmTapes tin).
          { clear - Hbs. rewrite <- sizeOfmTapes_upperBound with (t:=tin[@Fin0]). 2:now eapply vect_nth_In.
           destruct Hbs as (rem&->). cbn.  rewrite encode_list_concat. repeat (autorewrite with list;cbn).
           rewrite length_concat. rewrite map_map;cbn. rewrite sumn_map_c. nia. } 
          modpon Hb2;[]. infTer 3. 2:easy.
          {hnf. cbn. TMSimp. exists bs. repeat simple apply conj. easy. 1-3:try isRight_mono. 
           erewrite UpToC_le. rewrite Hlebs. reflexivity. }
          intros t1 _ (HP'&Hrem_1). specialize (HP' bs). TMSimp. modpon HP'.
          infTer 5. TMSimp_goal. intros t2 _ (Ht2&Ht2Rem). specialize (Ht2 [appT]). modpon Ht2.
          (*unfold tapes in tin,tout,t1 |-. destruct_vector. cbn [Vector.nth Vector.caseS] in *. all:subst. *)
          TMSimp.
          
          infTer 5.
          {hnf;cbn. eexists _ (*(compile (Computable.enc (rev bs)))*),[appT]. repeat simple apply conj. 1-2:now simpl_surject;try contains_ext.
           setoid_rewrite ((proj2_sig (BaseCode.App'_steps_nice _) _) : _ <= _).
           
           rewrite (correct__leUpToC size_compile_list_bool), Hlebs. reflexivity.
          }
          intros t3 _ (Ht3&Ht3Rem). specialize (Ht3 (compile (Computable.enc (rev bs))) [appT]). modpon Ht3;[]. TMSimp.
          infTer 5.
          { hnf;cbn. eexists _, _. repeat simple apply conj. 1-2:now simpl_surject;try contains_ext.
            eassert (H':=proj2_sig (BaseCode.App'_steps_nice _) P).
            hnf in H'. rewrite H'. reflexivity. }
          intros t4 _ (Ht4&Ht4Rem). specialize (Ht4 P (compile (Computable.enc (rev bs)) ++ [appT])). TMSimp.
          modpon Ht4; [].
          infTer 5. intros t5 _ (Ht5&Ht5Rem). specialize Ht5 with (x:=[]). modpon Ht5;[].
          infTer 5. intros t6 _ (Ht6&Ht6Rem). specialize (Ht6 0). TMSimp. modpon Ht6;[].
          infTer 5.
          { hnf;cbn. eexists _,_,_. repeat simple apply conj. 1-3:now simpl_surject;try contains_ext.
            match goal with |- _ <= ?c' => set (c:=c') end.
            unfold CaseList.Constr_cons_steps, Reset_steps. ring_simplify.
            setoid_rewrite Encode_pair_hasSize. cbn - [plus mult].
            repeat setoid_rewrite @BaseCode.encodeList_size_app.
            unfold c.
            rewrite (correct__leUpToC size_compile_list_bool), Hlebs. reflexivity.             
          }
          intros t7 _ (Ht7&Ht7Rem). modpon Ht7 . progress TMSimp.
          infTer 5. now contains_ext.
          intros t8 _ (Ht8'&Ht8Rem). modpon Ht8'. TMSimp.
          (*move Hsteps at bottom. destruct Hsteps as [ [H' ->] | H' ].
          { edestruct move H' destruct H'. }*)
          infTer 3.
          { split. now contains_ext. unfold Reset_steps.
            rewrite (correct__leUpToC size_compile_list_bool), Hlebs.  reflexivity. }
          reflexivity. 
          intros t9 _ (Ht9'&Ht9Rem). modpon Ht9'.
          infTer 4. intros t10 _ (Ht10&Ht10Rem). TMSimp.
          specialize (Ht10 []). modpon Ht10.
          infTer 4. intros t11 _ (Ht11&Ht11Rem). specialize (Ht11 []). modpon Ht11. TMSimp.
          hnf. eexists [(0,_)],[],[],_. repeat eapply conj. 
          -eexists. eassumption.
          -rewrite surjectTapes_nth. simpl_surject. TMSimp_goal. contains_ext. 
          -rewrite surjectTapes_nth. simpl_surject. TMSimp_goal. contains_ext. 
          -rewrite surjectTapes_nth. simpl_surject. TMSimp_goal. contains_ext.
          -intros i. rewrite surjectTapes_nth. simpl_surject. destruct_fin i;cbn. all:TMSimp_goal. all:isRight_mono.
          -unshelve erewrite (correct__leUpToC (Loop_steps_nice _) (_,_)). easy. 
           cbn [length]. unfold sizeP. rewrite !map_app,!sumn_app.
         
           rewrite (correct__leUpToC sizeT_compile_list_bool bs).
           set (c:= sumn (map sizeT [appT])). cbv in c. subst c.
           rewrite !Nat.add_assoc.  replace (0 + steps__LM + 1 + (sumn (map sizeT P))) with (steps__LM + sizeP P) by (unfold sizeP;lia).
           rewrite Hlebs. reflexivity.
      }
      ring_simplify.
      unfold Reset_steps.
      setoid_rewrite (sizeP_le_size P).
      repeat rewrite sizeOfTape_tape_contains_size with (1:=(tape_contains_contains_size HP)). 
      repeat rewrite sizeOfmTapes_upperBound with (tps:=tin). 2-3:now eapply vect_nth_In. 
      [time]:refine (fun '(steps__LM,sizeM) => _).
      set (sizeM := sizeOfmTapes _). unfold time. reflexivity.
      unfold time.
      smpl_upToC.
      1-15,18:cbn [Nat.pow];now smpl_upToC_solve.
      2:{ transitivity (fun '(steps, size) => (steps + size + 1) ^ 3).
          2:now smpl_upToC_solve.
          
      nary apply upToC_pow_le_compat_nary. 1-2:nia. smpl_upToC_solve.
      }

      nary apply upToC_mul_nary.
      2:nary apply  upToC_pow_le_compat_nary. 2,3:easy.
      all:try smpl_upToC_solve.
    Qed.

    Definition Terminates := projT2 _Terminates.

      
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
