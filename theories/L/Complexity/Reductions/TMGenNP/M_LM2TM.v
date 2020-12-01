From Undecidability.TM Require TM_facts ProgrammingTools CaseList CaseBool.
From Complexity.TM Require Code.Decode Code.DecodeList.

From Undecidability.TM Require Import TM SizeBounds.

From Undecidability.L.Complexity  Require Import UpToCNary.
From Complexity.L.Complexity  Require Import LMGenNP.


From Undecidability.L.AbstractMachines Require Import FlatPro.Programs.
From Complexity.L.AbstractMachines Require Import FlatPro.Computable.Compile.
     
Unset Printing Coercions.

From Undecidability.TM.L Require Alphabets M_LHeapInterpreter.

From Coq Require Import Lia Ring Arith.

From Undecidability.TM.L Require Import Boollist_to_Enc.

From Complexity.L.AbstractMachines.TM_LHeapInterpreter Require SizeAnalysis LMBounds_Loop.

Set Default Proof Using "Type".

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
        
    Definition retr__pro : Retract Alphabets.sigPro sig := ComposeRetract retr__HClos _.

    Definition retr__nat : Retract sigNat sig:= ComposeRetract retr__pro _.
    
    Definition Rel : pRel (sig ^+) bool 11 :=
      fun tin '(y,tout) =>
        forall (P:Pro),
        tin[@Fin1] ≃(retr__pro) P ->
        (forall i : Fin.t 9, isVoid tin[@FinR 2 i])
        -> match y with
            false => ~ exists (bs:list bool), tin[@Fin0] ≃ bs
          | true => exists (bs : list bool),
                   tin[@Fin0] ≃ bs
                   /\ exists sigma' k, ARS.evaluatesIn LM_heap_def.step k (initLMGen P (compile (Extract.enc (rev bs)))) sigma'
          end.
(* initLMGen = n s c : list Tok => ([(0, s ++ c ++ [appT])], [], []) *)
    Import Boollist_to_Enc ListTM Alphabets StepTM.

    Definition M : pTM sig ^+ bool 11 :=
      If (CheckEncodesBoolList.M _ @ [|Fin0|])
         (Return (F:=FinType (EqType unit)) (LiftTapes (BoollistToEnc.M _ retr__pro) [|Fin0;Fin2;Fin3;Fin4 |];; (* 0:right, 2:compile (enc (rev b)), 3,4:right*)
                  LiftTapes (ChangeAlphabet (WriteValue ([appT])) retr__pro) [| Fin3|];; (*3:[appT]*)
                  LiftTapes (ChangeAlphabet (App' _ ) retr__pro) [|Fin2;Fin3|];; (*3:compile (rev b)++[appT]*)         
                  LiftTapes (ChangeAlphabet (App' _) retr__pro) [|Fin1;Fin3|];; (*3:P++compile (rev b)++[appT]*)
                  LiftTapes (ChangeAlphabet (WriteValue ((@nil (LM_heap_def.HClos)))) retr__listHClos) [| Fin0|];; (*0:[]*)
                  LiftTapes (ChangeAlphabet (WriteValue (0)) (StepTM.retr_nat_step_clos_ad retr__listHClos)) [| Fin5|];; (*5:0*)
                  LiftTapes (StepTM.ConsClos retr__listHClos) [|Fin0;Fin5;Fin3 |];; (* 0: initLMGen, 5,3:right *)
                  LiftTapes (Reset _) [|Fin1|];;
                  LiftTapes (Reset _) [|Fin2|];;(*1,2: right*)
(*1,2: empty*)
                  LiftTapes (ChangeAlphabet (WriteValue ((@nil (LM_heap_def.HClos)))) retr__listHClos) [| Fin1|];; (*1:[]*)
                  LiftTapes (ChangeAlphabet (WriteValue ((@nil (LM_heap_def.HEntr)))) retr__Heap) [| Fin2|];; (*2:[]*)
                  ChangeAlphabet M_LHeapInterpreter.Loop retr__LAM )
                 true)
         (Return Nop false).
 
    
    Definition Ter time: tRel sig^+ 11 :=
      (fun tin k =>
         exists (P:Pro) steps__LM,
           tin[@Fin1] ≃(retr__pro) P /\
           (forall i : Fin.t 9, isVoid tin[@FinR 2 i])
           /\ (((~exists (bs : list bool), tin[@Fin0] ≃ bs) /\ steps__LM = 0)
             \/
             exists (bs : list bool),
               tin[@Fin0] ≃ bs
               /\ exists sigma', ARS.evaluatesIn LM_heap_def.step steps__LM (initLMGen P (compile (Extract.enc (rev bs)))) sigma')
           /\ time (steps__LM,sizeOfmTapes tin) <= k).

    Import MoreList.

    Lemma size_compile_list_bool:
      (fun bs : list bool => Code.size (compile (Extract.enc (rev bs)))) <=c (fun bs => length bs + 1).
    Proof.
      (* From Undecidability.L.AbstractMachines.TM_LHeapInterpreter Require  *)
      Import TM_LHeapInterpreter.SizeAnalysis TM_LHeapInterpreter.LMBounds_Loop.
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

    
    Local Arguments sizeOfmTapes : simpl never.
    Definition _Terminates :
      { time : UpToC ((fun '(steps, size) => (steps + 1) * (steps + size + 1) ^3 ))
               & projT1 M ↓ Ter time}.
    Proof.
      eexists_UpToC time.
      eapply TerminatesIn_monotone.
      { unfold M. TM_Correct.
        all: eauto 2 using App'_Terminates,App'_Realise,BoollistToEnc.Realise,ConsClos_Realise,ConsClos_Terminates,Loop_Terminates.
        all: try now (notypeclasses refine (@Reset_Terminates _ _ _ _ _);shelve).
        all: try now (notypeclasses refine (@Reset_Realise _ _ _ _ _);shelve).
        1:notypeclasses refine (CheckTapeContains.Realise _ _).
        3:notypeclasses refine (CheckTapeContains.Terminates _ _).
        4:apply CheckEncodesBoolList.Terminates'.
        1,3:apply CheckEncodesBoolList.Realise';now destruct x.
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
          set (sizeM := sizeOfmTapes [|tin_0; tin_1; tin_2; tin_3; tin_4; tin_5; tin_6; tin_7; tin_8; tin_9; tin_10|]).
          assert (Hlebs : length bs <= sizeM).
          { clear - Hbs. unfold sizeM. rewrite <- sizeOfmTapes_upperBound with (t:=tin_0).
           2:now eapply vect_nth_In with (i:=Fin0).
           destruct Hbs as (rem&->). cbn.  rewrite encode_list_concat. repeat (autorewrite with list;cbn).
           rewrite length_concat. rewrite map_map;cbn. rewrite sumn_map_c. nia. } 
          modpon Hb2;[]. infTer 3. 2:easy.
          {hnf. cbn. TMSimp. exists bs. repeat simple apply conj. easy. 1-3:try isVoid_mono. 
           erewrite UpToC_le. rewrite Hlebs. reflexivity. }
          intros t1_ _ (HP'&Hrem_1). specialize (HP' bs). TMSimp. modpon HP'.
          infTer 5. TMSimp_goal. intros t2_ _ (Ht2&Ht2Rem). modpon Ht2.
          (*unfold tapes in tin,tout,t1 |-. destruct_vector. cbn [Vector.nth Vector.caseS] in *. all:subst. *)
          TMSimp.
          
          infTer 5.
          {hnf;cbn. eexists _ (*(compile (Extract.enc (rev bs)))*),[appT]. repeat simple apply conj. 1-2:now simpl_surject;try contains_ext.
           setoid_rewrite ((proj2_sig (BaseCode.App'_steps_nice _) _) : _ <= _).
           
           rewrite (correct__leUpToC size_compile_list_bool), Hlebs. reflexivity.
          }
          intros t3_ _ (Ht3&Ht3Rem). specialize (Ht3 (compile (Extract.enc (rev bs))) [appT]). modpon Ht3;[]. TMSimp.
          infTer 5.
          { hnf;cbn. eexists _, _. repeat simple apply conj. 1-2:now simpl_surject;try contains_ext.
            eassert (H':=proj2_sig (BaseCode.App'_steps_nice _) P).
            hnf in H'. rewrite H'. reflexivity. }
          intros t4_ _ (Ht4&Ht4Rem). specialize (Ht4 P (compile (Extract.enc (rev bs)) ++ [appT])). TMSimp.
          modpon Ht4; [].
          infTer 5. intros t5_ _ (Ht5&Ht5Rem). modpon Ht5;[].
          infTer 5. intros t6_ _ (Ht6&Ht6Rem). TMSimp. modpon Ht6;[].
          infTer 5.
          { hnf;cbn. eexists _,_,_. repeat simple apply conj. 1-3:now simpl_surject;try contains_ext.
            match goal with |- _ <= ?c' => set (c:=c') end.
            unfold CaseList.Constr_cons_steps, Reset_steps. ring_simplify.
            setoid_rewrite Encode_pair_hasSize. cbn - [plus mult].
            repeat setoid_rewrite @BaseCode.encodeList_size_app.
            unfold c.
            rewrite (correct__leUpToC size_compile_list_bool), Hlebs. reflexivity.             
          }
          intros t7_ _ (Ht7&Ht7Rem). modpon Ht7 . progress TMSimp.
          infTer 4. now contains_ext. reflexivity.
          intros t8_ _ (Ht8'&Ht8Rem). modpon Ht8'. TMSimp.
          (*move Hsteps at bottom. destruct Hsteps as [ [H' ->] | H' ].
          { edestruct move H' destruct H'. }*)
          infTer 3.
          { split. now contains_ext. unfold Reset_steps.
            rewrite (correct__leUpToC size_compile_list_bool), Hlebs.  reflexivity. }
          reflexivity. 
          intros t9_ _ (Ht9'&Ht9Rem). modpon Ht9'.
          infTer 4. intros t10 _ (Ht10&Ht10Rem). TMSimp.
          modpon Ht10.
          infTer 4. intros t11 _ (Ht11&Ht11Rem). specialize Ht11. modpon Ht11. TMSimp.
          hnf. eexists [(0,_)],[],[],_. repeat eapply conj. 
          -eexists. eassumption.
          -cbn. simpl_surject. TMSimp_goal. contains_ext. 
          -cbn. simpl_surject. TMSimp_goal. contains_ext. 
          -cbn. simpl_surject. TMSimp_goal. contains_ext.
          -intros i. cbn. destruct_fin i;cbn. all:simpl_surject. all:isVoid_mono.
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

      
    Definition Realise : M ⊨ Rel.
    Proof.
      unfold M. eapply Realise_monotone.
      { TM_Correct.
        1:{  notypeclasses refine (CheckTapeContains.Realise _ _).
             eapply CheckEncodesBoolList.Realise'. now destruct x.
             now eapply list_encode_prefixInjective,DecodeBool.bool_encode_prefixInjective. }
        now apply BoollistToEnc.Realise.
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
      inv Hx. destruct H0 as (bs&Hx). TMSimp. 
      do_n_times_fin 9 ltac:(fun i => let H := fresh "HRem" in specialize (HRem i) as H;cbn in H);clear HRem.
      modpon H0.
      eexists bs. split. contains_ext.
      modpon H2;[]. modpon H4;[].
      modpon H6;[].
      modpon H8;[].
      modpon H10;[].
      modpon H12;[]. modpon H14;[]. modpon H16;[].
      modpon H18;[].
      modpon H20;[].
      rename H11 into H11',H22 into H11.
      specialize (H11 (fst (fst (initLMGen P (compile (Extract.enc (rev bs)))))) [] []).
      cbn in H11. TMSimp. 
      modpon H11.
      1:{ instantiate (1:= [| _;_;_;_;_;_;_;_|]). 
          intros i. destruct_fin i;cbn;simpl_surject;eauto.
      }
      destruct H11 as (T'&V'&H'&k&Hred&HHalt&_).
      exists (T',V',H'),k. split. exact Hred. exact HHalt.
    Qed.
    
  End sec.
End LMtoTM.
