From Undecidability.L Require Import Tactics.LTactics.
From Undecidability.L.Datatypes Require Import Lists LVector LSum LProd LFinType LNat.
From Undecidability.L.Complexity Require Import NP Synthetic Monotonic.
From Undecidability.L.Functions Require Import EqBool.
From Undecidability.L.TM Require Import TapeFuns CompCode.

From Undecidability.TM Require Import TM CodeTM.
From Undecidability.TM.Single Require Import EncodeTapes StepTM.

From Undecidability.TM Require M2MBounds.
From Undecidability Require Import TM.VectorPrelim.

Unset Printing Coercions.

(*Import EncodeTapes DecodeTapes Single.StepTM ProgrammingTools Combinators Decode.*)


(*From Undecidability Require Import MultiUnivTimeSpaceSimulation. *)

From Undecidability.L.Complexity Require Import TMGenNP_fixed_mTM M_multi2mono.


Section LMGenNP_to_TMGenNP_mTM.


  Context (sig:finType) (n:nat) `{R__sig : registered sig}  (M : mTM sig (S n)).
  Let M__mono := M__mono M.
  
  Local Arguments Canonical_Rel : simpl never. 
  Local Arguments loopM : clear implicits.
  Local Arguments loopM {_ _ } _ _ _.
  Import EqBool.
  
  Lemma TMGenNP_mTM_to_TMGenNP_singleTM :
    restrictBy (HaltsOrDiverges_fixed_mTM M) (TMGenNP_fixed_mTM M)
               ⪯p unrestrictedP (TMGenNP_fixed_singleTapeTM (projT1 M__mono)).
  Proof.
    subst M__mono.
    evar (f__steps : nat*nat*nat -> nat). evar (f__nice : nat*nat*nat -> nat).
    enough (Hf__nice : f__steps <=c f__nice).
    unfold TMGenNP_fixed_mTM. unfold TMGenNP_fixed_singleTapeTM. cbn.
    set (t__start:=fun (ts : tapes sig n) => inl START::concat (map (fun t => inr (sigList_cons)::map (fun s => inr (sigList_X s)) (encode_tape t)) (Vector.to_list ts))++[inr (sigList_cons)]).
    set (t__size := fun maxSize => 3 + if eqb 0 maxSize then 0 else 1 + maxSize).
    eapply reducesPolyMO_intro_restrictBy with
        (f:=fun '(ts,maxSize,steps) => (t__start ts
                                     ,t__size maxSize
                                     ,  c__leUpToC (H:=Hf__nice) * f__nice (steps,sizeOfmTapes ts,maxSize)+ 3)).
    2:{ unfold execTM.
        intros [[v maxSize] steps]. unfold HaltsOrDiverges_fixed_mTM. intros H_HaltOrDiv.
        split. easy. split.
        -intros (t1&Ht1&s__end&Hs__end).
         eexists (map (fun c => inr (sigList_X c)) (encode_tape t1) ++ [inr sigList_nil;inl STOP]). 
         split. 1:{ cbn - [plus]. autorewrite with list. rewrite sizeOfTape_encodeTape. cbn - [Nat.eqb].
                    destruct (Nat.eqb_spec 0 (sizeOfTape t1));
                      destruct (eqb_spec 0 (maxSize)). all:try nia.
         }
         edestruct Terminates__mono as (?&?).
         2:{ eexists. cbn. unfold execTM. rewrite H. easy. }
         cbn. set (tin:=midtape _ _ _).
         eexists (select (putFirstAtEnd n) (t1:::v)), _.
         assert (Ht1v:contains_tapes tin (select (putFirstAtEnd n) (t1 ::: v))). 
         { hnf. subst tin. f_equal. unfold encode_tapes.
           rewrite encode_list_concat.
           autorewrite with list. cbn. rewrite !concat_map,!map_map.
           rewrite vector_to_list_correct,putFirstAtEnd_to_list.
           autorewrite with list. cbn. repeat setoid_rewrite map_map.
           rewrite concat_app;cbn. autorewrite with list. easy.
         } split. easy.
         split. 2:easy. hnf.
         (do 2 eexists). split.
         +intros ? ?. cbn in H. replace v0 with ((select (putFirstAtEnd n) (t1 ::: v))) in * by now eapply contains_tapes_inj. clear v0 H.
          split. 1: {hnf. rewrite putEnd_invL. eauto. }
          assert (H':=proj2_sig M2MBounds.Loop_steps_nice). hnf in H'.
          unfold PrettyBounds.dominatedWith in H'.
          rewrite H'. rewrite vector_to_list_correct, putFirstAtEnd_to_list.
          rewrite BaseCode.encodeList_size_app,size_list, to_list_length.
          unfold size. cbn - [mult plus]. 
          autorewrite with list. cbn [length]. rewrite sizeOfTape_encodeTape_le.
          erewrite sumn_map_le_pointwise with (f2:=fun x => _).
          2:{ intros. rewrite sizeOfTape_encodeTape_le. rewrite sizeOfmTapes_upperBound. 2:now eapply tolist_In. reflexivity. }
          rewrite !sumn_map_c,to_list_length.
          unshelve erewrite ( _ : (n * (2 + sizeOfmTapes v) + n + 1 + S (2 + sizeOfTape t1 + 1) + S n * steps)
                                  <= ((steps + sizeOfmTapes v + 5)* S n + sizeOfTape t1)). nia.
          reflexivity. 
         +cbn - [mult plus]. autorewrite with list; cbn - [plus mult].
          rewrite length_concat,map_map;cbn - [plus mult];setoid_rewrite map_length.
          rewrite sizeOfTape_encodeTape_le,Ht1.
          rewrite sumn_le_bound.
          2:{ intros ? (?&<-&?)%in_map_iff.
              rewrite sizeOfTape_encodeTape_le, sizeOfmTapes_upperBound. 2:now apply tolist_In. reflexivity. }
          rewrite map_length. rewrite to_list_length.
          replace (1 + (2 + maxSize + 2)) with (maxSize + 5) by lia.
          setoid_rewrite <- correct__leUpToC.
          [f__steps]:refine (fun '(steps, sizeOfmTapes, maxSize) =>  _).
          set (sizeOfmTapes _). unfold f__steps. reflexivity.
        -intros (cert&Hsize&f'&Hf'). destruct @loopM as [f| ] eqn:Hf. all:cbn -[plus mult t__start] in *. 2:now inv Hf'. clear Hf' f'.
         apply Realises__mono in Hf as (v0&v1&Hv0&Hv1&H__mono). cbn in Hv0.
         hnf in H__mono;cbn in H__mono. unfold LiftTapes in H__mono;cbn in H__mono.
         destruct H__mono as (outc&k&Hout&<-&_).
         hnf in Hv0. revert Hv0. intros [= Htl].
         unfold encode_tapes in Htl;rewrite encode_list_concat in Htl.
         rewrite map_app,concat_map,map_map,vector_to_list_correct in Htl. cbn in Htl. 
         setoid_rewrite map_map in Htl. rewrite <- !app_assoc in Htl. cbn in Htl.
         assert (H':=Htl). eapply concat_eq_inv_borderL with (isBorder := fun c => c = inr sigList_cons) in H'. rewrite map_length,to_list_length in H'.
         5:easy. 4:now cbn;intuition subst.
         2,3:intros _ (x&<-&Hinx)%in_map_iff. 2,3:eexists _,_;split;[reflexivity | ].
         2,3:now split;[easy | intros ? (y&<-&Hiny)%in_map_iff;easy].
         destruct H' as [Hinit Hlast]. rewrite <- MCList.map_skipn in Hlast.
         destruct (split_vector v0 n) as (v'&vlst) eqn:Hsplit.
         unshelve eassert (H':=split_vector_correct _ _). 6:rewrite Hsplit in H'. clear. abstract nia. 
         cbn [fst snd] in H'.  apply (f_equal (@vector_to_list _ _ )) in H'. rewrite vector_to_list_cast in H'. clear Hsplit.
         rewrite vector_app_to_list in H'.  
         revert v' vlst H'. replace (Init.Nat.min n (S n)) with n by nia. replace (S n - n) with 1 by nia.
         intros v' vlst eq. destruct (destruct_vector1 vlst) as (ts&->). cbn in eq.
         rewrite !vector_to_list_correct in eq.
         rewrite <- eq in Hlast,Hinit.
         replace v' with v in *.
         2:{ eapply VectorSpec.eq_nth_iff. intros i ? <-.
             unshelve eassert (Htmp:=Hinit (proj1_sig (Fin.to_nat i)) _). now destruct Fin.to_nat.
             destruct (Fin.to_nat i) eqn:Hi.
             rewrite <- !vector_to_list_correct,map_app,!vector_to_list_map,!vector_to_list_correct in Htmp. 
             rewrite nth_error_app1 in Htmp. 2:now rewrite to_list_length.
             cbn in Htmp. rewrite !vector_nth_error_nat in Htmp.
             destruct lt_dec. 2:easy. 
             rewrite !nth_map' in Htmp. revert Htmp. intros [= Htmp].
             apply map_injective in Htmp. 2:congruence. apply DecodeTape.tape_encode_injective in Htmp.
             rewrite <- (Fin.of_nat_to_nat_inv i).  rewrite Hi;cbn.
             erewrite Fin.of_nat_ext. apply Htmp.
         }
         clear Hinit v'.
         rewrite skipn_app in Hlast. 2:now rewrite to_list_length. cbn in Hlast.
         autorewrite with list in Hlast. cbn in Hlast. revert Hlast. intros [= ->].
         edestruct H_HaltOrDiv as (?&?&?&?).
         2:now eauto.
         assert (Hts__size : sizeOfTape ts <= maxSize).
         1:{ autorewrite with list in Hsize.  rewrite sizeOfTape_encodeTape in Hsize. unfold t__size in *.
             destruct (eqb_spec 0 maxSize);destruct sizeOfTape. all:cbn in Hsize;try nia. }
         clear Hsize. unfold initc in *. cbn in Hout.
         unshelve eassert (Htmp := LiftTapes_lift _ _). 11:{ now rewrite Hout. } now apply putEndAtFirst_dupfree.
         cbn in Htmp. unfold selectConf in Htmp. cbn in Htmp.

         erewrite putEndAtFirst_to_list in Htmp. 2:exact eq. eassumption.
    }
    2:{
      
      unfold f__steps.
      enough ((fun _ => 1) <=c f__nice).
      smpl_upToC.
      3:{ [f__nice]: exact (fun '(x,y,z) => (fun s => s*s*S x) (S x + y + z)).
          subst f__nice.
          set (c:= 5*(S n) + 1).
          exists (c * c).
          intros [[x y] z].
          set (s:=S x+y+z).  
          unshelve erewrite (_ : (x + y + 5) * S n + z <= c*s). 1:{ unfold s,c. nia. }
          nia.
      }
      all:unfold f__nice. all:smpl_upToC_solve.
    }

    assert (polyTimeComputable f__nice).
    { 
      evar (time : nat -> nat). [time]:intros n0.
      eexists (fun x => time x).
      { unfold f__nice. Import Nat. extract. solverec.
        set (n0:=(L.size (enc (a0, b0, b)))).
        assert (a0+b0+b+1 <= n0). 1:{ unfold n0. rewrite !size_prod. cbn [fst snd]. rewrite !size_nat_enc. 
          unfold c__natsizeS, c__natsizeO; nia. }
        unfold add_time, mult_time. 
        unshelve erewrite (_ : a0 <= n0). nia. unshelve erewrite (_ : b0 <= n0). nia. unshelve erewrite (_ : b <= n0). nia.
        unfold time. reflexivity. }
      1,2:unfold time;smpl_inO.
      { evar (f__size : nat -> nat). [f__size]:intros n0. exists f__size.
        { intros [[a0 b0] b]. unfold f__nice.
          set (n0:=(L.size (enc (a0, b0, b)))).
          assert (a0+b0+b+1 <= n0). 1:{ unfold n0. rewrite !size_prod. cbn [fst snd]. rewrite !size_nat_enc. 
            unfold c__natsizeS, c__natsizeO; nia. }
          rewrite size_nat_enc. 
          unshelve erewrite (_ : a0 <= n0). nia. unshelve erewrite (_ : b0 <= n0). nia. unshelve erewrite (_ : b <= n0). nia.
          change S with (plus 1).
          unfold f__size;reflexivity.
        }
        all:unfold f__size;smpl_inO.
      }
    }
    clearbody f__nice.

    assert (polyTimeComputable t__size).
    { 
      evar (c0 : nat).
      eexists (fun _ => c0).
      { unfold t__size. Import Init.Nat. Import EqBool LNat Equality. Import Equality. Import EqBool. set (WorkAround := Nat.eqb).
        extract. unfold WorkAround. solverec. all:rewrite eqbTime_le_l.
        all:set (c:=L.size (enc 0)). all:cbv in c;subst c. all:subst c0. 2:easy. nia. }
      1,2:smpl_inO.
      { evar (f__size : nat -> nat). [f__size]:intros n0. exists f__size.
        { intros x. unfold t__size.
          set (n0:=(L.size (enc x))).
          assert (Hx:x<=n0) by apply size_nat_enc_r.
          rewrite size_nat_enc. destruct _. 2:rewrite Hx;unfold f__size;reflexivity. unfold f__size. nia.
        }
        
        all:unfold f__size;smpl_inO.
      }
    }clearbody t__size.

    assert (polyTimeComputable t__start).
    {
      set (f:=fun s : sigTape sig => inr (sigList_X s)) in t__start.
      assert ( {f__c:UpToC (fun _ => 1) & computableTime' f (fun _ _ => (f__c tt,tt))}) as [t__f comp__f].
      {  evar (c:nat). exists_UpToC (fun _ => c). unfold f. clear_all. extract. solverec. [c]:exact 3. now unfold c. subst c. smpl_upToC_solve. }

      set (g:= (fun t : tape sig => inr sigList_cons :: map f (encode_tape t))) in t__start.
      assert ( {t__g:UpToC (fun t=> sizeOfTape t + 1) & computableTime' g (fun t _ => (t__g t,tt))}) as [t__g comp__g].
      {  evar (t__c: tape sig -> nat). [t__c]:intro. exists_UpToC t__c. unfold g.
         extract. solverec.
         rewrite map_time_const,sizeOfTape_encodeTape_le. all:unfold t__c. reflexivity. smpl_upToC_solve.
      } 
      
      evar (time : nat -> nat). [time]:intros n0.
      eexists (fun x => time x).
      { unfold t__start. Import Datatypes. set (WorkAround:=Vector.to_list). extract. solverec. rewrite (UpToC_le _).
        rewrite (correct__leUpToC (mapTime_upTo _)). 
        rewrite length_concat,map_map. subst g. cbn -[plus mult]. setoid_rewrite map_length. rewrite to_list_length.
        erewrite sumn_map_le_pointwise  with (f2:=fun _ => _).
        2:{ intros;rewrite (UpToC_le t__g),sizeOfmTapes_upperBound;try reflexivity;now apply tolist_In. }
        erewrite sumn_map_le_pointwise with (f1:=fun x1 : tape sig => S (| encode_tape x1 |)) (f2:=fun _ => _).
        2:{ intros. setoid_rewrite sizeOfTape_encodeTape_le at 1. rewrite sizeOfmTapes_upperBound at 1. 2:now apply tolist_In.
            reflexivity. }
        rewrite sumn_map_c,to_list_length.
        rewrite sumn_map_c,to_list_length.
        rewrite TMEncoding.sizeOfmTapes_by_size. set (L.size _).
        unfold time. reflexivity.
      }
      1,2:now unfold time;change S with (plus 1);smpl_inO.
      { evar (f__size : nat -> nat). [f__size]:intros n0. exists f__size.
        { intros x. unfold t__start.
          rewrite size_list_cons. subst g f.
          rewrite Lists.size_list. rewrite map_app,concat_map,map_map. cbn. setoid_rewrite map_map. rewrite sumn_app.
          assert (H' : forall l, sumn (concat l) = sumn (map sumn l)). 1:{induction l;cbn;now autorewrite with list. }
          rewrite H',map_map. cbn. set (tmp:=L.size (enc (inr sigList_cons)));cbv in tmp;subst tmp.
          setoid_rewrite size_sum. rewrite size_boundary. setoid_rewrite size_sigList.
          repeat setoid_rewrite <- plus_assoc.  ring_simplify. ring_simplify (7 + (4 + 5)).
          repeat setoid_rewrite sumn_map_add. repeat setoid_rewrite sumn_map_c. setoid_rewrite sumn_map_mult_c_r.
          setoid_rewrite sumn_map_le_pointwise with (f2:=fun x => _)at 2 3 4.
          2,3,4: (setoid_rewrite sizeOfTape_encodeTape_le at 1;intros;rewrite sizeOfmTapes_upperBound at 1; [ | now apply tolist_In]; reflexivity).
          rewrite sumn_map_c.
          setoid_rewrite sumn_map_le_pointwise with (f2:=fun x => _).
          2:{ intros. setoid_rewrite sumn_map_le_pointwise with (f2:=fun x => _).
              2:{ intros. apply (correct__leUpToC (size_finType_any_le_c (X:=finType_CS (sigTape sig)))). }
              rewrite sumn_map_c. rewrite sizeOfTape_encodeTape_le,  sizeOfmTapes_upperBound. 2:now apply tolist_In. reflexivity. }
          rewrite sumn_map_c. rewrite to_list_length. setoid_rewrite TMEncoding.sizeOfmTapes_by_size.
          set (n0:= L.size _). ring_simplify. unfold f__size. reflexivity.
        }
        all:unfold f__size;smpl_inO.
      }
    }
    clearbody f__steps t__start.
(*    assert (polyTimeComputable (@sizeOfmTapes sig n)) by apply ptc_sizeOfmtapes. *)

    evar (time : nat -> nat). [time]:intros n0.
      eexists (fun x => time x).
      {
        extract. solverec.
        remember (L.size (enc (a0, b0, b))) as n0 eqn:Hn0.
        rewrite !size_prod in Hn0. cbn [fst snd] in Hn0.
        erewrite (mono__polyTC _ (x':=n0)). 2:{ subst n0. repeat set (L.size _). nia. }
        setoid_rewrite (mono__polyTC _ (x':=n0)) at 2. 2:{ subst n0. repeat set (L.size _). nia. } 
        set (c0 := 5+c__natsizeO +c__natsizeS). 
        assert (H'' : L.size (enc (b, sizeOfmTapes a0, b0)) <= n0*c0).
        {  rewrite !size_prod. cbn [fst snd]. setoid_rewrite size_nat_enc at 2.
            rewrite TMEncoding.sizeOfmTapes_by_size. subst n0. repeat set (L.size _). nia. }
        setoid_rewrite (mono__polyTC _ (x':=n0*c0)) at 3. 2:exact H''. 
        specialize (bounds__rSP (f:=f__nice)) as H'. setoid_rewrite <- size_nat_enc_r in H'.
        unfold mult_time, add_time. 
        unshelve rewrite H'. now apply resSize__polyTC.
        setoid_rewrite mono__rSP. 2,3:exact H''.
        rewrite TMEncoding.sizeOfmTapes_by_size at 1. unshelve erewrite (_ : L.size (enc a0) <= n0). now (subst n0;clear;repeat set (L.size _);nia).
        unfold time. reflexivity.
      }
      1,2:now unfold time;smpl_inO;apply inOPoly_comp;smpl_inO.
      { evar (f__size : nat -> nat). [f__size]:intros n0. exists f__size.
        { intros [[a0 b0] b]. remember (L.size (enc (a0, b0, b))) as n0 eqn:Hn0.
          rewrite !size_prod in Hn0|-*. cbn [fst snd] in Hn0|-*. rewrite !size_nat_enc.
          assert (H'' : L.size (enc (b, sizeOfmTapes a0, b0)) <= n0*(5 + c__natsizeS + c__natsizeO)).
        {  rewrite !size_prod. cbn [fst snd]. setoid_rewrite size_nat_enc at 2.
           rewrite TMEncoding.sizeOfmTapes_by_size. subst n0. repeat set (L.size _). nia. }
        specialize (bounds__rSP (f:=f__nice)) as H'. setoid_rewrite <- size_nat_enc_r in H'.
        unshelve rewrite H'. now apply resSize__polyTC.
        setoid_rewrite mono__rSP. 2:exact H''.

        specialize (bounds__rSP (f:=t__size)) as Hsize. setoid_rewrite <- size_nat_enc_r in Hsize at 1.
        unshelve rewrite Hsize. now apply resSize__polyTC. 
        setoid_rewrite (mono__rSP _ (x':=n0)) at 1 . 2:nia.

        specialize (bounds__rSP (f:=t__start)) as Hstart.
        unshelve rewrite Hstart. now apply resSize__polyTC. 
        setoid_rewrite (mono__rSP _ (x':=n0)) at 1 . 2:subst;clear;repeat (set (L.size _));nia.
        unfold f__size. reflexivity.
        }
        1,2:unfold f__size;smpl_inO; apply inOPoly_comp;smpl_inO.

      }
    
        
  Qed.

  (* Print Assumptions LMGenNP_to_TMGenNP_mTM. *)

End LMGenNP_to_TMGenNP_mTM.
