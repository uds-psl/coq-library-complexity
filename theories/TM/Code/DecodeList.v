From Undecidability.TM Require Import TM ProgrammingTools Code.Decode Code.
Require Import FunInd Lia Ring Arith Program.Wf.


Lemma list_encode_prefixInjective sigX X (cX : codable sigX X):
  prefixInjective cX -> prefixInjective (Encode_list cX).
Proof.
  intros HcX. intros l. unfold Encode_list;cbn.
  induction l as [ | x l].
  {cbn. intros [];cbn. all:easy. }
  intros [ | x' l']. all:cbn. easy. intros ? ? [=H]. rewrite !app_assoc_reverse in H.
  specialize (map_retract_prefix_inj (H:=Retract_sigList_X (Retract_id sigX))) with (1:=H) as (t1'&t2'&H').
  apply HcX in H' as ->. apply app_inv_head in H. apply IHl in H. congruence.
Qed.

      
(*
Lemma TerminatesIn_Realises sig F n (M : pTM sig F n) Ter Rel:
  projT1 M ↓ Ter -> M ⊨ Rel
  -> forall tin, (exists k, Ter tin k) -> (exists ! y, Rel tin y ).
Proof.
  intros Terminates Realises. intros t (k&Tt).
  specialize (Terminates _ _ Tt) as (c&Hc).
  eexists. split. now eapply Realises;eassumption.
  intros c' Hc'. Realises
Qed. *)

From Undecidability.TM Require Import Code.DecodeBool.

Module CheckEncodeList.
  Section checkEncodeList.

    (* Context (sigX:finType) X (cX : codable sigX X). *)
    Local Notation sigX := bool (only parsing).
    Local Notation cX := Encode_bool (only parsing).
    Local Notation X := bool.

    Context (tau:finType) `{I : Retract (sigList sigX) tau}.

    Let I__X : Retract sigX tau := ComposeRetract I _. 
    Existing Instance I__X.
    Local Arguments ComposeRetract : simpl never.
    
    Local Remove Hints Retract_id : typeclass_instances.
    
    Let Rel : pRel tau bool 1 := ContainsEncoding.Rel (Encode_list cX) Retr_f.
    Let Rel__X :=  ContainsEncoding.Rel cX Retr_f.
    
    Definition R__step : pRel tau (option bool) 1 :=
      fun t '(y,t') =>
        match Option.bind Retr_g (current t[@Fin0]) with
          Some sigList_nil => t[@Fin0]=t'[@Fin0]
                             /\ y = Some true
        | Some sigList_cons =>
          exists t1 b1, Rel__X [|tape_move_right t[@Fin0]|] (b1,t1)
                   /\ t1[@Fin0] = tape_move_right t[@Fin0]
                   /\ t'[@Fin0] = (if b1 then tape_move_right t1[@Fin0] else t1[@Fin0])
                   /\ y = if b1 then None else Some false
        | _ => t[@Fin0]=t'[@Fin0] /\ y = Some false
        end.

    (*
    Context (M__X : pTM tau bool 1).
    Context (Realises__X : M__X ⊨ Rel__X).
     *)
    Local Notation M__X := (CheckEncodesBool.M (I:=I__X)) (only parsing).
    Local Notation Realises__X := (RealiseIn_Realise (@CheckEncodesBool.RealisesIn _ _)) (only parsing).
    
    Definition M__step : pTM tau (option bool) 1 :=
      Switch (Relabel ReadChar (Option.bind Retr_g))
             (fun c =>
                match c with
                | Some sigList_nil => (Return Nop (Some true))
                | Some sigList_cons => (Move Rmove;; If M__X (Move Rmove;;Return Nop None) (Return Nop (Some false)))
                | _ => Return Nop (Some false)
                end).
    
    Lemma Realises__step: M__step ⊨ R__step.
    Proof.
      unfold M__step,R__step.
      eapply Realise_monotone.
      { eapply Switch_Realise. now TM_Correct.
        introsSwitch c. destructBoth c as [ [] | ]. all:TM_Correct. apply Realises__X. }
      hnf. cbn. intros t (b,t') (?&?&(?&->&->&->)&H).
      destruct Option.bind as [ [] | ];cbn in H.
      1,2,4:now destruct H as (->&[? ->]).
      destruct H as (_&t1&Ht1&H). rewrite <- Ht1. destruct H as [H|H].
      2:{ destruct H as (?&(?&->)&->&[_ <-]). eexists [|t'[@Fin0]|],false. cbn. easy. }
      destruct H as (t2&(?&->)&?&_&Ht2&->&_&<-). eexists t2,true. hnf in t2. destruct_vector. cbn.  easy.
    Qed.
               
    Lemma Terminates__step T__X (Ter__X : projT1 M__X ↓ T__X):
      projT1 M__step ↓  (fun t k => exists k', T__X ([|tape_move_right t[@Fin0]|]) k' /\ k' + 7 <= k ).
    Proof.
      unfold M__step.
      eapply TerminatesIn_monotone.
      { eapply Switch_TerminatesIn. 1,2:now TM_Correct.
        introsSwitch c. destructBoth c as [ [] | ]. all:TM_Correct. all:try eassumption. eapply RealiseIn_Realise, CheckEncodesBool.RealisesIn. }
      intros ? ? (k'&H1&H2). infTer 5.
      2:{ intros t ? (?&->&->&<-).
          destruct (Option.bind Retr_g (current t[@Fin0])) as [ [] | ].  1,2,4:now apply Nat.le_0_l. 
          infTer 5. cbn -[plus]. intros t1 _ Ht1. infTer 2.
          1:{rewrite <- Ht1 in H1. hnf in t1. destruct_vector;eassumption. }
          infTer 2. intros t2 [] Ht2. 2:now apply Nat.le_0_l.
          infTer 4. intros. reflexivity.
      } ring_simplify. nia.
    Qed.

    Definition M := While M__step.

    Lemma Realises:
      (*prefixInjective cX -> *)
      (forall (x:X), encode x <> []) ->
      M ⊨ Rel.
    Proof.
      intros (*EpI_cX *) Hnnil. unfold Rel. 
      eapply Realise_monotone.
      { unfold M. TM_Correct_step. eapply Realises__step. }
      apply WhileInduction. all:unfold R__step,Rel;cbn.
      -intros t y tout. destruct Option.bind as [[] | ]eqn:Heq.
       3: intros (t1&b&Ht1&H);destruct b;[easy | ]; revert H.
       2:{ intros [Ht [= ->]]. all:hnf.
           destruct t[@Fin0] as [ | | | t__L c t__R]. 1-3:easy. cbn in Heq. eapply retract_g_inv in Heq as ->.
           split. 2:now eexists 0.
           eexists []. rewrite <- Ht.  cbn. easy.
       }
       2:{ intros (Ht&Ht2&[= ->]). all:hnf. destruct Ht1 as [Ht1 [k Ht1']]. rewrite Ht2 in *. clear tout Ht2.
           hnf. split. 2:{ eexists (S k). rewrite nat_rect_succ_r. cbn in *. congruence. }
           intros [] ?; cbn.
           all:intros Ht'. all:erewrite tape_local_current_cons in Heq;[ |apply Ht']. all:cbn in Heq.
           all:rewrite retract_g_adjoint in Heq. now inv Heq.
           cbn in *. erewrite tape_local_move_right in Ht1. 2:eassumption.  autorewrite with list in Ht1.
           eapply Ht1 with (x:=b). f_equal.
       }
       all:intros [Ht [= ->]]. all:hnf.
       all:split;[ | now eexists 0 ].  
       all:intros ? ? Ht'. all:destruct t[@Fin0]. all:cbn in Heq;inv Heq. cbn in *. all:destruct x;inv Ht'.
       all:retract_adjoint. all:easy. 
      -intros tin tmid tout yout Hin. unfold ContainsEncoding.Rel. 
       destruct tin[@Fin0] as [ | | | t__L c t__R ] eqn:Htin. all: cbn in Hin. 1-3:easy.
       destruct (Retr_g c) as [[] | ] eqn:Hc. 1,2,4:easy.
       apply retract_g_inv in Hc as ->. destruct Hin as (t1&[]&H__X&_&Hmid'&[=]).
       hnf in H__X. destruct H__X as [(x&Hx1&Hx2) [k__x Hk__x]]. (* cbn in Hx1.
       destruct t__R;revert Ht0;cbn. all:intros [= <- -> ->]. cbn in Hk__x.
       hnf in Hmid|-*. rewrite Hmid' in *. clear Hmid' tmid.
       (*)rewrite Hmid',Htin in *.  clear tin Htin tmid Hmid'. *) *)
       intros [hmid [k Hk]]. 
       split. 2:{ eexists _. clear hmid. cbn in *. rewrite nat_rect_succ_r. cbn. rewrite nat_rect_plus. rewrite <- Hk__x.
                  rewrite Hmid' in Hk.        rewrite <- nat_rect_succ_r in Hk. exact Hk.
       } clear k Hk.
       cbn in  *. rewrite tape_local_move_right' in Hx1. subst t__R.
       rewrite Hmid' in *. clear Hmid' tmid.
       destruct (cX x) eqn:HcX in Hx2,Hk__x;cbn in *. now edestruct Hnnil;eassumption.
       destruct t1[@Fin0] as [ | | | ? ? t__R];cbn in *. 1-3: now length_not_eq in Hx2. 
       destruct yout.
       2:{ intros [ | x' l'] ?;cbn. now intros [= [=]%retract_f_injective <-].
           intros [= Hx'].
           (*rewrite map_app,map_map,app_assoc_reverse in Hx'. *)
           eapply retract_f_injective in Hx' as [= ->].
           (*set (f' := map _) in Hx'. change f' with (map (Retr_f (Retract:=I__X))) in Hx'. clear f'. *)
           (*specialize map_retract_prefix_inj with (1:= Hx') as (?&?&Hx1'). *)
           (*apply EpI_cX in Hx1' as <-. apply app_inv_head in Hx'.*)
           destruct t__R.  now destruct l'.
           eapply hmid. cbn.  eassumption.
       }
       edestruct hmid as (xs&Hxs&->). rewrite tape_local_move_right' in Hxs. subst t__R. rewrite tape_left_move_right',Hx2.
       exists (x::xs). cbn in *. autorewrite with list. now cbn.
       (* rewrite rev_app_distr,map_app,map_app,!map_rev,!map_app,!map_map,!app_assoc_reverse,!map_rev,map_map.
       set (f' := map _ (cX x)). change f' with (map (Retr_f (Retract:=I__X)) (cX x)). clear f'.
       split. easy. rewrite HcX. cbn. now autorewrite with list. *)
    Qed.

    Lemma Terminates :
      projT1 M ↓ (fun tin k => length (tape_local tin[@Fin0])*8 + 8 <= k).
    Proof.
      cbn.
      eapply TerminatesIn_monotone.
      { unfold M. TM_Correct_step.
        2:eapply Terminates__step, RealiseIn_TerminatesIn.
        1:eapply Realises__step. now apply @CheckEncodesBool.RealisesIn. }
      eapply WhileCoInduction.
      intros tin k Hk. 
      infTer 4.
      intros [] tmid. now intros; nia.
      cbn [R__step].  destruct Option.bind as [ [] | ] eqn:Hc. 1,2,4:intuition congruence.
      intros (?&[]&Hbool&Ht'&H'&[=]). hnf in x. destruct_vector. cbn in Ht'. subst h. cbn - [plus] in *. 
      destruct (tin[@Fin0]) as [ | | | ? ? t__R]. 1-3:easy. cbn - [plus] in *. 
      destruct Hbool as [(x&Hx1&Hx2) _]. cbn in Hx1,Hx2.
      rewrite tape_local_move_right' in Hx1. rewrite tape_right_move_right' in Hx1. destruct t__R. easy.
      cbn -[plus]in *. inv Hx2. inv Hx1.
      eapply retract_g_inv in Hc as ->.
      rewrite H'. rewrite tape_local_move_right'.
      eexists. split. reflexivity. nia.
    Qed.

    
    (*
    Context c__X (Terminates__X : projT1 M__X ↓ (ContainsEncoding.Ter cX Retr_f c__X)).

    
    Variable c':nat.
    (* This sems hard as the run-time depends on the precise values. *)
    Lemma Terminates :
      projT1 M ↓ ContainsEncoding.Ter (Encode_list cX) Retr_f c'.
    Proof. (*
      unfold M.
      eapply TerminatesIn_monotone.
      { TM_Correct_step. now apply Realises__step. apply Terminates__step. eassumption. }
      apply WhileCoInduction.
      intros tin k Ter__X.
      assert (exists y, R__step tin y /\ forall y', R__step tin (None,y') -> y = (None,y')).
      { destruct Ter__X as (k__X&?&?&?). edestruct Terminates__step. eassumption.  unfold ContainsEncoding.Ter. 
        2:{eexists. split. eapply Realises__step. eassumption.
           unfold R__step. intros ?. destruct Option.bind as [[] | ] eqn:eqc.  1,2,4:intuition congruence.
           intros (?&[]&RX&?&?). 2:congruence. unfold Rel__X in RX.
           eapply ContainsEncoding.functional_true in RX. 2-3:admit.
        intros ? H'. eapply Realises__step in H. unfold R__step in *. }
      (l&Htin&Hl&Hk).
      -destruct (Encode_list _ x) eqn:eqxs. now destruct xs.
       unfold ContainsEncoding.Ter. cbn - [R__step] in *. 
       erewrite tape_local_move_right. 2:eassumption.  
      do 2 eexists.
      -eexists. split. 2:easy. applt cbn.
      eexists. eapply Realises__step. eapply Switch_TerminatesIn. 1,2:now TM_Correct.
        introsSwitch c. destructBoth c as [ [] | ]. all:TM_Correct. all:eassumption. }
      intros ? ? HT. infTer 5.
      2:{ intros t ? (?&->&->&<-).
          destructBoth (Option.bind Retr_g (current t[@Fin0])) eqn. as [ | ].
            infTer 5.  unfold CheckEncodesTape.Ter. intros ? _ Htout. rewrite !Htout. infTer 4.
            intros ? ? ?. destruct b.
            -infTer 5. intros ? ? ->.
             rewrite !Ht. cbn in *. fold n0.  destruct H as [_ (k&H)].
             rewrite H. rewrite iter_transitive with (g:=fun x => | right x |) (R:=le). 2:eauto. 2:apply Ht.
             rewrite Htout,Ht. fold n0. reflexivity.
            -nia.
            -nia.
             intros ? ? ?. nia. *)
    Abort.
*)
  End checkEncodeList.
End CheckEncodeList.

