From Undecidability.L Require Import Tactics.LTactics.
From Undecidability.L.Datatypes Require Import Lists LVector.
From Undecidability.L.Complexity Require Import NP Synthetic Monotonic.
From Undecidability.TM Require Import TM.
From Undecidability.L.AbstractMachines Require Import FlatPro.Programs FlatPro.Computable.LPro.

From Undecidability.L.Complexity Require Import LMGenNP TMGenNP_fixed_mTM.

Require Undecidability.LAM.TM.HaltingProblem.
Module LAM := Undecidability.LAM.TM.HaltingProblem.

From Undecidability Require Import TMGenNP.M_LM2TM.

Check LMtoTM.M.

From Undecidability Require Import LSum.

From Undecidability Require Import CompCode. 

Import ProgrammingTools.

Module TrueOrDiverge.
  Import TM.TM ProgrammingTools CaseList CaseBool Code.Decode Code.DecodeList.

  Section sec.
  Variable (n:nat) (sig : finType) (M' : pTM sig bool n).

  Definition M := If M' Nop Diverge.

  Lemma Realises R' (H' : M' ⊨ R'):
    M ⊨ (fun tin out => R' tin (true,snd out)).
  Proof.
    eapply Realise_monotone.
    { eapply If_Realise. eassumption. now TM_Correct. now apply Diverge_Realise. }
    hnf. intros x [[] y]. intros [H|H].
    -cbn in H. destruct H as (?&?&<-). easy. 
    -exfalso. cbn in H. firstorder.
  Qed.

  Import TM.
  
  Lemma TerminatesIn R' (HR' : M' ⊨ R') T' (HT' : projT1 M' ↓ T'):
    projT1 M ↓ (fun tin k => T' tin (k-1) /\ 0 < k /\ forall tout, ~ R' tin (false,tout)).
  Proof.
    eapply TerminatesIn_monotone.
    { eapply If_TerminatesIn. 1,2:eassumption. now TM_Correct. now apply Canonical_TerminatesIn. }
    intros tin [] (HTtin&Hfalse). easy. 
    do 2 eexists;repeat simple apply conj. eassumption.
    2:{ intros ? ? ?. destruct b. reflexivity. now exfalso. }
    nia.
  Qed.
  End sec.
End TrueOrDiverge.


Arguments LMtoTM.M : clear implicits.


(*move*)
Lemma uniform_confluent_confluent (X : Type) (R : X -> X -> Prop):
  uniform_confluent R -> confluent R.
Proof.
  intros H x y y' Hy Hy'. apply ARS.star_pow in Hy as (?&Hy). apply ARS.star_pow in Hy' as (?&Hy'). 
  edestruct parametrized_confluence as (?&?&z&?&?&?&?&?).
  eassumption. exact Hy. exact Hy'. exists z. split;eapply pow_star. all:easy.
Qed. 
  
Lemma LMGenNP_to_TMGenNP_mTM :
  {sig : finType &
   {n:nat &
    {R__sig : registered sig &
     {M : mTM sig (S n) & 
          restrictBy (LMHaltsOrDiverges (list bool)) (LMGenNP (list bool)) ⪯p (restrictBy (HaltsOrDiverges_fixed_mTM M) (TMGenNP_fixed_mTM M))}}}}.
Proof.
  evar (sig : finType). evar (tau : finType). evar (n:nat).
  unshelve epose (_:mTM tau (S n)) as M.
  { unshelve notypeclasses refine (projT1 ( (*TrueOrDiverge.M*) (@LMtoTM.M sig _ _))).
    2:now notypeclasses refine (Retract_inl _ (Retract_id _)).
    now notypeclasses refine (Retract_inr _ (Retract_id _)).
  } cbn in M.
  unshelve eexists _,n,_,M.
  now apply LFinType.registered_finType.
  set (Retr1 := Retract_inr _ _) in M.
  set (Retr2 := Retract_inl _ _) in M.

  evar (R__Pro: Retract Alphabets.sigPro sig). unfold sig in tau. cbn in tau. 

  evar (ts__start:Pro -> tapes tau (S (n-1))).
  [ts__start]: refine (fun (P :Pro) => CodeTM.initValue _ R__Pro P ::: Vector.const (CodeTM.initRight _) (n-1)).
  
  evar (tmp2:Type). evar (f__steps:tmp2).
  evar (tmp3:Type). evar (f__size:tmp3).
  eapply reducesPolyMO_intro_restrictBy with
      (f:=fun '(P,maxSize,steps) => (ts__start P,f__size maxSize,f__steps steps P maxSize));subst tmp2;subst tmp3.
  2:{
    intros [[P maxSize] steps] H. split.
    { hnf in H|-*. destruct H as ((s&Hs&s__proc)&HsmallCert&Hk).
      intros t__cert Hsize k conf__res HM.
      
      apply LMtoTM.Realises in HM as HM__sound. hnf in HM__sound. specialize (HM__sound P).
      Tactic Notation "mp" hyp(L) "as" ident(H) :=
        lazymatch type of L with
          ?t -> _ => 
          assert (H:t);[ |
                         specialize (L H)]
        end.
      mp HM__sound as HMP.
      { cbn. unfold R__Pro. apply initValue_contains. }
      mp HM__sound as HMright.
      { intros. cbn - [Vector.const]. rewrite Vector.const_nth. apply initRight_isRight. }
      
      specialize LMtoTM.Terminates with (sig:=_) (retr__LAM:=Retr1) (retr__list:=Retr2) as HM__terminate.
      set (M' := projT1 _) in HM__terminate at 1; replace M' with M in *;[ | unfold M,M';reflexivity];clear M'.
      hnf in HM__terminate.

      specialize HM__terminate as (conf' & HM__terminate).
      2:{ erewrite loop_injective with (b:=conf__res). 3:exact HM__terminate. 2:eassumption.
          eassumption.
      }
      cbn -[ts__start] in HMP.
      hnf.
      exists P. 
      set (t__M := f__UpToC _) at 1.
      cut (forall steps__LM, steps__LM <= steps -> 
                      t__M (steps__LM, sizeOfmTapes (t__cert ::: ts__start P)) <= f__steps steps P maxSize).
      {
        intros Hmono.
        destruct (projT2 _) eqn:Heqcase in HM__sound.
        2:{ eexists 0. repeat simple apply conj.
            -exact HMP.
            -exact HMright.
            -left. split. 2:easy. eassumption.
            -apply Hmono. clear;nia. 
        }
        edestruct HM__sound as (bs&?&?&k0&?).
        cbn in H.
        specialize sizeOfTape_tape_contains_size with (1:=tape_contains_contains_size H) as Hsize_bs.
        set (tmp := sizeOfTape _) in Hsize,Hsize_bs. rewrite <- Hsize_bs in Hsize at 1. clear Hsize_bs tmp.

        { (*specialize HsmallCert with (1:=H0) as (cert'&sigma'&Hcert'size&(k'&Hcert'R)%(proj1 (@ARS.star_pow _ _ _ _))). *)
         eexists k0. repeat simple apply conj.
          -exact HMP.
          -exact HMright.
          -right. eauto.
          -apply Hmono.
           (*specialize HsmallCert with (1:=H0) as (cert'&sigma'&Hcert'size&Hcert'R).
           replace x with sigma' in *.
           2:{
             eapply ARS.unique_normal_forms with (R:= LM_heap_def.step).
             -eapply uniform_confluent_confluent,functional_uc, LM_heap_def.step_functional.
             -destruct H0 as (H0'&?). apply pow_star,star_ecl in H0'. apply star_ecl in Hcert'R. rewrite <- H0',<-Hcert'R.
           destruct (HsmallCert _ _ _H0) *)
           eapply Hk. 2:eassumption.
           Set Nested Proofs Allowed.
           (*move*)
           Lemma size_rev X {_:registered X} (xs : list X): L.size (enc (rev xs)) = L.size (enc xs).
           Proof.
             rewrite !size_list,map_rev,<- sumn_rev. easy.
           Qed.

           rewrite size_rev.
           
           (*move*)
           Lemma Lsize_list_bool_le:
             (fun (bs : list bool) => L.size (enc bs)) <=c (fun bs => length bs + 1).
           Admitted.
           Lemma length_le_TMsize_list_bool:
             (fun (bs : list bool) => length bs + 1) <=c size.
           Admitted.
           specialize @correct__leUpToC with (l:=Lsize_list_bool_le) (x:=bs) as ->.
           specialize @correct__leUpToC with (l:=length_le_TMsize_list_bool) (x:=bs) as ->.
           rewrite Hsize.
           rewrite <- mult_assoc_reverse.
           set (c:= c__leUpToC * c__leUpToC).
           enough (Hdiv:f__size maxSize <= maxSize / (c+1)).
           { unshelve erewrite (_ : c <= c +1) at 1. clear;nia.
             rewrite Hdiv,Nat.mul_div_le. 2:clear;nia. reflexivity.
           }
           [f__size]:refine (fun n => _). subst f__size;cbn beta. reflexivity.
        }
      }
      (* TODO: instantiate using monotonic property? *)
      Import String. instantiate (f__steps := TODO ("above, and abstract important properties")).
      admit. 
    }
    (* TODO: We might canc opy some reasoning from the first part down here*)
    (* TODO: do we need HsmallCert? *)
    destruct H as ((s&->&s__proc)&HsmallCert&Hk).
    unfold LMGenNP, TMGenNP_fixed_mTM.
    split.
    -intros (cert & HcertSize & sigma & k' &Hk' &HR'). admit.
     
    -admit. 
  }
  admit.
Admitted.

Print Assumptions LMGenNP_to_TMGenNP_mTM.
