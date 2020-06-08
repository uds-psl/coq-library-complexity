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

    Lemma Terminates R' (HR' : M' ⊨ R') T' (HT' : projT1 M' ↓ T'):
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
Lemma initValue_sizeOfTape (sig sigX X : Type) (cX : codable sigX X) (I : Retract sigX sig) (x : X):
  sizeOfTape (initValue cX I x) = size x + 2.
Proof.
  cbn. autorewrite with list. cbn. now unfold size.
Qed.


Lemma initRight_sizeOfTape sig :
  sizeOfTape (initRight sig) = 1.
Proof.
  cbn. nia.
Qed.

Module M.
  Section M.
    Arguments LMtoTM.M : clear implicits.
    Definition sig := (finType_CS (HaltingProblem.sigStep + sigList bool)).

    Definition sig__reg : registered sig := LFinType.registered_finType.

    Definition Retr1 : Retract _ sig := (Retract_inl _ (Retract_id _)).
    Definition Retr2 : Retract _ sig := (Retract_inr _ (Retract_id _)).

    Let n := 11.
    Definition M : pTM _ _ n := TrueOrDiverge.M (LMtoTM.M sig Retr1 Retr2).
    Definition ts__start : Pro -> tapes (sig^+) (n-1) :=
      (fun P => CodeTM.initValue _ (@LMtoTM.retr__pro _ Retr1) P ::: Vector.const (CodeTM.initRight _) (n-2)).

    Definition Rel : pRel (sig ^+) unit 11 :=
      fun tin _ =>
        forall P t__cert, tin = t__cert:::ts__start P
                   -> exists bs : list bool,
            t__cert ≃(Retr2) bs /\
            (exists (sigma' : LM_heap_def.state) (k : nat), evaluatesIn LM_heap_def.step k (initLMGen P (compile (enc (rev bs)))) sigma').


    Definition Realises :
      M ⊨
        (fun tin _ =>
           forall P t__cert, tin = t__cert:::ts__start P
                      -> exists bs : list bool,
               t__cert ≃(Retr2) bs /\
               (exists (sigma' : LM_heap_def.state) (k : nat), evaluatesIn LM_heap_def.step k (initLMGen P (compile (enc (rev bs)))) sigma')).
    Proof.
      unfold M. eapply Realise_monotone.
      1:now eapply TrueOrDiverge.Realises, LMtoTM.Realises.
      intros ? out H P t__cert ->. hnf in H|-*. specialize (H P).
      apply H.
      -apply CodeTM.initValue_contains.
      -intros ?. cbn - [Vector.const]. rewrite Vector.const_nth. now apply CodeTM.initRight_isRight.
    Qed.

    Definition time := @f__UpToC _ _ (projT1 (@LMtoTM._Terminates sig Retr1 Retr2)).

    Definition Terminates :
      projT1 M ↓ (fun tin k => 0 < k /\
                            exists P k__LM t__cert (bs : list bool),
                              tin = t__cert ::: ts__start P
                              /\ t__cert ≃(Retr2) bs
                              /\ (exists sigma' : LM_heap_def.state, evaluatesIn LM_heap_def.step k__LM (initLMGen P (compile (enc (rev bs)))) sigma')
                              /\ time (k__LM, sizeOfmTapes tin) <= k-1).
    Proof.
      unfold M. eapply TerminatesIn_monotone.
      {eapply TrueOrDiverge.Terminates. now apply LMtoTM.Realises. apply LMtoTM.Terminates. }
      intros tin k (HkPos&P&k__LM&t__cert&bs&->&Ht__cert&HLM&Htime). unfold LMtoTM.Ter.
      split.
      2:{ split. easy. unfold LMtoTM.Rel. intros _ H. eapply (H P).
          -apply CodeTM.initValue_contains.
          -intros ?. cbn - [Vector.const]. rewrite Vector.const_nth. now apply CodeTM.initRight_isRight.
          -eauto.
      }
      exists P,k__LM.
      repeat simple apply conj.
      -apply CodeTM.initValue_contains.
      -intros ?. cbn - [Vector.const]. rewrite Vector.const_nth. now apply CodeTM.initRight_isRight.
      -right. exists bs;split. all:easy.
      -eassumption.
    Qed.
  End M.

    
  Lemma sizeStart t__cert P:
    sizeOfmTapes (t__cert ::: M.ts__start P)
    = max (sizeOfTape t__cert) (size P + 2).
  Proof.
    unfold sizeOfmTapes. rewrite Vector.fold_left_right_assoc_eq. 2:nia. cbn - [Vector.const initValue initRight].
    rewrite <- Vector.fold_left_right_assoc_eq.  2:nia.
    set (tmp:= VectorDef.const _ _). change (VectorDef.fold_left _ _ _) with (sizeOfmTapes tmp).
    rewrite initValue_sizeOfTape.
    replace (sizeOfmTapes tmp) with 1. nia.
    subst tmp. clear.
    unfold sizeOfmTapes. rewrite Vector.fold_left_right_assoc_eq. 2:nia.
    generalize 8 as x. induction x.
    -reflexivity.
    -cbn in *. now rewrite <- IHx.
  Qed.
    
    
End M.

(*move*)
Lemma size_rev X {_:registered X} (xs : list X): L.size (enc (rev xs)) = L.size (enc xs).
Proof.
  rewrite !size_list,map_rev,<- sumn_rev. easy.
Qed.


(*move*)
Lemma uniform_confluent_confluent (X : Type) (R : X -> X -> Prop):
  uniform_confluent R -> confluent R.
Proof.
  intros H x y y' Hy Hy'. apply ARS.star_pow in Hy as (?&Hy). apply ARS.star_pow in Hy' as (?&Hy').
  edestruct parametrized_confluence as (?&?&z&?&?&?&?&?).
  eassumption. exact Hy. exact Hy'. exists z. split;eapply pow_star. all:easy.
Qed.


Lemma LMGenNP_to_TMGenNP_mTM (_ : registered M.sig):
  restrictBy (LMHaltsOrDiverges (list bool)) (LMGenNP (list bool)) ⪯p (restrictBy (HaltsOrDiverges_fixed_mTM (projT1 M.M)) (TMGenNP_fixed_mTM (projT1 M.M))).
Proof.
  evar (f__size:nat -> nat).
  Import Datatypes.Lists Datatypes.LBool.
  enough (Hcert_f__size : forall maxSize (bs : list bool) sig R, size (enc bs) <= maxSize -> sizeOfTape (initValue (sig:=sig) _ R bs) <= f__size maxSize).

  
  evar (f__steps:nat * Pro * nat -> nat).
  enough (Hf__steps : forall steps P maxSize t__cert k__LM,
             sizeOfTape t__cert <= f__size maxSize
             -> k__LM <= steps ->
             M.time (k__LM, sizeOfmTapes (t__cert ::: M.ts__start P)) <= f__steps (steps,P,maxSize)).

  
  
  eapply @reducesPolyMO_intro_restrictBy with
      (f:=fun '(P,maxSize,steps) => (M.ts__start P,f__size maxSize,S (f__steps (steps,P,maxSize)))).
  2:intros [[P maxSize] steps] H; split.
  2:{ hnf in H|-*. destruct H as ((s&->&s__proc)&HsmallCert&Hk).
      intros t__cert' k res' HM.
      specialize (M.Realises HM) as H'. hnf in H'. specialize H' with (1:=eq_refl) as (bs'&Hbs'&(sigma'&k__LM'&HbsRed')).
      specialize HsmallCert with (1:=HbsRed') as (bs&res__LM&Hbs&HbsRed&Hter__LM). clear HM k res' t__cert' bs' Hbs' sigma' k__LM' HbsRed'.
      apply star_pow in HbsRed as (k__LM&HbsRed).
      assert (Hk__LM : k__LM <= steps).
      { eapply Hk. exact Hbs. split. all:eassumption. }
      edestruct M.Terminates as (conf'&eq).
      2:{ eexists (initValue _ _ (rev bs)),_. split. 2:eassumption. eapply Hcert_f__size. rewrite size_rev. easy. }
      split. now clear;Lia.nia.
      eexists _,_,_,(rev bs).
      repeat simple apply conj.
      1:now reflexivity.
      1:now apply initValue_contains.
      2:{
        unshelve erewrite (_ : forall x, S x - 1 = x). 1:now clear;nia.
        apply Hf__steps. 2:eassumption. eapply Hcert_f__size.  rewrite size_rev. easy.
      }
      rewrite rev_involutive. unfold evaluatesIn;eauto.
  }
  3:{ intros steps P maxSize t__cert k__LM Hsize Hk__LM.
      rewrite M.sizeStart.
      unfold M.time.
      rewrite UpToC_le.
      rewrite !Hk__LM. clear Hk__LM k__LM.
      rewrite !Hsize. clear Hsize t__cert.
      [f__steps]:refine (fun '(steps,P,maxSize) => _). unfold f__steps. reflexivity.
  }
  3:{ intros maxSize bs sig R Hsize. rewrite initValue_sizeOfTape. 
      
      specialize @correct__leUpToC with (l:=M_Boollist_to_Enc.BoollistToEnc.boollist_size) (x:=bs) as ->.
      rewrite <- size_list_enc_r in Hsize. rewrite Hsize. 
      [f__size]:refine (fun n => _). subst f__size;cbn beta. reflexivity.
  }

  2:{
    destruct H as ((s&->&s__proc)&HsmallCert&Hsmallk).
    unfold LMGenNP, TMGenNP_fixed_mTM.
    split.
    -intros (cert' & HcertSize' & sigma'' & k' &Hk' &HR').
     edestruct M.Terminates with (k:= S (f__steps (steps,compile s,maxSize))) as (tout&Hout).
     { split. easy. eexists _,_,_,(rev cert'). rewrite rev_involutive. repeat simple apply conj.
       1:reflexivity.
       2:eexists;exact HR'.
       1:now apply initValue_contains.
       { unshelve erewrite (_ : forall x, S x - 1 = x). 1:now clear;nia.
         apply Hf__steps. 2:eassumption.
         eapply Hcert_f__size. now rewrite size_rev.
       }
     }
     do 2 eexists.
     2:{
       eexists. eassumption. }
     eapply Hcert_f__size. now rewrite size_rev.
    -intros (t__cert&Hsize_t__cert&(res&Hres)).
     specialize (M.Realises Hres) as H'. hnf in H'. specialize H' with (1:=eq_refl) as (bs'&Hbs'&(sigma'&k__LM'&HbsRed')).
      specialize HsmallCert with (1:=HbsRed') as (bs&res__LM&Hbs&HbsRed&Hter__LM). clear Hres bs' Hbs' sigma' k__LM' HbsRed'.
      apply star_pow in HbsRed as (k__LM&HbsRed).
      assert (Hk__LM : k__LM <= steps).
      { eapply Hsmallk. exact Hbs. split. all:eassumption. }
      exists bs. repeat simple apply conj. 1:easy. unfold evaluatesIn; eauto 10.
  }
  {
    clear Hf__steps Hcert_f__size.
    enough (polyTimeComputable f__steps).
    enough (polyTimeComputable f__size).

    - admit. (*TODO: Lemmas for PolyTimeComputable, See CanEnumTerm.v*)
    - admit.
    - admit.
  }
Admitted.

Print Assumptions LMGenNP_to_TMGenNP_mTM.
