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

Import LSum.

From Undecidability Require Import CompCode. 

Import ProgrammingTools.

Arguments LMtoTM.M : clear implicits.

Lemma LMGenNP_to_TMGenNP_mTM :
  {sig : finType &
   {n:nat &
    {R__sig : registered sig &
     {M : mTM sig (S n) & 
          restrictBy (LMHaltsOrDiverges (list bool)) (LMGenNP (list bool)) ⪯p (restrictBy (HaltsOrDiverges_fixed_mTM M) (TMGenNP_fixed_mTM M))}}}}.
Proof.
  evar (sig : finType). evar (tau : finType). evar (n:nat).
  unshelve epose (_:mTM tau (S n)) as M.
  { unshelve notypeclasses refine (projT1 (@LMtoTM.M sig _ _)).
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
      (f:=fun '(P,maxSize,steps) => (ts__start P,f__size maxSize,f__steps steps));subst tmp2;subst tmp3.
  2:{
    intros [[P maxSize] steps] H. split.
    { hnf in H|-*. destruct H as ((s&Hs&s__proc)&Hk).
      intros t__cert Hsize k conf__res HM.
      apply LMtoTM.Realises in HM as HM__sound. hnf in HM__sound. specialize (HM__sound P).
      TODO.

      (*TODO: HaltsOrDiverges_fixed_mTM must say that "if we do not hold in ''steps' step, we never hold." More explicitely, the problem was that loopM is monotonic. Alternatively, we could say "if we halt in k steps, we also hold in "steps" step", which is better *)
      
      (*TODO: "modus ponens" of the assumptions for HM__sound, as we need them later *)

      TODO.
      (* THEN: continue with proof, use combination *)
      
      ProgrammingTools.modpon HM__sound;[ | | ].
      { cbn. unfold R__Pro. eapply CodeTM.initValue_contains. }
      { intros. cbn - [Vector.const]. rewrite Vector.const_nth. apply initRight_isRight. }
      specialize LMtoTM.Terminates with (sig:=_) (retr__LAM:=Retr1) (retr__list:=Retr2) as HM__terminate.
      set (M' := projT1 _) in HM__terminate at 1; replace M' with M in *;[ | unfold M,M';reflexivity];clear M'.
      hnf in HM__terminate.
      (* Question: does termination/Realisation framework give me ability to say that every execution also terminates early? *)
      
       idtac. possibly_bracketed_ident+.
      
      rewrite Hk.
        simpl_surject.
        simpl_surject.
      tape_surject. }
      { }
      specialize ()
      specialize LMtoTM.Realises with (1:=H__loop). Realise
        
    }
    hnf. hnf. split. cbn.  fold HaltsOrDiverges_fixed_mTM. intros H_HaltOrDiv.
  }
  
Qed.
