From Undecidability.L.Complexity Require Import NP.
From Undecidability.TM Require TM ProgrammingTools CaseList CaseBool Code.Decode Code.DecodeList.
From Undecidability.TM Require Import TM SizeBounds.

From Undecidability.L.Complexity  Require Import TMGenNP_fixed_mTM UpToCNary.

From Undecidability.L.AbstractMachines Require Import FlatPro.Programs.
     
Unset Printing Coercions.

From Undecidability.LAM Require Alphabets.

From Coq Require Import Lia Ring Arith.

From Undecidability.L.Complexity  Require Import GenNP_is_hard LMGenNP TMGenNP_fixed_mTM.
Check fun M =>
  restrictBy (LMHaltsOrDiverges _) (LMGenNP (list bool)) ⪯p (restrictBy (HaltsOrDiverges_fixed_mTM M) (TMGenNP_fixed_mTM M)).

From Undecidability Require Import Code.ListTM_concat_repeat.

Module BoollistToEnc.


  Definition enc_bool_perElem (b:bool) := [lamT;lamT;varT 0;lamT; lamT; varT (if b then 1 else 0); retT; retT;appT].
  Definition enc_bool_nil := [lamT; lamT; varT 1; retT; retT].
  Definition enc_bool_closing :=  [appT; retT; retT].

  Lemma enc_bool_explicit (bs : list bool):
    compile (Computable.enc bs) = flat_map enc_bool_perElem bs ++ enc_bool_nil ++ concat (repeat enc_bool_closing (length bs)).
  Proof.
    unfold Computable.enc. cbn. unfold Lists.list_enc. cbn. unfold LBool.bool_enc.
    induction bs as [ | b bs]. reflexivity.
    cbn - [concat repeat]. rewrite IHbs. replace (S (| bs |)) with (|bs|+1) by nia.
    destruct b;cbn - [concat repeat]. all:repeat (autorewrite with list; cbn - [concat repeat]). all:repeat f_equal.
    all:rewrite repeat_add_app,concat_app. all:easy.
  Qed.

  Arguments enc_bool_perElem : simpl never.
  
  Section M.
    Import ProgrammingTools Combinators ListTM CaseList CaseBool.
    Import Alphabets.


    Variable (sig : finType).
    (* Hypothesis (defX: inhabitedC sigX). *)

    (* We use the FinType instance of bool, as it has a Case-machine *)
    
    Context `{retr__list : Retract (sigList bool) sig}
            `{retr__Pro : Retract Alphabets.sigPro sig}
            `{retr__nat : Retract sigNat sig}.
    Local Instance retr__bool : Retract bool sig := ComposeRetract retr__list (Retract_sigList_X _).
  
    Check _ : codable sig (list bool).
    Check _ : codable sig bool.

    (* Tapes: 
       0: bs (input)
       1: result 
       2: intern (constant for ConcatRepeat [0])
       3: intern (length of bs for concatReepat [1])
     *)
    
    Definition Rel : pRel sig^+ unit 4 :=
      ignoreParam
        (fun tin 'tout =>
           forall (bs : list bool),
             tin[@Fin0] ≃ bs 
             -> isRight tin[@Fin1]
             -> isRight tin[@Fin2]
             -> isRight tin[@Fin3]
             -> isRight tout[@Fin0]
               /\ tout[@Fin1]  ≃ compile (Computable.enc (rev bs))
               /\ isRight tin[@Fin2]
               /\ isRight tin[@Fin3]).

    (* für step (prepend the bs-dependent symbols) 
               Tapes: 
       0: bs (input)
       1: result 
       2: head of bs
       3: intern (length of bs for concatReepat [1])
     *)

    Definition M__step : pTM sig^+ (option unit) 4 :=
      If (LiftTapes (ChangeAlphabet (CaseList.CaseList _) retr__list) [|Fin0;Fin2|])
         (Switch (LiftTapes (ChangeAlphabet CaseBool retr__bool) [|Fin2|])
                 (fun b => LiftTapes (ChangeAlphabet (WriteValue (encode (enc_bool_perElem b))) _) [| Fin2|];;
                        LiftTapes (ChangeAlphabet (App' _) _) [|Fin2;Fin1|];;
                        Return (LiftTapes (Reset _) [|Fin2|]) None))
         (Return (LiftTapes (Reset _) [|Fin0|]) (Some tt)).

    Definition Rel__step : pRel sig^+ (option unit) 4 :=
      (fun tin '(yout,tout) =>
           forall (bs : list bool) (res : Pro),
             tin[@Fin0] ≃ bs 
             -> tin[@Fin1] ≃ res
             -> isRight tin[@Fin2]
             -> match bs,yout with
                 [],  Some _ => isRight tout[@Fin0] /\ tout[@Fin1] = tin[@Fin1]
               | (b::bs),None => tout[@Fin0] ≃ bs /\ tout[@Fin1] ≃ enc_bool_perElem b++res
               | _,_ => False
               end
               /\ isRight tin[@Fin2]
               /\ tout[@Fin3] = tin[@Fin3]).

    
    Lemma Realises__step : M__step ⊨ Rel__step .
    Proof.
      eapply Realise_monotone.
      {unfold M__step. TM_Correct_noSwitchAuto. TM_Correct.
       2,3: now (notypeclasses refine (@Reset_Realise _ _ _ _ _);shelve).
       intros b. TM_Correct. 2:now (notypeclasses refine (@Reset_Realise _ _ _ _ _);shelve).
       now apply App'_Realise. }
      intros t (y,t') H. cbn. 
      intros bs res Hbs Hres Ht2. 
      destruct H as [H|H].
      -cbn in H. TMSimp. modpon H;[]. destruct bs. now exfalso.
       TMSimp. modpon H0;[]. modpon H1;[]. modpon H2;[]. TMSimp.
       repeat (simple apply conj). all:try contains_ext. now isRight_mono. reflexivity. 
      -cbn in H. TMSimp. modpon H;[]. destruct bs. 2:easy. TMSimp.
       modpon H1;[]. modpon H0; [].
       repeat (simple apply conj). all:try now isRight_mono. all:reflexivity.
       Unshelve. 4:eauto. 2:easy.
    Qed.

    Definition M__loop : pTM sig^+ unit 4 := While M__step.

    

    Definition M : pTM sig^+ unit 4 :=
      LiftTapes (Length retr__list retr__nat) [|Fin0;Fin1;Fin2;Fin3|];;
      LiftTapes (ChangeAlphabet (WriteValue (encode (enc_bool_closing))) _) [|Fin2|];;
      LiftTapes (ConcatRepeat.M retr__list retr__nat) [|Fin2;Fin3;Fin1|];;
      LiftTapes (Reset _) [|Fin2|];;
      LiftTapes (ChangeAlphabet (WriteValue (encode  (enc_bool_nil))) _ ) [|Fin2|];;
      LiftTapes (ChangeAlphabet (App' _) _) [|Fin2;Fin1|];;
      M__loop.


    (*
    Context (sig F:finType) (n:nat) (M__multi : pTM sig F n).

      (*TODO: Check that tape contaisn Encoding of programm*)
  (*
      Definition M : pTM _ _ 12 := LiftTapes HaltingProblem.Loop [|Fin1,Fin2,|].

      Definition Rel : pRel ((sigList (sigTape sig)) ^+) (option F) 1 :=
        fun t '(y,t') => match y with
                        None => ~ exists (v : tapes sig n), StepTM.contains_tapes t[@Fin0] v
                      | Some y => exists (v v': tapes sig n), StepTM.contains_tapes t[@Fin0] v
                                                        /\ StepTM.contains_tapes t'[@Fin0] v'
                                                        /\ Canonical_Rel M__multi v (y,v')
                      end.
  *) *)
  End M.
End BoollistToEnc.

From Undecidability.LAM Require HaltingProblem.

  
Module LMtoTM.
  Module LAM := LAM.TM.HaltingProblem.
  Section sec.
    Import ProgrammingTools Combinators.

    Check HaltingProblem.Loop.
    
    Context (sig F:finType) (n:nat) (M__multi : pTM sig F n).

    (*TODO: Check that tape contaisn Encoding of programm*)
(*
    Definition M : pTM _ _ 12 := LiftTapes HaltingProblem.Loop [|Fin1,Fin2,|].

    Definition Rel : pRel ((sigList (sigTape sig)) ^+) (option F) 1 :=
      fun t '(y,t') => match y with
                      None => ~ exists (v : tapes sig n), StepTM.contains_tapes t[@Fin0] v
                    | Some y => exists (v v': tapes sig n), StepTM.contains_tapes t[@Fin0] v
                                                      /\ StepTM.contains_tapes t'[@Fin0] v'
                                                      /\ Canonical_Rel M__multi v (y,v')
                    end.
*)
  End sec.
End LMtoTM.
