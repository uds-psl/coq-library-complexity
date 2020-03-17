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
