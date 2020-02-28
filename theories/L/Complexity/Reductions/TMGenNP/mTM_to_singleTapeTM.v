From Undecidability.L Require Import Tactics.LTactics.
From Undecidability.L.Datatypes Require Import Lists LVector.
From Undecidability.L.Complexity Require Import NP Synthetic Monotonic.
From Undecidability.TM Require Import TM.
From Undecidability.TM Require TM ProgrammingTools CaseList.


From Undecidability.L.Complexity  Require GenNP.
From Undecidability.L.Complexity  Require Import LMGenNP TMGenNP_fixed_mTM.


From Undecidability.TM.Single Require EncodeTapes StepTM DecodeTapes. (** In emacs: coq-prefer-top-of-conclusion: t; *)


Module MultiToMono.
  Section multiToMono.

    Import EncodeTapes DecodeTapes Single.StepTM ProgrammingTools Combinators Decode.
    Context (sig F:finType) (n:nat) (M__multi : pTM sig F (S n)).

    Definition M : pTM ((sigList (sigTape sig)) ^+) (option F) 1 :=
      If (CheckTapeContains.M (CheckEncodesTapes.M (S n)))
         (Relabel (ToSingleTape M__multi) Some)
         (Return Nop None).

    


  End multiToMono.
End MultiToMono.

Lemma LMGenNP_to_TMGenNP_mTM (sig:finType) (n:nat) `{R__sig : registered sig}  (M : mTM sig (S n)):
  exists sig' `{R__sig' : registered sig'} (M' : mTM sig 1),
    restrictBy (HaltsOrDiverges_fixed_mTM M) (TMGenNP_fixed_mTM M)
               ⪯p unrestrictedP (TMGenNP_fixed_singleTapeTM M').
Proof.

Abort.
