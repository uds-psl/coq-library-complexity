From Undecidability.L Require Import Tactics.LTactics.
From Undecidability.L.Datatypes Require Import Lists LVector.
From Undecidability.L.Complexity Require Import NP Synthetic Monotonic.
From Undecidability.TM Require Import TM Single.StepTM.

From Undecidability.L.Complexity  Require GenNP.
From Undecidability.L.Complexity  Require Import LMGenNP TMGenNP_fixed_mTM.


From Undecidability Require Import TM.Single.EncodeTapes.


Lemma LMGenNP_to_TMGenNP_mTM (sig:finType) (n:nat) `{R__sig : registered sig}  (M : mTM sig (S n)):
  exists sig' `{R__sig' : registered sig'} (M' : mTM sig 1),
    restrictBy (HaltsOrDiverges_fixed_mTM M) (TMGenNP_fixed_mTM M)
               ⪯p unrestrictedP (TMGenNP_fixed_singleTapeTM M').
Proof.
Abort.
