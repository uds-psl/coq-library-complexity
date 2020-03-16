From Undecidability.L Require Import Tactics.LTactics.
From Undecidability.L.Datatypes Require Import Lists LVector.
From Undecidability.L.Complexity Require Import NP Synthetic Monotonic.
From Undecidability.TM Require Import TM.
From Undecidability.L.AbstractMachines Require Import FlatPro.Programs FlatPro.Computable.LPro.

From Undecidability.L.Complexity Require Import LMGenNP TMGenNP_fixed_mTM.

Require Undecidability.LAM.TM.HaltingProblem.
Module LAM := Undecidability.LAM.TM.HaltingProblem.

(* TODO: find: *)
Axiom (sig:finType) (n:nat).
Context `{R__sig : registered sig}.
Axiom  (M : mTM sig (S n)) .

Lemma LMGenNP_to_TMGenNP_mTM :
  restrictBy (LMHaltsOrDiverges (list bool)) (LMGenNP (list bool)) ⪯p (restrictBy (HaltsOrDiverges_fixed_mTM M) (TMGenNP_fixed_mTM M)).

Abort.
