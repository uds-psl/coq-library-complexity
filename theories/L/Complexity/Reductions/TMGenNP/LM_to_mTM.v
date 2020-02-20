From Undecidability.L Require Import Tactics.LTactics.
From Undecidability.L.Datatypes Require Import Lists LVector.
From Undecidability.L.Complexity Require Import NP Synthetic Monotonic.
From Undecidability.TM Require Import TM.


From Undecidability.L.Complexity  Require Import LMGenNP TMGenNP_fixed_mTM.
From Undecidability.L.AbstractMachines Require Import FlatPro.Computable.LPro.

(* TODO: find: *)
Axiom (sig:finType) (n:nat) (X:Type).
Context `{R__sig : registered sig} `{registered X}.
Axiom  (M : mTM sig (S n)) .

Lemma LMGenNP_to_TMGenNP_mTM : LMGenNP X ⪯p TMGenNP_fixed_mTM M.
Abort.



