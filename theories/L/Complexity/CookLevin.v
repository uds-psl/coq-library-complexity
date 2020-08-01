From Undecidability.L.Complexity Require Import NP Synthetic.
From Undecidability.L.Complexity.Problems Require Import GenNP.GenNP.
From Undecidability.L.Complexity.Reductions Require Import TMGenNP.IntermediateProblems.
From Undecidability.L.Complexity Require Import overview.

From Undecidability.L Require Import  LTactics FinTypeLookup LFinType LSum.
From PslBase Require Import FinTypes.

Lemma GenNP_to_SAT :
  restrictBy (LHaltsOrDiverges (list bool)) (GenNP (list bool)) ⪯p unrestrictedP SAT.SAT.
Proof.
  eapply reducesPolyMO_transitive. exact GenNP_to_TMGenNP.
  eapply reducesPolyMO_transitive. 2:exact FlatSingleTMGenNP_to_SAT.
  eapply fixedTM_to_FlatSingleTMGenNP.
  eapply finFun_computableTime_const. 2:exact 0.
  exact _.
Qed.

Lemma CookLevin : NPcomplete (unrestrictedP SAT.SAT).
Proof.
  split. 2:apply SAT.sat_NP.
  eapply red_NPhard. apply GenNP_to_SAT.
  From Undecidability Require Import GenNP_is_hard CanEnumTerm.
  apply NPhard_GenNP.
  eapply boollist_enum.boollists_enum_term.
Qed.

(* Print Assumptions CookLevin. *)
(* Closed under the global context *)
