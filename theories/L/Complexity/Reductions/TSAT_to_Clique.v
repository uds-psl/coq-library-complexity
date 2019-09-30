From Undecidability.L.Complexity Require Import NP Synthetic Problems.SAT Problems.Clique. 
From Undecidability.L Require Import Tactics.LTactics.

(*we first design the reduction function*)
(* idea: for every clause,  *)

Lemma 3sat_to_clique  : reducesPolyMO TSAT LClique. 
Proof. 
Admitted. 

