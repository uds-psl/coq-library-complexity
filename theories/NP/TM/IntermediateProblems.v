From Undecidability.L Require Import Tactics.LTactics Prelim.MoreList Prelim.MoreBase.
From Complexity.Complexity Require Import NP Definitions Monotonic.
From Complexity.NP Require Import L.GenNP.


(** * From L to TMs *)

(** Start: *)
(** * This start might be bad, as we need to check the bound explicitly, e.g. count the beta-steps during the simulation. *)
(** * But we can choose the bound large enough such that the term we simulate halts in the bound or always diverges *)
(** * We might want to simulate some L term that always halts *)
(** * But that means we need to distinguish true/false in the representation. *)

(** * Eventuell moechten wir nicht mit einem "einfachen" problem starten, sondern erst eienn lambda-trm scheiben, der decider für eine lang genuge zeit simulirt und dann hält oder divergiert, je nachdem ob der Decider wahr oder falsch sagt *)
(** * Divergenz ist ein schlechter Problem, wenn man von divergens reduziert, da man häufig nur obere schranken für die Laufzeit der Simulatoren hat.

Da der simulierte Term evtl aber mit groesserer Schranke haelt muesste man dann schritte mitzählen. *)

(* Weitere Idee: Prädikat nutzen, um Probleminstanzen weiter einzuschränken? *)

From Undecidability.TM Require Import TM CodeTM.
From Undecidability Require Import LFinType.

From Complexity Require Import NP L_to_LM LM_to_mTM mTM_to_singleTapeTM TMGenNP_fixed_mTM Subtypes.

Import LNat.
Lemma GenNP_to_TMGenNP:
  GenNP (list bool) ⪯p TMGenNP_fixed_singleTapeTM (projT1 (M_multi2mono.M__mono (projT1 M.M))).
Proof.
  eapply reducesPolyMO_transitive. now apply GenNP_to_LMGenNP.
  eapply reducesPolyMO_transitive. now apply LMGenNP_to_TMGenNP_mTM.
  now apply TMGenNP_mTM_to_TMGenNP_singleTM.
Qed.

(*
Print Assumptions GenNP_to_TMGenNP.
*)
(** Not Complete: nice form of Time bound *)
(*From Undecidability.L.AbstractMachines.TM_LHeapInterpreter  Require TM.LMBounds. *)


(** Approach: simulate step-indexed L interpreter inside TM *)
(** Problems: Well-formedness of certificate-input? *)

(** Maybe intermediate problem in terms of Heap-Machine? *)
