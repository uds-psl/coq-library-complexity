From Undecidability.L.Complexity Require Import NP Synthetic Monotonic GenNPHalt.




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

Print GenNPHalt.

Check NPhard_GenNP.


(** Have: Implementation of Heap-based machine (Not step-indexed) *)

From Undecidability.LAM  Require TM.HaltingProblem.


Print HaltingProblem.Loop_Rel.
Print HaltingProblem.Loop_T.

(** Not Complete: nice form of Time bound *)
From Undecidability.LAM  Require TM.LMBounds.
Print LMBounds.LM.


(** Approach: simulate step-indexed L interpreter inside TM *)
(** Problems: Well-formedness of certificate-input? *)

(** Maybe intermediate problem in terms of Heap-Machine?)
