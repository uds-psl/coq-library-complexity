From Undecidability.L Require Import Tactics.LTactics Prelim.MoreList Prelim.MoreBase.
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

From Undecidability.L.AbstractMachines.FlatPro Require LM_heap_def LM_heap_correct LPro Decompile.
Section LMGenNPHalt.
  Import LM_heap_def LM_heap_correct LBool.

  Definition initLMGen s c : (list (nat*list Tok)*list (nat*list Tok)*list (option ((nat * list Tok) * nat)))
    := ([(0,s)],[(0,c)],[]).
  
  Definition LMGenNPHalt' : list Tok*nat*nat -> Prop :=
    fun '(P, maxSize, steps (*in unary*)) =>
      exists (Q:list Tok), size (enc Q) <= maxSize /\ halts_k (initLMGen P Q) steps.

  Definition LMHaltsOrDiverges : list Tok*nat*nat -> Prop :=
    fun '(P, maxSize, steps (*in unary*)) =>
      exists s, size (enc (compile s)) <= maxSize -> forall k, halts_k (initLMGen P (compile s)) k -> k <= steps.

  Definition LMGenNPHalt := restrictBy LMHaltsOrDiverges LMGenNPHalt'.
  
  From Undecidability.L Require Import Functions.LoopSum.
  
  Lemma polyRed_GenNPHalt_to_LMGenNPHalt :
    GenNPHalt ⪯p LMGenNPHalt.
  Proof.
    (*)pose (f__s s c :=
            match decompile 0 c [] with
               inl _ => 
              | inr _ => false
            end
         ). *)
    pose (f := (fun '(s, maxSize, steps) => ([appT],cnst 0,cnst 1)): (term * nat * nat) -> _);cbn beta in f.
    eapply reducesPolyMO_intro with (f:=f).


  

  From Undecidability.LAM  Require TM.HaltingProblem.
  About HaltingProblem.Loop_Rel.
  About HaltingProblem.Loop_T.

  Abort.
End LMGenNPHalt.


(** Not Complete: nice form of Time bound *)
From Undecidability.LAM  Require TM.LMBounds.


(** Approach: simulate step-indexed L interpreter inside TM *)
(** Problems: Well-formedness of certificate-input? *)

(** Maybe intermediate problem in terms of Heap-Machine? *)
