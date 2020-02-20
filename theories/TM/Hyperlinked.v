From Undecidability Require Import TM.Prelim.
From Undecidability Require Import TM.TM.
From Undecidability.TM Require Import Basic.Mono Basic.Null Compound.Multi.

(** This file is meant as an entry point for the hyperlinks in the paper. For [Check]s, just click them to get to the lemma. *)


Section PrimitiveMachines.

  Check Mono.ReadChar_Sem.
  
  Check Mono.Write_Sem.
  
  Check Mono.Move_Sem.
  
  Check Multi.Nop_Sem.

End PrimitiveMachines.

