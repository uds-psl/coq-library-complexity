(* -*- company-coq-local-symbols: (("|_|" .?␣)); -*- *)
From Undecidability.L.Complexity.Cook Require Import GenNP TCSR Prelim GenNP_GenNPInter_Basics GenNP_GenNPInter_Tape GenNP_GenNPInter_Transition. 
From PslBase Require Import FiniteTypes. 

From Undecidability.TM Require Import TM.
Require Import Lia. 

Module nondet (sig : TMSig). 
  Module trans' := transition sig. 
  Export trans'. 

  Inductive nondetSig' := nblank | nstar | ndelimC | ninit : nondetSig'. 

  Definition nondetSig := sum Gamma nondetSig'. 

  Definition nondetRule := nondetSig -> nondetSig -> nondetSig -> nondetSig -> nondetSig -> nondetSig -> Prop. 

  Notation "f $ x" := (f x) (at level 60, right associativity, only parsing).

  Inductive nondetRules : nondetRule :=
  | bbbC : nondetRules (inr nblank) (inr nblank) (inr nblank) (inl $ inr $ inr (neutral, |_|)) (inl $ inr $ inr (neutral, |_|)) (inl $ inr $ inr (neutral, |_| ))
  | dbbC : nondetRules (inr ndelimC) (inr nblank) (inr nblank) (inl $ inr $ inl delimC) (inl $ inr $ inr (neutral, |_|)) (inl $ inr $ inr (neutral, |_|))
  | bbdC : nondetRules (inr nblank) (inr nblank) (inr ndelimC) (inl $ inr $ inr (neutral, |_|)) (inl $ inr $ inr (neutral, |_|)) (inl $ inr $ inl delimC)
  | bbiC : nondetRules (inr nblank) (inr nblank) (inr ninit) (inl $ inr $ inr (neutral, |_|)) (inl $ inr $ inr (neutral, |_|)) (inl $ inl (start, |_|))
  | bisC m : nondetRules (inr nblank) (inr ninit) (inr nstar) (inl $ inr $ inr (neutral, |_|)) (inl $ inl (start, |_|)) (inl $ inr $ inr (neutral, m)).

End nondet. 
