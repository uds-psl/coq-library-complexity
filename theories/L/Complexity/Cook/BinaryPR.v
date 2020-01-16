From PslBase Require Import Base. 
From PslBase Require Import FiniteTypes. 
Require Import Lia.
From Undecidability Require Import L.Complexity.Cook.Prelim.
From Undecidability.L.Complexity.Cook Require Export PR.

Record BinaryPR := {
  offset : nat;
  width : nat;
  init : list bool;
  windows : list (PRWin bool);
  final : list (list bool);
  steps : nat
  }.

Definition BinaryPR_wellformed (c : BinaryPR) := 
  width c > 0 
  /\ length (init c) >= width c
  /\ (forall win, win el windows c -> PRWin_of_size win (width c)) 
  /\ (exists k, length (init c) = k * offset c).

Definition BinaryPRLang (C : BinaryPR) := 
  BinaryPR_wellformed C /\ exists (sf : list bool), relpower (valid (offset C) (width C) (windows C)) (steps C) (init C) sf /\ satFinal (offset C) (length (init C)) (final C) sf.
