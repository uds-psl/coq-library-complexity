From PslBase Require Import Base. 
From PslBase Require Import Vectors.Vectors. 
From Undecidability Require Import L.Complexity.Cook.Prelim.
From Undecidability.L.Complexity.Cook Require Export PR.
Require Import Lia.

Record FlatPR := {
  Sigma : nat;
  offset : nat;
  width : nat;
  init : list nat;
  windows : list (PRWin nat);
  final : list (list nat);
  steps : nat
  }.

Definition list_ofFlatType (l : list nat) ( k : nat) := forall a, a el l -> a < k.
Definition PRWin_ofFlatType (win : PRWin nat) (k : nat) := list_ofFlatType (prem win) k /\ list_ofFlatType (conc win) k. 

Definition FlatPR_wellformed fpr := 
  width fpr > 0 
  /\ (forall win, win el windows fpr -> PRWin_of_size win (width fpr)) 
  /\ (exists k, length (init fpr) = k * offset fpr)
  /\ list_ofFlatType (init fpr) (Sigma fpr)
  /\ (forall s, s el final fpr -> list_ofFlatType s (Sigma fpr))
  /\ (forall win, win el windows fpr -> PRWin_ofFlatType win (Sigma fpr)). 

Definition FlatPRLang (C : FlatPR) := FlatPR_wellformed C /\ exists (sf : list nat), list_ofFlatType sf (Sigma C) /\ relpower (valid (offset C) (width C) (windows C)) (steps C) (init C) sf /\ satFinal (final C) sf.
