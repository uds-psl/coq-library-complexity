From PslBase Require Import Base. 
From PslBase Require Import Vectors.Vectors. 
From Undecidability Require Import L.Complexity.Cook.Prelim FlatPR.
From Undecidability.L.Complexity.Cook Require Export TPR.
Require Import Lia.

Record FlatTPR := {
  Sigma : nat;
  init : list nat;
  windows : list (TPRWin nat);
  final : list (list nat);
  steps : nat
  }.

Definition TPRWinP_ofFlatType (winp : TPRWinP nat) (k : nat) := winEl1 winp < k /\ winEl2 winp < k /\ winEl3 winp < k.
Definition TPRWin_ofFlatType (win : TPRWin nat) (k : nat) := TPRWinP_ofFlatType (prem win) k /\ TPRWinP_ofFlatType (conc win) k. 

Definition FlatTPR_wellformed ftpr := 
  list_ofFlatType (init ftpr) (Sigma ftpr)
  /\ (forall s, s el final ftpr -> list_ofFlatType s (Sigma ftpr))
  /\ (forall win, win el windows ftpr -> TPRWin_ofFlatType win (Sigma ftpr)). 

Definition FlatTPRLang (C : FlatTPR) := FlatTPR_wellformed C /\ exists (sf : list nat), list_ofFlatType sf (Sigma C) /\ relpower (valid (rewritesHeadList (windows C))) (steps C) (init C) sf /\ satFinal (final C) sf. 

