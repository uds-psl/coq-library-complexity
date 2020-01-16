From PslBase Require Import Base FinTypes. 
From PslBase Require Import Vectors.Vectors. 
From Undecidability Require Import L.Complexity.Cook.Prelim FlatPR FlatFinTypes. 
From Undecidability.L.Complexity.Cook Require Export TPR.
Require Import Lia.

Record FlatTPR := {
  Sigma : nat;
  init : list nat;
  windows : list (TPRWin nat);
  final : list (list nat);
  steps : nat
  }.

Definition finReprEl' (X : finType) (e : nat) (E : X) := e = index E. 

Inductive isFlatTPRWinPOf (X : finType) (flatwinp : TPRWinP nat) (winp : TPRWinP X) := 
  mkIsFlatTPRWinPOf (Helem1 : finReprEl' (winEl1 flatwinp) (winEl1 winp))
    (Helem2 : finReprEl' (winEl2 flatwinp) (winEl2 winp))
    (Helem3 : finReprEl' (winEl3 flatwinp) (winEl3 winp))
  : isFlatTPRWinPOf flatwinp winp. 

Inductive isFlatTPRWinOf (X : finType) (flatwin : TPRWin nat) (win : TPRWin X) := 
  mkIsFlatTPRWinOf (Hprem : isFlatTPRWinPOf (prem flatwin) (prem win)) 
    (Hconc : isFlatTPRWinPOf (conc flatwin) (conc win))
  : isFlatTPRWinOf flatwin win. 

Inductive isFlatTWindowsOf (X : finType) (flatwindows : list (TPRWin nat)) (windows : list (TPRWin X)) := 
  mkIsFlatWindowsOf (Hsound : forall flatwin, flatwin el flatwindows -> exists win, win el windows /\ isFlatTPRWinOf flatwin win)
    (Hcomplete : forall win, win el windows -> exists flatwin, flatwin el flatwindows /\ isFlatTPRWinOf flatwin win)
  : isFlatTWindowsOf flatwindows windows. 

Inductive isFlatTPROf (fpr : FlatTPR) (pr : TPR) := 
  mkIsFlatPROf (HSigma : finRepr (TPR.Sigma pr) (Sigma fpr))
    (HInit : isFlatListOf (init fpr) (TPR.init pr))
    (HWindows : isFlatTWindowsOf (windows fpr) (TPR.windows pr))
    (HFinal : isFlatFinalOf (final fpr) (TPR.final pr))
  : isFlatTPROf fpr pr.

Definition FlatTPRLang (C : FlatTPR) := exists (C' : TPR), isFlatTPROf C C' /\ TPRLang C'. 


(*Definition TPRWinP_ofFlatType (winp : TPRWinP nat) (k : nat) := winEl1 winp < k /\ winEl2 winp < k /\ winEl3 winp < k.*)
(*Definition TPRWin_ofFlatType (win : TPRWin nat) (k : nat) := TPRWinP_ofFlatType (prem win) k /\ TPRWinP_ofFlatType (conc win) k. *)

(*Definition FlatTPR_wellformed ftpr := *)
  (*length (init ftpr) >= 3*)
  (*/\ list_ofFlatType (Sigma ftpr) (init ftpr) *)
  (*/\ (forall s, s el final ftpr -> list_ofFlatType (Sigma ftpr) s)*)
  (*/\ (forall win, win el windows ftpr -> TPRWin_ofFlatType win (Sigma ftpr)). *)

(*Definition FlatTPRLang (C : FlatTPR) := FlatTPR_wellformed C /\ exists (sf : list nat), list_ofFlatType  (Sigma C) sf /\ relpower (valid (rewritesHeadList (windows C))) (steps C) (init C) sf /\ satFinal (final C) sf. *)

