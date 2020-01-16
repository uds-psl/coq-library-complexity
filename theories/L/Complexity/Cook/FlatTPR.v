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
  length (init ftpr) >= 3
  /\ list_ofFlatType (Sigma ftpr) (init ftpr) 
  /\ (forall s, s el final ftpr -> list_ofFlatType (Sigma ftpr) s)
  /\ (forall win, win el windows ftpr -> TPRWin_ofFlatType win (Sigma ftpr)). 

Section fixParams. 
  Variable (Sigma : nat).
  Variable (windows : list (TPRWin nat)). 
  Variable (p : rewritesHeadAbstract nat). 

(*  [>validity of a rewrite <]*)
  (*[>we use a modified version that enforces (even in the case of vacuous rewrites which are unconstrained by the rewrite windows) that the resulting strings are strings over the finite alphabet <]*)
  (*[>(for the non-flat version, this is already enforced by typing) <]*)
  (*Inductive validFlat : list nat -> list nat -> Prop :=*)
    (*| validFlatB: validFlat [] [] *)
    (*| validFlatSA a b x y: validFlat a b -> x < Sigma -> y < Sigma -> length a < 2 -> validFlat (x:: a) (y:: b)*)
    (*| validFlatS a b x y : validFlat a b -> x < Sigma -> y < Sigma -> p (x::a) (y::b) -> validFlat (x::a) (y::b). *)

  (*Hint Constructors valid. *)

  (*Lemma validFlat_length_inv a b : validFlat a b -> length a = length b. *)
  (*Proof.*)
    (*induction 1. *)
    (*- now cbn.*)
    (*- cbn; congruence.*)
    (*- cbn; congruence. *)
  (*Qed. *)

  (*Lemma relpower_validFlat_length_inv n a b : relpower validFlat n a b -> length a = length b. *)
  (*Proof.  induction 1; [solve [eauto] | ]. apply validFlat_length_inv in H. congruence. Qed. *)
End fixParams. 

Definition FlatTPRLang (C : FlatTPR) := FlatTPR_wellformed C /\ exists (sf : list nat), list_ofFlatType  (Sigma C) sf /\ relpower (valid (rewritesHeadList (windows C))) (steps C) (init C) sf /\ satFinal (final C) sf. 

