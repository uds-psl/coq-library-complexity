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

Lemma list_ofFlatType_app (l1 l2 : list nat) (k : nat) : list_ofFlatType (l1 ++ l2) k <-> list_ofFlatType l1 k /\ list_ofFlatType l2 k. 
Proof. 
  split; intros; unfold list_ofFlatType in *. 
  - setoid_rewrite in_app_iff in H. split; intros; apply H; eauto. 
  - destruct H as (H1 & H2); setoid_rewrite in_app_iff; intros a [ | ]; eauto. 
Qed. 

Definition PRWin_ofFlatType (win : PRWin nat) (k : nat) := list_ofFlatType (prem win) k /\ list_ofFlatType (conc win) k. 

Definition FlatPR_wellformed fpr := 
  width fpr > 0 
  /\ offset fpr > 0 
  /\ (exists k, k > 0 /\ width fpr = k * offset fpr)
  (*/\ (offset fpr <= width fpr)*)
  /\ length (init fpr) >= width fpr
  /\ (forall win, win el windows fpr -> PRWin_of_size win (width fpr)) 
  /\ (exists k, length (init fpr) = k * offset fpr)
  /\ list_ofFlatType (init fpr) (Sigma fpr)
  /\ (forall s, s el final fpr -> list_ofFlatType s (Sigma fpr))
  /\ (forall win, win el windows fpr -> PRWin_ofFlatType win (Sigma fpr)). 

Section fixParams. 
  Variable (Sigma : nat).
  Variable (offset : nat). 
  Variable (width : nat).
  Variable (windows : list (PRWin nat)). 
  Context (G0 : width > 0).

  (*validity of a rewrite *)
  (*we use a modified version that enforces (even in the case of vacuous rewrites which are unconstrained by the rewrite windows) that the resulting strings are strings over the finite alphabet *)
  (*(for the non-flat version, this is already enforced by typing) *)
  Inductive validFlat: list nat -> list nat -> Prop :=
  | validFlatB: validFlat [] [] 
  | validFlatSA a b u v : validFlat a b -> length a < width - offset -> list_ofFlatType u Sigma -> list_ofFlatType v Sigma -> length u = offset -> length v = offset -> validFlat (u++ a) (v++ b)
  | validFlatS a b u v rule: validFlat a b -> list_ofFlatType u Sigma -> list_ofFlatType v Sigma -> length u = offset -> length v = offset -> rule el windows -> rewritesHead rule (u ++ a) (v ++ b) -> validFlat (u ++ a) (v ++ b). 

  Lemma validFlat_length_inv a b : validFlat a b -> length a = length b. 
  Proof.
    induction 1. 
    - now cbn.
    - repeat rewrite app_length. firstorder. 
    - repeat rewrite app_length; firstorder. 
  Qed. 
End fixParams. 

Definition FlatPRLang (C : FlatPR) := FlatPR_wellformed C 
  /\ exists (sf : list nat), list_ofFlatType sf (Sigma C) 
      /\ relpower (validFlat (Sigma C) (offset C) (width C) (windows C)) (steps C) (init C) sf 
      /\ satFinal (offset C) (length (init C)) (final C) sf.

Section fixInstance.
  Variable (fpr : FlatPR). 
  Notation Sigma := (Sigma fpr).
  Notation offset := (offset fpr).
  Notation width := (width fpr).
  Notation init := (init fpr).
  Notation windows := (windows fpr).
  Notation final := (final fpr).
  Notation steps := (steps fpr). 

  Context (A : FlatPR_wellformed fpr). 

  Lemma validFlat_multiple_of_offset a b : validFlat Sigma offset width windows a b -> exists k, |a| = k * offset. 
  Proof. 
    induction 1 as [ | ? ? ? ? ? IH | ? ? ? ? ? ? IH]. 
    - exists 0. cbn; lia. 
    - destruct IH as (k & IH). exists (S k). now rewrite app_length. 
    - destruct IH as (k & IH). exists (S k). now rewrite app_length. 
  Qed. 

  Lemma valid_list_ofFlatType_invariant a b : 
    list_ofFlatType a Sigma -> validFlat Sigma offset width windows a b -> list_ofFlatType b Sigma. 
  Proof.
    intros H0 H. induction H. 
    - apply H0. 
    - apply list_ofFlatType_app in H0. apply list_ofFlatType_app. tauto. 
    - apply list_ofFlatType_app in H0. apply list_ofFlatType_app. tauto. 
  Qed. 

  Lemma relpower_valid_list_ofFlatType_invariant steps a b: 
    list_ofFlatType a Sigma -> relpower (validFlat Sigma offset width windows) steps a b -> list_ofFlatType b Sigma. 
  Proof. 
    intros. induction H0; [easy | ]. 
    apply IHrelpower. eapply valid_list_ofFlatType_invariant, H0. apply H. 
  Qed. 

  Lemma relpower_validFlat_length_inv n a b : relpower (validFlat Sigma offset width windows) n a b -> length a = length b. 
  Proof.  induction 1; [solve [eauto] | ]. apply validFlat_length_inv in H. congruence. Qed.

End fixInstance.
