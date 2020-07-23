From PslBase Require Import Base.
Require Import Lia.
From Undecidability.L.Complexity Require Import MorePrelim. 
From Undecidability.L.Complexity.Problems.Cook Require Export PR.
From Undecidability.L.Complexity.Problems.Cook Require Import FlatPR.

(** * BinaryPR: Parallel Rewriting restricted to a binary alphabet *)

(** Note that BinaryPR is syntactially flat as we need not artificially restrict 𝔹 to be a finite type*)
Inductive BinaryPR := {
  offset : nat;
  width : nat;
  init : list bool;
  windows : list (PRWin bool);
  final : list (list bool);
  steps : nat
  }.

(** the same well-formedness conditions as for Parallel Rewriting *)
Definition BinaryPR_wellformed (c : BinaryPR) := 
  width c > 0 
  /\ offset c > 0
  /\ (exists k, k > 0 /\ width c = k * offset c)
  /\ length (init c) >= width c
  /\ (forall win, win el windows c -> PRWin_of_size win (width c)) 
  /\ (exists k, length (init c) = k * offset c).

Definition BinaryPRLang (C : BinaryPR) := 
  BinaryPR_wellformed C
  /\ exists (sf : list bool), relpower (valid (offset C) (width C) (windows C)) (steps C) (init C) sf
                     /\ satFinal (offset C) (length (init C)) (final C) sf.


(** extraction *)
From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Import  LProd LOptions LLNat LLists.

MetaCoq Run (tmGenEncode "BinaryPR_enc" (BinaryPR)).
Hint Resolve BinaryPR_enc_correct : Lrewrite. 

From Undecidability.L.Complexity Require Import PolyBounds. 

Instance term_Build_BinaryPR : computableTime' Build_BinaryPR (fun _ _ => (1, fun _ _ => (1, fun _ _ => (1, fun _ _ => (1, fun _ _ => (1, fun _ _ => (1, tt))))))).
Proof.
  extract constructor. solverec. 
Defined. 

Definition c__offset := 9.
Instance term_BinaryPR_offset : computableTime' offset (fun _ _ => (c__offset, tt)). 
Proof. 
  extract. unfold c__offset. solverec. 
Defined. 

Definition c__width := 9.
Instance term_BinaryPR_width : computableTime' width (fun _ _ => (c__width, tt)). 
Proof. 
  extract. unfold c__width. solverec. 
Defined. 

Definition c__init := 9.
Instance term_BinaryPR_init : computableTime' init (fun _ _ => (c__init, tt)). 
Proof. 
  extract. unfold c__init. solverec. 
Defined. 

Definition c__windows := 9.
Instance term_BinaryPR_windows : computableTime' windows (fun _ _ => (c__windows, tt)). 
Proof. 
  extract. unfold c__windows. solverec. 
Defined. 

Definition c__final := 9.
Instance term_BinaryPR_final : computableTime' final (fun _ _ => (c__final, tt)). 
Proof. 
  extract. unfold c__final. solverec. 
Defined. 

Definition c__steps := 9.
Instance term_BinaryPR_steps : computableTime' steps (fun _ _ => (c__steps, tt)). 
Proof. 
  extract. unfold c__steps. solverec. 
Defined. 

Lemma BinaryPR_enc_size (fpr : BinaryPR) : size (enc fpr) = size(enc (offset fpr)) + size (enc (width fpr)) + size (enc (init fpr)) + size (enc (windows fpr)) + size (enc (final fpr)) + size (enc (steps fpr)) + 8. 
Proof. 
  destruct fpr. cbn. unfold enc. cbn. nia.
Qed. 


