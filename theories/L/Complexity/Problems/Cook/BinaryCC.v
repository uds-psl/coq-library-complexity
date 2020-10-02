From PslBase Require Import Base.
Require Import Lia.
From Complexity.L.Complexity Require Import MorePrelim. 
From Complexity.L.Complexity.Problems.Cook Require Export CC.
From Complexity.L.Complexity.Problems.Cook Require Import FlatCC.

(** * BinaryCC: Parallel Rewriting restricted to a binary alphabet *)
(** ** Definition *)

(** Note that BinaryCC is syntactially flat as we need not artificially restrict 𝔹 to be a finite type*)
Inductive BinaryCC := {
  offset : nat;
  width : nat;
  init : list bool;
  cards : list (CCCard bool);
  final : list (list bool);
  steps : nat
  }.

(** the same well-formedness conditions as for Parallel Rewriting *)
Definition BinaryCC_wellformed (c : BinaryCC) := 
  width c > 0 
  /\ offset c > 0
  /\ (exists k, k > 0 /\ width c = k * offset c)
  /\ length (init c) >= width c
  /\ (forall card, card el cards c -> CCCard_of_size card (width c)) 
  /\ (exists k, length (init c) = k * offset c).

Definition BinaryCCLang (C : BinaryCC) := 
  BinaryCC_wellformed C
  /\ exists (sf : list bool), relpower (valid (offset C) (width C) (cards C)) (steps C) (init C) sf
                     /\ satFinal (offset C) (length (init C)) (final C) sf.


(** extraction *)
From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Import  LProd LOptions.

MetaCoq Run (tmGenEncode "BinaryCC_enc" (BinaryCC)).
Hint Resolve BinaryCC_enc_correct : Lrewrite. 

From Complexity.L.Complexity Require Import PolyBounds. 

Instance term_Build_BinaryCC : computableTime' Build_BinaryCC (fun _ _ => (1, fun _ _ => (1, fun _ _ => (1, fun _ _ => (1, fun _ _ => (1, fun _ _ => (1, tt))))))).
Proof.
  extract constructor. solverec. 
Defined. 

Definition c__offset := 9.
Instance term_BinaryCC_offset : computableTime' offset (fun _ _ => (c__offset, tt)). 
Proof. 
  extract. unfold c__offset. solverec. 
Defined. 

Definition c__width := 9.
Instance term_BinaryCC_width : computableTime' width (fun _ _ => (c__width, tt)). 
Proof. 
  extract. unfold c__width. solverec. 
Defined. 

Definition c__init := 9.
Instance term_BinaryCC_init : computableTime' init (fun _ _ => (c__init, tt)). 
Proof. 
  extract. unfold c__init. solverec. 
Defined. 

Definition c__cards := 9.
Instance term_BinaryCC_cards : computableTime' cards (fun _ _ => (c__cards, tt)). 
Proof. 
  extract. unfold c__cards. solverec. 
Defined. 

Definition c__final := 9.
Instance term_BinaryCC_final : computableTime' final (fun _ _ => (c__final, tt)). 
Proof. 
  extract. unfold c__final. solverec. 
Defined. 

Definition c__steps := 9.
Instance term_BinaryCC_steps : computableTime' steps (fun _ _ => (c__steps, tt)). 
Proof. 
  extract. unfold c__steps. solverec. 
Defined. 

Lemma BinaryCC_enc_size (fpr : BinaryCC) : size (enc fpr) = size(enc (offset fpr)) + size (enc (width fpr)) + size (enc (init fpr)) + size (enc (cards fpr)) + size (enc (final fpr)) + size (enc (steps fpr)) + 8. 
Proof. 
  destruct fpr. cbn. unfold enc. cbn. nia.
Qed. 


