From Undecidability.L Require Import L.
From Undecidability.L.Datatypes Require Import Lists LNat.
From Complexity.Libs Require Export PSLCompat.
Require Import Lia. 

(** * Shared Definitions for SAT and FSAT *)

Notation var := (nat) (only parsing). 
Notation assgn := (list var). 

Definition evalVar a v  := list_in_decb Nat.eqb a v.

Lemma evalVar_in_iff a v : evalVar a v = true <-> v el a. 
Proof. 
  unfold evalVar. rewrite list_in_decb_iff; [easy | symmetry; apply Nat.eqb_eq].
Qed.

Lemma evalVar_monotonic a a' v : a <<= a' -> evalVar a v = true -> evalVar a' v = true.
Proof. 
  intros H1 H2. rewrite evalVar_in_iff in *. firstorder.
Qed.

Lemma evalVar_assgn_equiv a a' v : a === a' -> evalVar a v = evalVar a' v. 
Proof. 
  intros H. enough (evalVar a v = true <-> evalVar a' v = true).
  { destruct evalVar, evalVar; firstorder. }
  split; apply evalVar_monotonic; apply H. 
Qed.


