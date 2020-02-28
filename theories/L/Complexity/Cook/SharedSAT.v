From Undecidability.L Require Import L.
From Undecidability.L.Datatypes Require Import LLists. 
Require Import Lia. 

Notation var := (nat) (only parsing). 
Notation assgn := (list var). 

Definition evalVar a v  := list_in_decb Nat.eqb a v.

Lemma evalVar_in_iff a v : evalVar a v = true <-> v el a. 
Proof. 
  unfold evalVar. rewrite list_in_decb_iff; [easy | symmetry; apply Nat.eqb_eq].
Qed.
