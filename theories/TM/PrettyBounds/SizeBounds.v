From Complexity.TM Require Import TM_facts Code.CodeTM.
From Complexity.Libs Require Import MaxList MoreList Vectors.

(* MOVE : this file contains general lemmas from is all over the place... *)


Lemma sizeOfmTapes_max_list_map (sig : Type) (n : nat) (T : tapes sig n) :
  sizeOfmTapes T = max_list_map (@sizeOfTape _) (Vector.to_list T).
Proof.
  unfold sizeOfmTapes.
  rewrite Vector.to_list_fold_left.
  rewrite Vector.to_list_map.
  unfold max_list_map, max_list.
  apply max_list_rec_eq_foldl.
Qed.

Lemma sizeOfmTapes_upperBound (sig : Type) (n : nat) (tps : tapes sig n) :
  forall t, Vector.In t tps -> sizeOfTape t <= sizeOfmTapes tps.
Proof.
  intros. rewrite sizeOfmTapes_max_list_map.
  apply max_list_map_ge.
  now apply Vector.to_list_In.
Qed.

Lemma right_sizeOfTape sig' (t:tape sig') :
  length (right t) <= sizeOfTape t.
Proof.
  destruct t;cbn. all:autorewrite with list;cbn. all:nia.
Qed.

Lemma length_tape_local_right sig' (t:tape sig') :
  length (tape_local (tape_move_right t)) <= sizeOfTape t.
Proof.
  destruct t;cbn.  1-3:nia. rewrite tape_local_move_right'. autorewrite with list;cbn. all:nia.
Qed.
