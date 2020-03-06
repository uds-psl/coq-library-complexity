
            
From Undecidability Require Import MaxList.
From Undecidability Require Import TM.TM.

(* MOVE : this file contains general lemmas from is all over the place... *)

Fixpoint vector_to_list (X : Type) (n : nat) (v : Vector.t X n) : list X :=
  match v with
  | Vector.nil _ => List.nil
  | Vector.cons _ x n v' => x :: vector_to_list v'
  end.


Lemma vector_to_list_correct (X : Type) (n : nat) (v : Vector.t X n) :
  vector_to_list v = Vector.to_list v.
Proof.
  induction v.
  - cbn. auto.
  - cbn. f_equal. auto.
Qed.

Lemma vector_to_list_length (X : Type) (n : nat) (v : Vector.t X n) :
  length (vector_to_list v) = n.
Proof.
  induction v.
  - cbn. auto.
  - cbn. f_equal. auto.
Qed.


Lemma vector_to_list_map (X Y : Type) (f : X -> Y) (n : nat) (v : Vector.t X n) :
  map f (vector_to_list v) = vector_to_list (Vector.map f v).
  induction v.
  - cbn. auto.
  - cbn. f_equal. auto.
Qed.

Lemma vector_to_list_cast (X : Type) (n1 n2 : nat) (H : n1 = n2) (v : Vector.t X n1) :
  vector_to_list (Vector.cast v H) = vector_to_list v.
Proof. subst. rename n2 into n. induction v as [ | x n v IH]; cbn; f_equal; auto. Qed.

Lemma vector_to_list_eta (X : Type) (n : nat) (v : Vector.t X (S n)) :
  Vector.hd v :: vector_to_list (Vector.tl v) = vector_to_list v.
Proof. destruct_vector. cbn. reflexivity. Qed.

Lemma vector_to_list_map2_eta (X Y Z : Type) (n : nat) (f : X -> Y -> Z) (xs : Vector.t X (S n)) (ys : Vector.t Y (S n)) :
  f (Vector.hd xs) (Vector.hd ys) :: vector_to_list (Vector.map2 f (Vector.tl xs) (Vector.tl ys)) =
  vector_to_list (Vector.map2 f xs ys).
Proof. now destruct_vector. Qed.

(** Technical compatibility lemma: Coq's standard library is soo inconsistent... *)
Lemma fold_left_vector_to_list (X Y : Type) (n : nat) (f : Y -> X -> Y) (v : Vector.t X n) (a : Y) :
  Vector.fold_left f a v = fold_left f (vector_to_list v) a.
Proof. revert a. induction v as [ | x n v IH]; intros; cbn in *; f_equal; auto. Qed.

Lemma max_list_rec_eq_foldl (a : nat) (xs : list nat) :
  fold_left max xs a = max_list_rec a xs.
Proof.
  revert a. induction xs as [ | x xs IH]; intros; cbn in *.
  - reflexivity.
  - rewrite IH. rewrite !max_list_rec_max. nia.
Qed.

Lemma sizeOfmTapes_max_list_map (sig : Type) (n : nat) (T : tapes sig n) :
  sizeOfmTapes T = max_list_map (@sizeOfTape _) (vector_to_list T).
Proof.
  unfold sizeOfmTapes.
  rewrite fold_left_vector_to_list.
  rewrite <- vector_to_list_map.
  unfold max_list_map, max_list.
  apply max_list_rec_eq_foldl.
Qed.

Lemma vector_to_list_In (X : Type) (n : nat) (xs : Vector.t X n) (x : X) :
  In x (vector_to_list xs) <-> Vector.In x xs.
Proof.
  split.
  - induction xs as [ | y n xs IH]; intros; cbn in *.
    + auto.
    + destruct H as [ <- | H].
      * now constructor.
      * now constructor; auto.
  - induction xs as [ | y n xs IH]; intros; cbn in *.
    + inv H.
    + apply In_cons in H as [<- | H].
      * now constructor.
      * now constructor; auto.
Qed.

Lemma sizeOfmTapes_upperBound (sig : Type) (n : nat) (tps : tapes sig n) :
  forall t, Vector.In t tps -> sizeOfTape t <= sizeOfmTapes tps.
Proof. intros. rewrite sizeOfmTapes_max_list_map. apply max_list_map_ge. now apply vector_to_list_In. Qed.

From Undecidability Require Import L.Prelim.MoreList.

Lemma max_list_sumn l : max_list l <= sumn l.
Proof.
  unfold max_list.
  induction l;cbn. 2:rewrite max_list_rec_max'. all:nia.
Qed.
