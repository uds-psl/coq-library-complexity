From Coq Require Import Lia Vectors.Vector.
Set Implicit Arguments.

Fixpoint split_vector {X : Type} {n : nat} (v : Vector.t X n) (k : nat) : Vector.t X (min k n) * Vector.t X (n-k).
Proof.
  destruct k as [ | k']; cbn.
  - split. apply Vector.nil.
    eapply Vector.cast. apply v. abstract lia.
  - destruct v as [ | x n' v']; cbn.
    + split. apply Vector.nil. apply Vector.nil.
    + specialize (split_vector X n' v' k') as (rec1&rec2).
      split. apply Vector.cons. apply x. apply rec1. apply rec2.
Defined. (* because definition *)


Lemma vector_cast_refl (X : Type) (n1 : nat) (H1 : n1 = n1) (v : Vector.t X n1) :
  Vector.cast v H1 = v.
Proof. induction v; cbn; f_equal; auto. Qed.

Lemma vector_cast_ext (X : Type) (m n : nat) (H1 H2 : n = m) (v : Vector.t X n) :
  Vector.cast v H1 = Vector.cast v H2.
Proof.
  revert H1 H2. revert m. induction v as [ | x n v IH]; intros.
  - cbn. destruct m. reflexivity. congruence.
  - cbn. destruct m. congruence. f_equal. auto.
Qed.

Lemma vector_cast_2 (X : Type) (n m : nat) (H1 : n = m) (H2 : m = n) (v : Vector.t X n) :
  Vector.cast (Vector.cast v H1) H2 = v.
Proof.
  revert H2 H1. revert m. induction v as [ | x n v IH]; intros.
  - cbn. destruct m; cbn. reflexivity. congruence.
  - cbn. destruct m; cbn. congruence. f_equal. auto.
Qed.


Lemma split_vector_correct (X : Type) (n : nat) (v : Vector.t X n) (k : nat) (H : min k n + (n-k) = n) :
  Vector.cast (Vector.append (fst (split_vector v k)) (snd (split_vector v k))) H = v.
Proof.
  revert n v H. induction k as [ | k IH]; intros; cbn.
  - destruct v; cbn; f_equal. apply vector_cast_2.
  - revert k H IH. destruct v as [ | x n v]; intros.
    + cbn. reflexivity.
    + cbn. specialize (IH _ v (f_equal Init.Nat.pred H)). destruct (split_vector v k) as [rec1 rec2] eqn:E. cbn in *. f_equal. auto.
Qed.

Lemma split_nat (n k : nat) : min k n + (n-k) = n.
Proof.
  revert n. induction k as [ | ? IH]; intros; cbn.
  - lia.
  - destruct n; cbn; f_equal; auto.
Qed.
