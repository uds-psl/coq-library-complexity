From PslBase Require Import Base. 
From PslBase Require Import Vectors.Vectors. 
From PslBase Require Import FiniteTypes. 
Require Import Lia.
Require Template.utils.

Definition substring (X : Type) (a b : list X) := exists b1 b2, b = b1 ++ a ++ b2. 
Definition prefix (X : Type) (a b : list X) := exists b', b = a ++ b'. 

Ltac discr_list := repeat match goal with
                    | [ H : |[]| = |?x :: ?xs| |- _] => cbn in H; congruence
                    | [ H : |?x :: ?xs| = |[]| |- _] => cbn in H; congruence
                    | [H : |?x :: ?xs| = 0 |- _] => cbn in H; congruence
                    | [H : 0 = |?x :: ?xs| |- _] => cbn in H; congruence
                    | [H : |[]| = S ?z |- _] => cbn in H; congruence
                    | [H : S ?z = |[]| |- _] => cbn in H; congruence
                    end. 
Ltac inv_list := repeat match goal with
                  | [H : |[]| = |?xs| |- _] => destruct xs; [ | discr_list]; cbn in H
                  | [H : |?x :: ?xs| = |?ys| |- _] => destruct ys; [ discr_list  | ]; cbn in H
                  | [H : |?xs| = 0 |- _] => destruct xs; [ | discr_list ]; cbn in H
                  | [H : 0 = |?xs| |- _] => destruct xs; [ | discr_list ]; cbn in H
                  | [H : |?xs| = S ?z |- _] => destruct xs ; [ discr_list | ]; cbn in H
                  | [H : S ?z = |?xs| |- _] => destruct xs; [ discr_list | ]; cbn in H
                  end. 

Lemma skipn_add (X : Type) (xs vs: list X) (i j : nat) : length vs = j -> skipn (j + i) (vs ++ xs) = skipn i xs. 
Proof. 
  revert vs; induction j; intros. 
  - inv_list. now cbn. 
  - inv_list. cbn. apply IHj. cbn in H; congruence.
Qed. 


Lemma skipn_app2 (X : Type) i (a b c : list X): c <> [] -> skipn i a = c -> skipn i (a ++ b) = c ++ b. 
Proof.
  intros H; revert i; induction a; intros. 
  - destruct i; cbn in H0; congruence. 
  - destruct i; cbn in H0.
    + cbn. now rewrite <- H0. 
    + cbn. now apply IHa. 
Qed. 

Lemma skipn_app3 (X : Type) i (a b : list X) : i <= |a| -> exists a', skipn i (a ++ b) = a' ++ b /\ a = firstn i a ++ a'. 
Proof. 
  intros. exists (skipn i a). split.
  + destruct (nat_eq_dec i (|a|)). 
    - rewrite skipn_app. 2: apply e. rewrite Template.utils.skipn_all2. 2: lia. now cbn. 
    - apply skipn_app2.
      * enough (|skipn i a| <> 0) by (destruct skipn; cbn in *; congruence). rewrite skipn_length. lia. 
      * reflexivity. 
  + now rewrite firstn_skipn. 
Qed.


Lemma length_app_decompose (X : Type) (a : list X) i j : length a = i + j -> exists a1 a2, a = a1 ++ a2 /\ length a1 = i /\ length a2 = j. 
Proof. 
  revert a. 
  induction i. 
  - cbn. intros. now exists [], a. 
  - cbn. intros. inv_list. assert (|a| = i + j) by lia. destruct (IHi a H0) as (a1 & a2 & H2 & H3). 
    exists (x :: a1), a2. firstorder. all: cbn. 1: rewrite H2. all: firstorder.
Qed. 


Inductive relpower (A : Type) (R : A -> A -> Prop) : nat -> A -> A -> Prop :=
| relpowerB (a : A) : relpower R 0 a a
| relpowerS (a b c : A) n : R a b -> relpower R n b c -> relpower R (S n) a c. 

Lemma relpower_trans A R n m (x y z : A) : relpower R n x y -> relpower R m y z -> relpower R (n + m) x z.
Proof. 
  induction 1. 
  - now cbn. 
  - intros. apply relpowerS with (b := b). assumption. now apply IHrelpower. 
Qed. 
