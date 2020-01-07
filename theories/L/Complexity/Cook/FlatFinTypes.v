From PslBase Require Import FiniteTypes.
Require Import PslBase.FiniteTypes.BasicDefinitions.
Require Import Lia.
From Undecidability.L.Complexity.Cook Require Import Prelim.

(*a finite type is represented by the number of its elements *)
Definition finRepr (X : finType) (n : nat) := n = length (elem X ). 
(*we just enumerate the elements starting at 0 *)
Definition finReprEl (X : finType) (n : nat) k (x : X) := finRepr X n /\ k < n /\ index x = k.  

Definition flatOption (n : nat) := S n.
Definition flatProd (a b : nat) := a * b.
Definition flatSum (a b : nat) := a + b.

Definition flatNone := 0.
Definition flatSome k := S k. 
Definition flatInl (k : nat) := k.
Definition flatInr (a: nat) k := a + k. 
Definition flatPair (a b : nat) x y := x * b + y. 

Lemma finReprOption (X : finType) (n : nat) : finRepr X n -> finRepr (FinType (EqType (option X))) (flatOption n).
Proof. 
  intros. unfold finRepr in *. unfold flatOption; cbn -[enum]. rewrite H; cbn.
  rewrite map_length. reflexivity. 
Qed. 

Lemma finReprElSome (X : finType) n k x : finReprEl n k x -> @finReprEl (FinType (EqType (option X))) (flatOption n) (flatSome k) (Some x). 
Proof. 
  intros (H1 & H2 & H3). split; [ | split]; cbn in *.
  - now apply finReprOption. 
  - unfold flatSome, flatOption; lia. 
  - rewrite getPosition_map. 2: unfold injective; congruence. now rewrite <- H3. 
Qed. 

Lemma finReprElNone (X : finType) n : finRepr X n -> @finReprEl (FinType (EqType (option X))) (flatOption n) flatNone None. 
Proof. 
  intros. split; [ | split]; cbn. 
  - now apply finReprOption.
  - unfold flatNone, flatOption. lia. 
  - now unfold flatNone. 
Qed. 

Lemma finReprSum (A B: finType) (a b : nat) : finRepr A a -> finRepr B b -> finRepr (FinType (EqType (sum A B))) (flatSum a b). 
Proof. 
  intros. unfold finRepr in *. unfold flatSum; cbn in *.
  rewrite app_length. rewrite H, H0.
  unfold toSumList1, toSumList2. now rewrite !map_length.
Qed. 

Lemma finReprElInl (A B : finType) (a b : nat) k x : finRepr B b -> finReprEl a k x -> @finReprEl (FinType (EqType (sum A B))) (flatSum a b) (flatInl k) (inl x). 
Proof. 
  intros H0 (H1 & H2 & H3). split; [ | split]. 
  - now apply finReprSum. 
  - now unfold flatInl, flatSum. 
  - unfold finRepr in H1. rewrite H1 in *. 
    clear H0 H1. cbn. unfold toSumList1, toSumList2, flatInl. 
    rewrite getPosition_app1 with (k := k).
    + reflexivity. 
    + now rewrite map_length. 
    + unfold index in H3. rewrite <- getPosition_map with (f := (@inl A B)) in H3. 2: now unfold injective.
      easy. 
Qed. 

Lemma finReprElInr (A B : finType) (a b : nat) k x : finRepr A a -> finReprEl b k x -> @finReprEl (FinType (EqType (sum A B))) (flatSum a b) (flatInr a k) (inr x). 
Proof. 
  intros H0 (H1 & H2 & H3). split; [ | split ]. 
  - now apply finReprSum. 
  - now unfold flatInr, flatSum. 
  - unfold finRepr in H1; rewrite H1 in *. clear H1. 
    cbn. unfold toSumList1, toSumList2, flatInr. 
    rewrite getPosition_app2 with (k := k). 
    + rewrite map_length. unfold finRepr in H0. now cbn. 
    + now rewrite map_length.
    + intros H1. apply in_map_iff in H1. destruct H1 as (? & ? &?); congruence. 
    + unfold index in H3. rewrite <- getPosition_map with (f := (@inr A B)) in H3. 2: now unfold injective. 
      easy. 
Qed. 

Lemma finReprProd (A B : finType) (a b : nat) : finRepr A a -> finRepr B b -> finRepr (FinType (EqType (prod A B))) (flatProd a b).  
Proof. 
  intros. unfold finRepr in *. unfold flatProd.
  cbn. now rewrite prodLists_length. 
Qed. 

Lemma finReprElPair (A B : finType) (a b : nat) k1 k2 x1 x2 : finReprEl a k1 x1 -> finReprEl b k2 x2 -> @finReprEl (FinType (EqType (prod A B))) (flatProd a b) (flatPair a b k1 k2) (pair x1 x2).
Proof. 
  intros (H1 & H2 & H3) (F1 & F2 & F3). split; [ | split]. 
  - now apply finReprProd. 
  - unfold flatPair, flatProd. nia. 
  - cbn. unfold flatPair. unfold finRepr in *. rewrite H1, F1 in *.
    rewrite getPosition_prodLists with (k1 := k1) (k2 := k2); eauto. 
Qed. 

