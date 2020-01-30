From PslBase Require Import Base FiniteTypes. 
From Undecidability.L.Complexity.Cook Require Import Prelim.
Require Import Lia.

(*We define uniform homomorphisms (of strings): Given strings of the same length, they output strings of the same length.*)
Section fixX.
  Variable (X Y : Type). 

  Definition homomorphism (h : list X -> list Y) := forall x1 x2, h (x1 ++ x2) = h x1 ++ h x2. 

  Lemma homo_nil h : homomorphism h -> h [] = []. 
  Proof. 
    intros. unfold homomorphism in H. specialize (H [] []). 
    cbn in H; rewrite H. destruct (h []) eqn:Heqn; cbn; [ congruence | ].  
    assert (|y :: l| = |(y :: l) ++ y :: l|) as H0 by congruence. 
    cbn in H0. rewrite app_length in H0. cbn in H0; lia. 
  Qed. 

  Lemma homo_cons h x l : homomorphism h -> h (x::l) = h [x] ++ h l.
  Proof. 
    intros. replace (x :: l) with ([x] ++ l) by now cbn. apply H. 
  Qed.

  Lemma homo_concat h : homomorphism h -> forall x, h (concat x) = concat (map h x). 
  Proof. 
    intros. induction x. 
    - cbn. apply homo_nil, H. 
    - cbn. rewrite H. now rewrite IHx. 
  Qed. 

  (*the last condition excludes the trivial homomorphism x ↦ ε *)
  Definition uniform_homomorphism (h : list X -> list Y) := homomorphism h /\ (forall x y, |h [x]| = |h [y]|) /\ (forall x, |h[x]| >= 1).

  Lemma unif_homo_length h x y : uniform_homomorphism h -> |x| = |y| -> |h x| = |h y|. 
  Proof. 
    intros (H1 & H2 & _). 
    revert y. induction x; intros. 
    - destruct y; cbn in *; [ | congruence]. now cbn. 
    - destruct y; cbn in *; [ congruence | ]. 
      replace (a :: x) with ([a] ++ x) by now cbn. replace (x0 :: y) with ([x0] ++ y) by now cbn. 
      rewrite !H1. rewrite !app_length. erewrite H2 with (y := x0). 
      rewrite IHx with (y := y); eauto. 
  Qed. 

  (*given an arbitrary function mapping elements of X into strings over Y, we can derive a homomorphism *)
  Definition canonicalHom (h' : X -> list Y) := fun (l : list X) => concat (map h' l). 
  Lemma canonicalHom_is_homomorphism h' : homomorphism (canonicalHom h'). 
  Proof. 
    unfold homomorphism. intros. unfold canonicalHom. 
    now rewrite map_app, concat_app. 
  Qed. 
End fixX. 


