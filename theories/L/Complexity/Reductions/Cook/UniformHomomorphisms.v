From PslBase Require Import Base FiniteTypes. 
From Complexity.L.Complexity Require Import MorePrelim.
Require Import Lia.

(** * Uniform homomorphisms *)

(** We define uniform homomorphisms (of strings): Given strings of the same length, they output strings of the same length.*)
Section fixX.
  Variable (X Y : Type). 
  (** ** Homomorphisms *)

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

  (** Given an arbitrary function mapping elements of X into strings over Y, we can derive a homomorphism in a canonical way*)
  Definition canonicalHom (h' : X -> list Y) := fun (l : list X) => concat (map h' l). 
  Lemma canonicalHom_is_homomorphism h' : homomorphism (canonicalHom h'). 
  Proof. 
    unfold homomorphism. intros. unfold canonicalHom. 
    now rewrite map_app, concat_app. 
  Qed. 

  Lemma canonicalHom_is_unique h' : forall h'', homomorphism h'' -> (forall x, h'' [x] = h' x) -> forall x, h'' x = canonicalHom h' x. 
  Proof. 
    intros. induction x. 
    - cbn. erewrite homo_nil; easy.
    - erewrite homo_cons; [ | easy]; cbn. rewrite IHx. now rewrite H0. 
  Qed. 

  (** ** Uniform Homomorphisms *)

  (** A uniform homomorphism is ε-free and maps all strings of the same length to strings of the same length,
    (stated differently: |h x| = n * |x| for n > 0) *)
  Definition uniform_homomorphism (h : list X -> list Y) := 
    homomorphism h 
    /\ (forall x y, |h [x]| = |h [y]|) 
    /\ (forall x, |h[x]| >= 1).

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

  Lemma unif_homo_eps_free h : uniform_homomorphism h -> forall x, h x = [] -> x = []. 
  Proof. 
    intros (H1 & H2 & H3) x H. 
    destruct x as [ | x y]; [easy | ]. rewrite homo_cons in H by easy. 
    apply list_eqn_length in H. rewrite app_length in H. cbn in H. 
    specialize (H3 x); lia. 
  Qed. 

  Lemma canonical_uniform_homo f k : (forall x, |f x| = k) -> k > 0 -> uniform_homomorphism (canonicalHom f). 
  Proof. 
    intros H1 H2. repeat split. 
    - apply canonicalHom_is_homomorphism. 
    - intros x y. cbn. now rewrite !app_nil_r, !H1. 
    - intros x. cbn. rewrite !app_nil_r, H1. lia. 
  Qed. 

  Variable (h : list X -> list Y). 
  Context (h_unifHom : uniform_homomorphism h). 
  Lemma h_nil_cons x l : not (|h []| = |h (x :: l)|). 
  Proof. 
    intros H. replace (x ::l) with ([x] ++ l) in H by now cbn.
    rewrite (proj1 h_unifHom) in H. rewrite (homo_nil (proj1 h_unifHom)) in H. 
    rewrite !app_length in H. cbn in H.  
    specialize (proj2 (proj2 h_unifHom) x). lia.
  Qed. 

  Lemma h_length_inv l1 l2 : |h l1| = |h l2| -> |l1| = |l2|. 
  Proof. 
    revert l2. induction l1; intros. 
    + destruct l2; [easy | now apply h_nil_cons in H].  
    + destruct l2; [ symmetry in H; now apply h_nil_cons in H | ]. 
      cbn. f_equal. apply IHl1. 
      rewrite homo_cons in H; [ | apply h_unifHom]. 
      rewrite homo_cons with (x := x) in H; [ | apply h_unifHom].
      rewrite !app_length in H.
      rewrite (proj1 (proj2 h_unifHom)) with (y := x) in H. lia. 
  Qed. 

  Lemma h_length_inv' l1 l2 : h l1 = h l2 -> |l1| = |l2|. 
  Proof. intros; now apply h_length_inv. Qed. 

  Lemma h_nil_inv a : h a = [] -> a = []. 
  Proof. 
    intros H. destruct a; [ easy | ]. replace (x ::a) with ([x] ++ a) in H by now cbn.
    rewrite (proj1 h_unifHom) in H.  apply list_eqn_length in H. rewrite app_length in H. 
    specialize (proj2 (proj2 h_unifHom) x). cbn in H; lia.
  Qed. 

End fixX. 

Lemma h_length_multiply (X : finType) (Y : Type) (h : list X -> list Y) : uniform_homomorphism h -> { k : nat & forall x, |h x| = k * |x| }. 
Proof. 
  intros (H1 & H2 & H3). 
  destruct (elem X) eqn:H4 . 
  - exists 42. intros []. 
    + rewrite homo_nil by auto. easy.
    + specialize (elem_spec e) as H5. rewrite H4 in H5. destruct H5. 
  - exists (|h [e]|).  
    induction x as [ | a x IH]. 
    + rewrite homo_nil by auto; easy.
    + rewrite homo_cons by auto. rewrite app_length, IH. cbn. enough (|h[a]| = |h[e]|) as -> by lia.
      apply H2. 
Defined. 
      

