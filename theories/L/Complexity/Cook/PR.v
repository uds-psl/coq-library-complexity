From PslBase Require Import Base. 
From PslBase Require Import Vectors.Vectors. 
From PslBase Require Import FiniteTypes. 
Require Import Lia.
From Undecidability Require Import L.Complexity.Cook.Prelim.

Record PRWin (Sigma : Type):= {
                                prem : list Sigma;
                                conc : list Sigma
                              }.

Record PR := {
               Sigma : finType;
               offset : nat; 
               width : nat;  
               init : list Sigma;  (* length is encoded implicitly as the length of init*) (*length should be a multiple of offset *)
               windows : list (PRWin Sigma);
               final : list (list Sigma);
               steps : nat
             }.

Definition PRWin_of_size (X : Type) (win : PRWin X) (k : nat) := |prem win| = k /\ |conc win| = k. 

Definition PRWin_of_size_dec (X : Type) width (win : PRWin X) := Nat.eqb (|prem win|) width && Nat.eqb (|conc win|) width.
Lemma PRWin_of_size_dec_correct (X : Type) width (win : PRWin X) : PRWin_of_size_dec width win = true <-> PRWin_of_size win width. 
Proof. 
  unfold PRWin_of_size, PRWin_of_size_dec. rewrite andb_true_iff. rewrite <- !(reflect_iff _ _ (Nat.eqb_spec _ _ )). easy.
Qed. 

Definition PR_wellformed (c : PR) := 
  width c > 0 
  /\ offset c > 0
  /\ (exists k, k > 0 /\ width c = k * offset c) (*instances not satisfying this property are wonderfully unintuitive *)
  /\ length (init c) >= width c (*we do not want vacuous rewrites *)
  /\ (forall win, win el windows c -> PRWin_of_size win (width c)) 
  /\ (exists k, length (init c) = k * offset c).

Definition PR_wf_dec (pr : PR) := 
  leb 1 (width pr) 
  && leb 1 (offset pr)
  && Nat.eqb (Nat.modulo (width pr) (offset pr)) 0
  && leb (width pr) (|init pr|)
  && forallb (PRWin_of_size_dec (width pr)) (windows pr)
  && Nat.eqb (Nat.modulo (|init pr|) (offset pr)) 0.
 

Lemma PR_wf_dec_correct (pr : PR) : PR_wf_dec pr = true <-> PR_wellformed pr. 
Proof. 
  unfold PR_wf_dec, PR_wellformed. rewrite !andb_true_iff, !and_assoc.
  rewrite !leb_iff. rewrite <- !(reflect_iff _ _ (Nat.eqb_spec _ _ )).  
  rewrite !forallb_forall. 
  setoid_rewrite PRWin_of_size_dec_correct.  
  split; intros; repeat match goal with [H : _ /\ _ |- _] => destruct H end; 
  repeat match goal with [ |- _ /\ _ ] => split end; try easy. 
  - apply Nat.mod_divide in H1 as (k & H1); [ | lia]. 
    exists k; split; [ | apply H1 ]. destruct k; cbn in *; lia.
  - apply Nat.mod_divide in H4 as (k & H4); [ | lia].  exists k; apply H4.  
  - apply Nat.mod_divide; [ lia | ]. destruct H1 as (k & _ & H1). exists k; apply H1.
  - apply Nat.mod_divide; [ lia | ]. apply H4. 
Qed. 


(**we do some general definitions first which can be reused for the flat version *)
Section fixX. 
  Variable (X : Type).
  Variable (offset : nat). 
  Variable (width : nat).
  Variable (windows : list (PRWin X)). 

  Context (G0 : width > 0).
  (*Context (exists k, length (init) = k * offset).*)

  (* the final constraint*)
  (* this is defined in terms of the offset: there must exist an element of a list of strings final which is a substring of the the string s at a multiple of offset *)
  Definition satFinal l (final : list (list X)) s := 
    exists subs k, subs el final /\ k * offset <= l /\  prefix subs (skipn (k * offset) s).

  (* rewrites inside a string *)
  Definition rewritesHead (X : Type) (win : PRWin X) a b := prefix (prem win) a /\ prefix (conc win) b.

  Definition rewritesAt (win : PRWin X) (i : nat) a b := rewritesHead win (skipn i a) (skipn i b).
  Lemma rewritesAt_head win a b : rewritesHead win a b <-> rewritesAt win 0 a b. 
  Proof. 
    unfold rewritesAt.
    rewrite <- firstn_skipn with (n:= 0) (l:= a) at 1.
    rewrite <- firstn_skipn with (n:= 0) (l:= b) at 1.
    repeat rewrite firstn_O; now cbn. 
  Qed. 

  Lemma rewritesAt_step (win : PRWin X) a b u v (i:nat) : length u = offset -> length v = offset -> rewritesAt win i a b <-> rewritesAt win (i + offset) (u ++ a) (v ++ b). 
  Proof.
    intros. unfold rewritesAt.
    rewrite Nat.add_comm. now repeat rewrite skipn_add. 
  Qed. 

  (*validity of a rewrite *)
  Inductive valid: list X -> list X -> Prop :=
  | validB: valid [] [] 
  | validSA a b u v : valid a b -> length a < width - offset -> length u = offset -> length v = offset -> valid (u++ a) (v++ b)
  | validS a b u v win: valid a b -> length u = offset -> length v = offset -> win el windows -> rewritesHead win (u ++ a) (v ++ b) -> valid (u ++ a) (v ++ b). 

  Lemma valid_length_inv a b : valid a b -> length a = length b. 
  Proof.
    induction 1. 
    - now cbn.
    - repeat rewrite app_length. firstorder. 
    - repeat rewrite app_length; firstorder. 
  Qed. 

  Lemma relpower_valid_length_inv k a b : relpower valid k a b -> length a = length b. 
  Proof. 
    induction 1; [ auto | rewrite <- IHrelpower; now apply valid_length_inv]. 
  Qed. 

  Lemma valid_vacuous (a b : list X) m: |a| = |b| -> |a| < width -> |a| = m * offset -> valid a b.
  Proof. 
    clear G0. 
    revert a b. induction m; intros.  
    - cbn in H1. destruct a; [ | cbn in H1; congruence]. destruct b; [ | cbn in H; congruence ].  constructor. 
    - cbn in H1. assert (offset <= |a|) by lia. apply list_length_split1 in H2 as (s1 & s2 & H3 & H4 & H5).  
      assert (offset <= |b|) by lia. apply list_length_split1 in H2 as (s3 & s4 & H6 & H7 & H8). 
      rewrite H5, H8. constructor 2. 
      + subst. apply IHm. 
        * rewrite !app_length in H. lia. 
        * rewrite app_length in H0. lia. 
        * rewrite app_length in *. lia. 
      + lia. 
      + lia. 
      + lia.  
  Qed. 

  Lemma valid_multiple_of_offset a b : valid a b -> exists k, |a| = k * offset.
  Proof. 
    induction 1. 
    - exists 0; now cbn. 
    - setoid_rewrite app_length. destruct IHvalid as (k & ->).  exists (S k); nia. 
    - setoid_rewrite app_length. destruct IHvalid as (k & ->).  exists (S k); nia. 
  Qed. 

  Definition validExplicit a b := length a = length b 
    /\ (exists k, length a = k * offset) 
    /\ forall i, 0 <= i < length a + 1 - width 
      /\ (exists j, i = j * offset) -> exists win, win el windows 
      /\ rewritesAt win i a b.

  Lemma valid_iff a b :
    valid a b <-> validExplicit a b.
  Proof.
    unfold validExplicit. split.
    - induction 1.
      + split; [now cbn |split; [now exists 0 | ] ]. intros. cbn [length] in H. lia.  
      + specialize (valid_length_inv H) as H'. split; [ repeat rewrite app_length; now rewrite H', H1, H2 | ].
        destruct IHvalid as (IH1 & IH2 & IH3). 
        split.
        1: { destruct IH2 as (k & IH2). exists (S k). rewrite app_length; lia. }
        rewrite app_length; intros. lia. 
      + destruct IHvalid as (IH1 & IH2 & IH3). split; [repeat rewrite app_length; firstorder | ].  
        split.
        1: { destruct IH2 as (k & IH2). exists (S k). rewrite app_length; lia. }
        rewrite app_length. intros i (iH1 & (j & iH2)). destruct j. 
        * exists win. split; [assumption | ]. rewrite Nat.mul_0_l in iH2. rewrite iH2 in *. now rewrite <- rewritesAt_head.  
        * cbn in iH2. assert (0 <= i - offset < (|a|) + 1 - width) by lia.
          assert (exists j, i - offset = j * offset) by (exists j; lia). 
          specialize (IH3 (i -offset) (conj H4 H5)) as (win' & F1 & F2). 
          exists win'; split; [assumption | ]. rewrite (@rewritesAt_step win' a b u v (i -offset) H0 H1) in F2. rewrite Nat.sub_add in F2; [assumption | lia]. 
    - intros (H1 & (k & H2) & H3). revert a b H1 H2 H3. induction k; intros. 
      + rewrite Nat.mul_0_l in H2; rewrite H2 in *. inv_list. constructor.
      + cbn in H2. rewrite H2 in H1; symmetry in H1.
        apply length_app_decompose in H2 as (u & a' & -> & H2 & H4).
        apply length_app_decompose in H1 as (v & b' & -> & H1 & H5). 
        destruct (le_lt_dec (width - offset) (length a')). 
        * (*have to find a window to apply*)
          rewrite app_length in H3. 
          assert (0 <= 0 < (|u|) + (|a'|) + 1 - width) by lia. 
          assert (exists j, 0 = j * offset) as H' by (exists 0; lia). 
          destruct (H3 0 (conj H H')) as (win & F1 & F2%rewritesAt_head). 
          eapply (@validS a' b' u v win). 2-5: assumption. 
          apply IHk; [lia | apply H4 | ]. 
          intros i (H0 & (j & H6)). assert (0 <= i + (|u|) < (|u|) + (|a'|) + 1 - width) by lia. 
          assert (exists j, i + (|u|) = j * offset) by (exists (S j); lia). 
          destruct (H3 (i + (|u|)) (conj H7 H8)) as (win' & F3 & F4). 
          exists win'; split; [assumption | ]. 
          rewrite H2 in F4. now apply (proj2 (@rewritesAt_step win' a' b' u v (i ) H2 H1)) in F4. 
        * (* the rewrite is vacuously valid *)
          constructor.
          2-4: assumption. 
          apply IHk; [congruence | assumption | ]. 
          intros i (F1 & (j & F2)). rewrite app_length in H3. 
          assert (0 <= i + (|u|) < (|u|) + (|a'|) + 1 - width) by lia.
          assert (exists j, i + (|u|) = j * offset) by (exists (S j); lia). 
          destruct (H3 (i + (|u|)) (conj H H0)) as (win & H6 & H7). 
          exists win; split; [assumption | ]. 
          rewrite H2 in H7. now apply (proj2 (@rewritesAt_step win a' b' u v i H2 H1)) in H7. 
  Qed. 
End fixX. 

Implicit Type (C : PR).

Section fixInstance.
  Variable (c : PR). 
  Context (wf : PR_wellformed c). 

  Notation string := (list (Sigma c)).
  Definition window := PRWin (Sigma c). 

  Implicit Type (s a b: string). 
  Implicit Type (win : window).
  Implicit Type (x y : Sigma c).

  Definition isRule r := r el windows c.
  Lemma isRule_length r : isRule r -> length (prem r) = width c /\ length (conc r) = width c.
  Proof. 
    intros. destruct wf as (_ & _ & _ & _ & H1 & _). specialize (H1 r H ) as (H1 & H2). tauto. 
  Qed. 

  Lemma rewritesHead_length_inv win a b : rewritesHead win a b -> isRule win -> length a >= width c /\ length b >= width c. 
  Proof. 
    intros. unfold rewritesHead, prefix in *. destruct H as ((b1 & ->) & (b2 & ->)). split.  
    - rewrite app_length. rewrite (proj1 (isRule_length H0)). lia.  
    - rewrite app_length, (proj2 (isRule_length H0)). lia. 
  Qed. 
End fixInstance. 

Definition PRLang (C : PR) := PR_wellformed C /\ exists (sf : list (Sigma C)), relpower (valid (offset C) (width C) (windows C)) (steps C) (init C) sf /\ satFinal (offset C) (|init C|) (final C) sf. 

(*we consider equivalent instances: equivalent instances are obtained by reordering the windows and final substrings *)

Hint Constructors valid. 
Lemma valid_windows_monotonous (X : Type) (offset width : nat) (a b : list X) (w1 w2 : list (PRWin X)) : 
  w1 <<= w2
  -> valid offset width w1 a b -> valid offset width w2 a b.
Proof. 
  intros. induction H0. 
  - eauto. 
  - eauto. 
  - apply H in H3. eauto. 
Qed. 

Lemma valid_windows_equivalent (X : Type) (offset width : nat) (a b : list X) (w1 w2 : list (PRWin X)) : 
  w1 === w2 
  -> valid offset width w1 a b <-> valid offset width w2 a b.
Proof. 
  intros [H1 H2]; split; now apply valid_windows_monotonous. 
Qed. 

Lemma satFinal_final_monotonous (X : Type) (offset l : nat) (f1 f2 : list (list X)) s: 
  f1 <<= f2 -> satFinal offset l f1 s -> satFinal offset l f2 s. 
Proof. 
  intros. destruct H0 as (subs & k & H1 & H2 & H3).
  exists subs, k. apply H in H1. easy.
Qed. 

Lemma satFinal_final_equivalent (X : Type) (offset l : nat) (f1 f2 : list (list X)) s: 
  f1 === f2 -> satFinal offset l f1 s <-> satFinal offset l f2 s. 
Proof. 
  intros [H1 H2]; split; now apply satFinal_final_monotonous. 
Qed. 


