Require Import PslBase.Base.
Require Import Lia. 
From Undecidability.L Require Import L.
From Undecidability.Shared Require Import Prelim.
From Undecidability.L.Complexity Require Import Tactics.

Section pair_eq.
  Variable (X Y : Type). 
  Variable  (eqbX : X -> X -> bool) (eqbY : Y -> Y -> bool). 
  Variable (eqbX_correct : forall a b, a = b <-> eqbX a b = true).
  Variable (eqbY_correct : forall a b, a = b <-> eqbY a b = true).

  Definition pair_eqb (a b : (X * Y)%type) : bool :=
    match a, b with (x1, y1), (x2, y2) => eqbX x1 x2 && eqbY y1 y2 end. 

  Lemma pair_eqb_correct a b : a = b <-> pair_eqb a b = true.
  Proof.
    destruct a, b. split. 
    + intros H. cbn. apply andb_true_intro; split.
      apply eqbX_correct; congruence. apply eqbY_correct; congruence. 
    + intros [H1 H2]%andb_prop. apply eqbX_correct in H1. apply eqbY_correct in H2. congruence. Qed. 
End pair_eq. 

(** *Results regarding lists *)

Section takeN.
  Variable (X : Type).
  Fixpoint takeN (l : list X) (n : nat) {struct n} :=
    match n with 0 => []
               | S n => match l with [] => []
                           | (l :: ls) => l :: takeN ls n
                        end
    end. 

  Lemma ntherror_sublist (l l' : list X) (k : nat) (x : X) : (nth_error l k = Some x) -> nth_error (l ++ l') k = Some x. 
  Proof. 
    revert k. 
    induction l. 
    - intros []; cbn; congruence.  
    - intros k H. destruct k.
      + cbn in H. destruct l'; now cbn.
      + cbn. apply IHl. now cbn in H. 
  Qed. 

  Lemma nth_error_nth (l : list X) (def res: X) (k : nat) : nth_error l k = Some res -> nth k l def = res. 
  Proof.
    revert k.
    induction l.
    - destruct k; cbn; congruence. 
    - destruct k; cbn. 
      + congruence. 
      + intros. now apply IHl. 
  Qed. 

  Lemma takeN_sublist (l : list X) (k k' : nat) (t : list X) : takeN l k = t -> k' >= k -> exists t', takeN l k' = t ++ t'. 
  Proof. 
    revert k k' t. induction l. 
    - intros k k' t H1 H2. exists []. destruct k', k; cbn in H1; cbn; rewrite <- H1; firstorder. 
    - intros k k' t H1 H2. destruct k, k'; cbn in H1; cbn; try rewrite <- H1. firstorder.
      exists (a :: takeN l k'). firstorder. lia.
      destruct t; try congruence. 
      specialize (IHl k k' t). inv H1.  destruct (IHl); try tauto; try lia. exists x0. cbn. now rewrite <- H. 
  Qed. 

  Lemma takeN_more_length (l : list X) (k : nat) : k >= (|l|) ->  takeN l k = l. 
  Proof. 
    revert k. induction l. 
    - intros k. cbn. destruct k; tauto. 
    - intros k. cbn. destruct k; cbn. lia. intros H. rewrite IHl. reflexivity. lia. 
  Qed. 

  Lemma takeN_split (l : list X) (k : nat) : exists t, l = takeN l k ++ t.
  Proof.
    enough (exists t, takeN l (|l|) = takeN l k ++ t). 
    { destruct H. specialize (@takeN_more_length l (|l|)) as H2. exists x. rewrite <- H, H2; [reflexivity | lia]. }
    destruct (lt_eq_lt_dec k (|l|)) as [[H|H] |H].
    1-2: apply takeN_sublist with (k:=k); try reflexivity; try lia.  
    exists []. repeat rewrite takeN_more_length. firstorder. all: lia.
  Qed. 

  Lemma takeN_length (l :list X) (k : nat) : (|takeN l k|) <= k. 
  Proof. 
    induction l in k |-*. 
    - destruct k; cbn; lia. 
    - destruct k; cbn; try lia. rewrite IHl. lia. 
  Qed. 

  Lemma takeN_minlength (l : list X) (n k : nat) : |l| >= k -> n >= k -> |takeN l n| >= k. 
  Proof. 
    induction l in n, k |-*. 
    - destruct n; cbn; lia.
    - cbn. destruct n, k; cbn. 1-3: lia.
      intros H1 H2. enough (|takeN l n| >= k) by lia. apply IHl; lia.  
  Qed. 

  Lemma ntherror_take (l : list X) (k n : nat) (v :X) : k < n -> nth_error l k = Some v -> nth_error (takeN l n) k = Some v. 
  Proof. 
    specialize (takeN_split l n) as [t H]. intros H1 H2. 
    (*Proof by contradiction*)
    destruct (nth_error (takeN l n) k) eqn:H3. 
    2: { exfalso. 
        apply nth_error_None in H3. assert (|l| > k) by (now apply nth_error_Some_lt with (x := v)).
        (*contradiction by H1, H3, H0 *)
        destruct (takeN_split l k) as [[] H4].
        - enough (|l| = k) by lia. rewrite H4. enough (|takeN l k| <= k /\ |takeN l k| >= k).
          {replace (takeN l k ++ []) with (takeN l k) by firstorder. lia. }
          split. apply takeN_length. apply takeN_minlength. all: lia. 
        - assert (|takeN l n| = k). enough (|takeN l n| >= k) by lia. apply takeN_minlength; lia. 
          assert (|takeN l n| >= S k). apply takeN_minlength; lia. lia. 
    }
    rewrite H in H2. specialize(Prelim.nthe_app_l t H3) as H4. now rewrite H4 in H2. 
  Qed. 
End takeN.

Section tabulate.
  Variable (A : Type).
  Fixpoint tabulate (f : nat -> A) (n : nat): list A := match n with 0 => []
                                                                      | S n => tabulate f n ++ [f n]
                                                                end. 

  Lemma tabulate_length (f : nat -> A)  (n : nat) : |tabulate f n| = n. 
  Proof. 
    induction n; cbn.
    - reflexivity. 
    - rewrite app_length, IHn. cbn;lia. 
  Qed. 

  Lemma tabulate_nth (f : nat -> A) (n : nat) : forall k, k < n -> nth_error (tabulate f n) k = Some (f k). 
  Proof.
    intros. induction n. 
    - lia. 
    - destruct (Nat.eqb k n) eqn:H1; dec_bool.
      + rewrite H1 in *; clear H1. cbn. rewrite nth_error_app2, tabulate_length. 2: specialize (tabulate_length f n); lia. 
        rewrite Nat.sub_diag; cbn; reflexivity.  
      + assert (k < n) by lia. clear H1 H. cbn. rewrite nth_error_app1. 2: now rewrite tabulate_length. 
        now apply IHn. 
  Qed. 

  Lemma tabulate_In (f : nat -> A) (n : nat) : forall a, a el tabulate f n <-> exists k, k < n /\ f k = a. 
  Proof.
    specialize (@tabulate_nth f n) as H1. 
    intros a. split.
    - intros (n0 & H2)%In_nth_error.
      assert (n0 < n). { rewrite <- tabulate_length with (f := f). now apply nth_error_Some_lt with (x:=a). }
      exists n0. split; [assumption|]. 
      specialize (H1 n0 H). congruence. 
    - intros (k & H2 & H3). specialize (H1 k H2).  
      rewrite <- H3; eapply nth_error_In, H1. 
  Qed. 
End tabulate. 


Section subsequence.
  Variable (X : Type).
  Definition subsequence (A B : list X) := exists C D, B = C ++ A ++ D.
  Notation "A 'subs' B" := (subsequence A B)(at level 70).

  Lemma subsequence_incl (A B : list X) : A subs B -> incl A B.
  Proof. 
    induction B. 
    - unfold subsequence. destruct A; cbn; try firstorder.
      intros (C & D & H). destruct C; cbn in H; congruence.   
    - intros (C & D & H). intros x xel. destruct C. 
      + cbn in H. rewrite H. firstorder. 
      + cbn in H. assert (x0 = a) as -> by congruence.  
        right. apply IHB; [|assumption]. exists C,D. congruence. 
  Qed.
End subsequence. 



Lemma map_el (X Y : Type) (l : list X) (f : X -> Y) (e : Y) : e el (map f l) <-> exists e', e' el l /\ f e' = e. 
Proof.
  induction l. 
  - cbn. split; [intros [] | intros (_ & [] & _)]. 
  - split.
    * intros [H1 | H2].
      + exists a. split; firstorder. 
      + destruct (proj1 IHl H2) as (e' & F1 & F2). exists e'. split; firstorder. 
    * intros (e' & H1 & H2). cbn. destruct H1.
      + rewrite H in *; now left. 
      + right; apply IHl. now exists e'. 
Qed. 

Lemma dupfree_nthe (X : Type) (l : list X) : dupfree l <-> forall i j a b, nth_error l i = Some a -> nth_error l j = Some b -> i <> j -> a <> b.
Proof. 
  split.
  - induction 1. 
    + intros. destruct i; cbn in H; congruence.  
    + intros. destruct i, j. 
      * congruence. 
      * cbn in H1, H2. apply nth_error_In in H2. assert (x = a) by congruence. rewrite H4 in H. congruence. 
      * cbn in H1, H2. apply nth_error_In in H1. assert (x = b) by congruence. rewrite H4 in H. congruence. 
      * cbn in H1, H2. apply IHdupfree with (i:= i) (j:=j); [assumption | assumption | congruence]. 
  - induction l. 
    + intros. constructor. 
    + intros. constructor. 
      * intros Hel%In_nth_error.  destruct Hel as (j & Hel). 
        specialize (H 0 (S j) a a). cbn in H. apply H; firstorder. 
      * apply IHl. firstorder. apply H with (i := S i) (j:= S j); firstorder. 
Qed. 

Section remove.
  Variable (X : Type).
  Context (eqdec : (forall x y: X, dec (x = y))).
  Lemma remove_el (l : list X) (a b : X) : a el remove eqdec b l <-> a el l /\ a <> b.
  Proof.
    revert a.
    induction l; intros; cbn.
    - tauto. 
    - destruct (eqdec b a).
      + split.
        * firstorder. 
        * intros [[-> | H1] H2]; [congruence|]. now apply IHl. 
      + split.
        * firstorder. congruence.  
        * firstorder. 
  Qed. 

  Lemma remove_length (l : list X) (a : X) : |remove eqdec a l| <= |l|.
  Proof.
    induction l; cbn.
    - lia.
    - destruct eqdec; cbn; lia. 
  Qed. 

  Lemma remove_length_el (l : list X) (a : X) : a el l -> |remove eqdec a l| < |l|.
  Proof.
    induction l.
    - intros [].
    - intros [-> | H1].
      + cbn. destruct (eqdec a a); [specialize (remove_length l a); lia | congruence].
      + cbn. destruct (eqdec a a0); [specialize (remove_length l a); lia | cbn; firstorder ].  
  Qed. 
End remove.

