From PslBase Require Import Base. 
From PslBase Require Import Vectors.Vectors. 
From PslBase Require Import FiniteTypes. 
Require Import Lia.
Require Template.utils.
From Undecidability.TM Require Import TM.
From Undecidability.TM Require Import TM.
From Undecidability.L.TM Require Import TMflat TMflatEnc TMflatFun TMEncoding TapeDecode TMunflatten.

Require Import Lia. 


Definition involution (X : Type) (f : X -> X) := forall (x : X), f (f x) = x. 

Lemma map_involution (X : Type)(f : X -> X) : involution f -> involution (map f). 
Proof. 
  intros. intros l. rewrite map_map. setoid_rewrite H. now rewrite map_id. 
Qed. 

Lemma involution_invert_eqn (X : Type) (f : X -> X) : involution f -> forall a b, f a = f b -> a = b. 
Proof. 
  intros. enough (f (f a) = f(f b)). { now rewrite  !H in H1. } now rewrite H0. 
Qed. 

Lemma involution_invert_eqn2 (X : Type) (f : X -> X) : involution f -> forall a b, f a = b -> a = f b. 
Proof. 
  intros. rewrite <- (H a). now apply involution_invert_eqn with (f := f). 
Qed. 

Smpl Create involution.
Ltac involution_simpl := smpl involution; repeat (involution_simpl).

Smpl Add (apply map_involution) : involution.

Lemma rev_involution (X : Type): involution (@rev X).  
Proof. 
  unfold involution. apply rev_involutive. 
Qed. 

Smpl Add (apply rev_involution) : involution. 



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

Lemma firstn_skipn_rev (X : Type) i (h : list X) : firstn i h = rev (skipn (|h| - i) (rev h)). 
Proof. 
  rewrite <- (firstn_skipn i h) at 3. 
  rewrite rev_app_distr.
  rewrite skipn_app. 
  - now rewrite rev_involution.
  - rewrite rev_length. now rewrite skipn_length.
Qed. 

Lemma skipn_firstn_rev (X : Type) i (h : list X) : skipn i h = rev (firstn (|h| - i) (rev h)). 
Proof. 
  intros. 
  destruct (le_lt_dec i (|h|)). 
  - rewrite firstn_skipn_rev. 
    rewrite !rev_involution.
    rewrite rev_length.
    replace ((|h|) - (|h| - i)) with i by  lia. easy. 
  - specialize (skipn_length i h) as H1. assert (|skipn i h| = 0) by lia. 
    specialize (firstn_le_length (|h| - i) (rev h)) as H2. assert (|firstn (|h| - i) (rev h)| = 0)  as H3 by lia. 
    destruct skipn, firstn; cbn in *; try congruence. 
Qed. 

Lemma map_firstn (X Y : Type) i (h : list X) (f : X -> Y) : map f (firstn i h) = firstn i (map f h). 
  revert i; induction h; intros; cbn. 
  - now rewrite !firstn_nil. 
  - destruct i; cbn; [reflexivity | now rewrite IHh].
Qed.

Lemma map_skipn (X Y : Type) i (h : list X) (f : X -> Y) : map f (skipn i h) = skipn i (map f h). 
  revert i; induction h; intros; cbn. 
  - now rewrite !skipn_nil. 
  - destruct i; cbn; [reflexivity | now rewrite IHh ]. 
Qed.


Lemma length_app_decompose (X : Type) (a : list X) i j : length a = i + j -> exists a1 a2, a = a1 ++ a2 /\ length a1 = i /\ length a2 = j. 
Proof. 
  revert a. 
  induction i. 
  - cbn. intros. now exists [], a. 
  - cbn. intros. 
inv_list. assert (|a| = i + j) by lia. destruct (IHi a H0) as (a1 & a2 & H2 & H3). 
    exists (x :: a1), a2. firstorder. 
Qed. 


Inductive relpowerRev (X : Type) (R : X -> X -> Prop) : nat -> X -> X -> Prop :=
| relpowerRevB x : relpowerRev R 0 x x
| relpowerRevS x y y' n: relpowerRev R n x y -> R y y' -> relpowerRev R (S n) x y'. 
Hint Constructors relpowerRev. 

Inductive relpower (A : Type) (R : A -> A -> Prop) : nat -> A -> A -> Prop :=
| relpowerB (a : A) : relpower R 0 a a
| relpowerS (a b c : A) n : R a b -> relpower R n b c -> relpower R (S n) a c. 
Hint Constructors relpower.

Lemma relpower_trans A R n m (x y z : A) : relpower R n x y -> relpower R m y z -> relpower R (n + m) x z.
Proof. 
  induction 1. 
  - now cbn. 
  - intros. apply relpowerS with (b := b). assumption. now apply IHrelpower. 
Qed. 

Lemma relpower_monotonous (X : Type) (R1 R2 : X -> X -> Prop) : (forall a b, R1 a b -> R2 a b) -> forall n a b, relpower R1 n a b -> relpower R2 n a b.
Proof. 
  intros H1 n a b. induction 1. 
  - eauto. 
  - apply H1 in H. eauto. 
Qed.

Lemma relpower_congruent (X : Type) (R R': X -> X -> Prop) :
  (forall x y, R x y <-> R' x y) -> forall n x y, relpower R n x y <-> relpower R' n x y. 
Proof. 
  intros H. induction n. 
  - split; intros H0; inv H0; eauto. 
  - split; intros H0; inv H0.
    + apply H in H2. apply IHn in H3. eauto. 
    + apply H in H2. apply IHn in H3. eauto. 
Qed. 

Lemma relpowerRev_trans (X : Type) (R : X -> X -> Prop) n m x y z : relpowerRev R n x y -> relpowerRev R m y z -> relpowerRev R (n + m) x z.
Proof. 
  rewrite Nat.add_comm. induction 2; cbn; eauto. 
Qed. 

Lemma relpower_relpowerRev (X : Type) (R : X -> X -> Prop) n x y : relpower R n x y <-> relpowerRev R n x y.
Proof. 
  split; induction 1; eauto. 
  - replace (S n) with (1 + n) by lia. eauto using relpowerRev_trans. 
  - replace (S n) with (n + 1) by lia. eauto using relpower_trans. 
Qed. 

Notation injective := Prelim.Injective.

Lemma getPosition_map (X Y : eqType) (f : X -> Y) (l : list X) (x : X) : injective f -> getPosition (map f l) (f x) = getPosition l x. 
Proof.
  intros.
  induction l; cbn. 
  - reflexivity. 
  - destruct Dec; destruct Dec; try congruence.
    now apply H in e.
Qed. 

Lemma getPosition_app1 (X : eqType) (A B : list X) x k : k < |A| -> getPosition A x = k -> getPosition (A ++ B) x = k.
Proof.
  revert k. induction A; intros; cbn in *.
  - lia. 
  - destruct Dec; [assumption | destruct k; [ lia | erewrite IHA]]. 
    + reflexivity. 
    + lia. 
    + easy. 
Qed. 

Lemma getPosition_app2 (X : eqType) (A B : list X) x k : k < |B| -> not (x el A) -> getPosition B x = k -> getPosition (A ++ B) x = |A| + k. 
Proof. 
  revert k. induction A; intros; cbn in *. 
  - apply H1. 
  - destruct Dec; [ exfalso ; auto | ]. 
    erewrite IHA; eauto. 
Qed. 


Lemma prodLists_length (X Y : Type) (A : list X) (B : list Y) : |prodLists A B| = |A| * |B|. 
Proof.
  induction A; cbn. 
  - reflexivity.
  - rewrite app_length. rewrite map_length, IHA. lia. 
Qed. 

Lemma in_prodLists_iff (X Y : Type) (A : list X) (B : list Y) a b : (a, b) el prodLists A B <-> a el A /\ b el B. 
Proof. 
  induction A; cbn.
  - tauto.
  - split; intros.
    + apply in_app_iff in H. destruct H as [H | H].
      * apply in_map_iff in H; destruct H as (? & H1 & H2). inv H1. auto. 
      * apply IHA in H. tauto. 
    + destruct H as [[H1 | H1] H2].
      * apply in_app_iff. left. apply in_map_iff. exists b. firstorder. 
      * apply in_app_iff. right. now apply IHA. 
Qed. 

Lemma getPosition_prodLists (X Y : eqType) (A : list X) (B : list Y) x1 x2 k1 k2 : getPosition A x1 = k1 -> k1 < |A| -> getPosition B x2 = k2 -> k2 < |B| -> getPosition (prodLists A B) (x1, x2) = (k1 * |B|) + k2. 
Proof. 
  revert k1. induction A; intros; cbn in *. 
  - lia. 
  - destruct k1. 
    + destruct Dec; [ | congruence].
      rewrite getPosition_app1 with (k := k2); [reflexivity | now rewrite map_length| ].
      rewrite e; now rewrite getPosition_map. 
    + destruct Dec; [ congruence | ]. 
      rewrite getPosition_app2 with (k := (k1 * |B|) + k2). 
      * rewrite map_length. lia. 
      * setoid_rewrite prodLists_length. nia. 
      * intros (? & ? &?)%in_map_iff. congruence. 
      * apply IHA; eauto. lia.  
Qed. 

Fixpoint filterSome (X : Type) (l : list (option X)) := match l with
                                                        | [] => []
                                                        | (Some x :: l) => x :: filterSome l
                                                        | None :: l => filterSome l
                                                        end. 

Lemma in_filterSome_iff (X : Type) (l : list (option X)) a:
  a el filterSome l <-> Some a el l.
Proof.
  induction l as [ | []]; cbn.  
  - tauto.
  - split.
    + intros [-> | H]; [eauto | right; now apply IHl]. 
    + intros [H1 | H]; [eauto | ]. inv H1. 
      * eauto. 
      * right; now apply IHl. 
  - rewrite IHl. split; intros H; [ eauto | now destruct H]. 
Qed. 


Lemma nth_error_nth (X : Type) x (l : list X) n : nth_error l n = Some x -> nth n l x = x.  
Proof. 
  revert n; induction l; intros; cbn. 
  - now destruct n. 
  - destruct n; cbn in H.
    * congruence. 
    * now apply IHl. 
Qed.

Lemma In_explicit (X : Type) (x : X) (l : list X) :
  x el l <-> exists s1 s2, l = s1 ++ [x] ++ s2. 
Proof. 
  induction l; cbn. 
  - split; [tauto | intros (s1 & s2 & H)].
    destruct s1; cbn in H; congruence. 
  - split. 
    + intros [-> | (s1 & s2 & ->)%IHl]. 
      * exists [], l. eauto. 
      * exists (a :: s1), s2; eauto. 
    + intros ([] & s2 & H). 
      * inv H. eauto. 
      * inv H. right; apply IHl.
        exists l0, s2. eauto. 
Qed. 

(*repeat an element *)
Fixpoint repEl (X : Type) n (e : X) := 
 match n with 
 | 0 => []
 | S n => e :: repEl n e
end. 

Lemma repEl_length (X : Type) n (e : X) : |repEl n e| = n. 
Proof. induction n; cbn; eauto. Qed. 

Lemma map_repEl (X Y : Type) (f : X -> Y) n (e : X) : map f (repEl n e) = repEl n (f e). 
Proof. induction n; cbn; [eauto | congruence]. Qed. 

Lemma repEl_add (X : Type) (a : X) n1 n2: repEl (n1 + n2) a = repEl n1 a ++ repEl n2 a.
Proof.  induction n1; cbn; [eauto | congruence]. Qed. 

Lemma list_length_split1 (X : Type) (s : list X) n : n <= |s| -> exists s1 s2, |s1| = n /\ |s2| = |s| - n /\ s = s1 ++ s2. 
Proof. 
  revert s. induction n; intros. 
  - exists [], s. cbn; rewrite Nat.sub_0_r. eauto. 
  - destruct s; cbn in H; [lia | ]. assert (n <= |s|) as H' by lia. 
    apply IHn in H' as (s1 & s2 & H1 & H2 & ->). 
    exists (x::s1), s2. cbn. eauto. 
Qed. 

Lemma list_length_split2 (X : Type) (s : list X) n : n <= |s| -> exists s1 s2, |s1| = |s| - n /\ |s2| = n /\ s = s1 ++ s2. 
Proof. 
  intros. assert (|s| - n <= |s|) as H' by lia. 
  specialize (list_length_split1 H') as (s1 & s2 & H1 & H2 & ->). 
  exists s1, s2. 
  rewrite app_length in *.
  repeat split; [lia | lia].
Qed. 

Lemma app_eq_length (X : Type) (s1 s2 w1 w2 : list X) : |s1| = |w1| -> s1 ++ s2 = w1 ++ w2 -> s1 = w1 /\ s2 = w2. 
Proof.
  intros. revert w1 H H0. induction s1; cbn in *; intros. 
  - destruct w1; cbn in *; eauto. 
  - destruct w1; cbn in *; [congruence | ]. inv H0. inv H. 
    specialize (IHs1 w1 H1 H3) as (-> & ->). eauto. 
Qed. 


Lemma S_injective a b : S a = S b -> a = b. 
Proof. congruence. Qed. 

Ltac list_length_inv := repeat match goal with 
    | [H : S _ = |?a| |- _] => is_var a; destruct a; cbn in H; [ congruence | apply S_injective in H]
    | [H : 0 = |?a| |- _] => is_var a; destruct a; cbn in H; [ clear H| congruence]
    | [H : |?a| = _ |- _] => symmetry in H
end.

Lemma list_eq_length (X : Type) (l1 l2 : list X) : l1 = l2 -> |l1| = |l2|. 
Proof. 
  congruence. 
Qed.

Lemma nth_error_step (X : Type) x s (l : list X) a y : x >= S s -> nth_error l (x - S s) = Some a <-> nth_error (y :: l) (x - s) = Some a.
Proof. 
  intros. replace (y :: l) with ([y] ++ l) by now cbn. 
  rewrite nth_error_app2; cbn; [ | lia].
  replace (x - s - 1) with (x - S s) by lia. tauto.
Qed. 
