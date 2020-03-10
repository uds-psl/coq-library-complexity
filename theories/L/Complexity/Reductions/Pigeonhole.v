Require Import PslBase.Base.
Require Import Lia. 

(** Derivation of the pigeonhole principle on lists *)
(** Adapted from ICL 2019 *)
Notation "x 'nel' A" := (~ In x A) (at level 70).
Section rep.
  Variable (X : Type). 

  Inductive rep : list X -> Prop :=
    repB x A : x el A -> rep (x::A)
  | repS x A : rep A -> rep (x::A).

  (** Inversion lemmas *)

  Fact rep_nil :
    ~ rep [].
  Proof.
    enough (forall A, rep A -> A = [] -> False) by eauto.
    intros A H. destruct H as [x A H|x A H]; intros [=].
  Qed.

  Fact rep_cons x A :
    rep (x::A) -> x el A \/ rep A.
  Proof.
    (* intros H. depelim H; auto. *)
    enough (forall B, rep B -> B = x::A -> x el A \/ rep A) by eauto.
    intros B H.
    destruct H as [y B H|y B H]; intros [= -> ->]; auto 2.
  Qed.

  Fact rep_dupfree_False A :
    rep A -> dupfree A -> False.
  Proof.
    intros H1 H2.
    induction H1 as [x A|x A _ IH].
    - inv H2. intuition.
    - inv H2. auto 2.
  Qed.

  Context (eqdec : (forall x y: X, dec (x = y))).

  Fact mem_dec (x:X) A :
    dec (x el A).
  Proof.
    apply In_dec, eqdec.
  Qed.

  Fact rep_plus_nrep A :
    rep A + dupfree A.
  Proof.
    induction A as [|x A [IH|IH]].
    - right. constructor.
    - left. constructor 2. exact IH.
    - destruct (mem_dec x A) as [H1|H1].
      + left. constructor 1. exact H1.
      + right. constructor 2; trivial.
  Qed.

  Goal forall A, dec (rep A).
  Proof.
    intros A.
    generalize (rep_plus_nrep A), (@rep_dupfree_False A).
    unfold dec. tauto.
  Qed.

  Fact dupfree_not_rep A :
    dupfree A <-> ~rep A.
  Proof.
    generalize (rep_plus_nrep A), (@rep_dupfree_False A).
    tauto.
  Qed.

  Fact not_dupfree_rep A :
    not (dupfree A) <-> rep A.
  Proof. 
    generalize (rep_plus_nrep A), (@rep_dupfree_False A); tauto. 
  Qed. 
   
  Fact mem_sigma (x : X) A :
    x el A -> {A1&{A2| A=A1++x::A2 }}.
  Proof.
    intros H.
    induction A as [|y A IH].
    - contradict H.
    - destruct (eqdec x y) as [<-|H1].
      + exists [], A. reflexivity.
      + destruct IH as (A1&A2&IH).
        * destruct H as [<-|H]; intuition.
        * exists (y::A1), A2. rewrite IH. reflexivity.
  Qed.

  Fact rep_sigma A :
    rep A -> {A1&{x&{A2&{A3| A=A1++x::A2++x::A3 }}}}.
  Proof.
    induction A as [|x A IH]; cbn.
    - intros H. exfalso. inv H.  (* intros []%rep_nil. *)
    - intros H.
      destruct (mem_dec x A) as [(A1&A2&H1)%mem_sigma|H1].
      + rewrite H1. exists [], x, A1, A2. reflexivity.
      + destruct IH as (A1&y&A2&A3&IH).
        * inv H; intuition. 
        *  rewrite IH. exists (x::A1), y, A2, A3. reflexivity.
  Qed.

  Fixpoint card A : nat :=
    match A with
      [] => 0
    | x:: A' => if mem_dec x A' then card A' else S (card A')
    end.

  Fact card_length A :
    card A <= length A.
  Proof.
    induction A as [|x A IH]; cbn.
    - lia.
    - destruct (mem_dec x A) as [H|H]; lia.
  Qed.
 
  Fact rep_card_length A :
    rep A <-> card A < length A.
  Proof.
    split.
    - induction 1 as [x A H|x A _ IH]; cbn;
        destruct (mem_dec x A) as [H1|H1].
      + generalize (card_length A). lia.
      + exfalso. auto 3.
      + generalize (card_length A). lia.
      + lia.
    - induction A as [|x A IH]; cbn.
      + intros H. exfalso. lia.
      + destruct (mem_dec x A) as [H|H].
        * intros _. constructor 1. exact H.
        * intros H1. constructor 2. apply IH. lia.
  Qed.
 
  Fact nrep_card_length A :
    dupfree A <-> card A = length A.
  Proof.
    (* Note the use of setoid rewriting *)
    rewrite dupfree_not_rep, rep_card_length.
    generalize (card_length A). lia. 
  Qed.

  (** Extensionality of Cardinality *)
  
  Fixpoint rem A x : list X :=
    match A with
      [] => []
    | y::A' => if eqdec y x then rem A' x else y::rem A' x
    end.

  Fact rem_el A x y :
    x el rem A y <-> x el A /\ x<> y.
  Proof.
    induction A as [|z A IH].
    - cbn. tauto.
    - cbn [rem].
      destruct (eqdec z y) as [<-|H]; cbn;
        intuition; congruence.
  Qed.

  Fact rem_nel_eq A x :
    x nel A -> rem A x = A.
  Proof.
    induction A as [|y A IH]; cbn.
    - intros _. reflexivity.
    - destruct (eqdec y x) as [<-|H].
      + intros []. now left.
      + intros H1. f_equal. tauto.
  Qed.

  Fact rem_cons_eq x A :
    rem (x :: A) x = rem A x.
  Proof.
    cbn. destruct (eqdec x x) as [_|H]; tauto.
  Qed.

  Fact rem_cons_eq' x y A :
    x <> y -> rem (y::A) x = y::rem A x.
  Proof.
    cbn. destruct (eqdec y x) as [<-|H]; tauto.
  Qed.

  Fact card_el_eq x A :
    x el A -> card (x::A) = card A.
  Proof.
    cbn. destruct (mem_dec x A) as [H|H]; tauto.
  Qed.

  Fact card_nel_eq x A :
    x nel A -> card (x::A) = S (card A).
  Proof.
    cbn. destruct (mem_dec x A) as [H|H]; tauto.
  Qed.

  Fact card_rem_eq A x :
    x el A -> card A = S (card (rem A x)).
  Proof.
    induction A as [|y A IH].
    - intros [].
    - destruct (eqdec x y) as [<-|H1].
      + intros _.
        rewrite rem_cons_eq.
        destruct (mem_dec x A) as [H1|H1].
        * rewrite (card_el_eq H1). exact (IH H1).
        * rewrite (rem_nel_eq H1). apply card_nel_eq, H1.
      + intros [<-|H2].
        { exfalso. auto. }
        rewrite (rem_cons_eq' _ H1).
        destruct (mem_dec y A) as [H3|H3].
        * rewrite (card_el_eq H3).
          rewrite card_el_eq. exact (IH H2).
          apply rem_el. auto.
        * rewrite (card_nel_eq H3). f_equal.
          rewrite card_nel_eq. exact (IH H2).
          contradict H3. apply rem_el in H3. tauto.
  Qed.

  Notation "A <<= B" := (incl A B) (at level 70).

  Fact card_incl A B :
    A <<= B -> card A <= card B.
  Proof.
    induction A as [|x A IH] in B |-*.
    - cbn. lia.
    - intros H. cbn.
      destruct (mem_dec x A) as [H1|H1].
      + apply IH. intros z H2. apply H. now right.
      + enough (card A <= card (rem B x)) as H2.
        { erewrite (@card_rem_eq B x). lia. apply H. now left. }
        apply IH. intros z H3. apply rem_el.
        split.
        * apply H. now right.
        * intros ->. auto.
  Qed.

  Lemma pigeonhole (l1 l2 : list X) : l1 <<= l2 -> |l2| < |l1| -> rep l1. 
  Proof. 
    intros.
    apply card_incl in H. apply rep_card_length.
    specialize (card_length l1) as H1. 
    specialize (card_length l2) as H2. 
    lia. 
  Qed. 

  Lemma pigeonhole' (l1 l2 : list X) : l1 <<= l2 -> |l2| < |l1| -> not (dupfree l1). 
  Proof. 
    intros H1 H2. eapply not_dupfree_rep, pigeonhole; eauto.
  Qed. 
End rep.
