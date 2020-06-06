From PslBase Require Import FinTypes. 
From Undecidability.L.Complexity.Problems Require Import UGraph. 
Require Import Lia.

Section fixGraph. 
  Variable (g : UGraph). 
  Notation V := (V g).
  Notation E := (@E g).

  Definition isClique (l : list V) := (forall v1 v2, v1 el l -> v2 el l -> v1 <> v2 -> E (v1, v2)) /\ dupfree l. 
  Definition isKClique k (l : list V) := |l| = k /\ isClique l. 

  (** an alternative inductive characterisation *)
  Inductive indKClique : nat -> list V -> Prop := 
    | indKCliqueNil : indKClique 0 []
    | indKCliqueS L v k : indKClique k L -> not (v el L) -> (forall v', v' el L -> E (v, v')) -> indKClique (S k) (v :: L). 
  Hint Constructors indKClique.

  Lemma indKClique_iff k L: isKClique k L <-> indKClique k L. 
  Proof. 
    split.
    - intros [H1 [H2 H3]]. revert L H1 H2 H3. induction k; intros. 
      + destruct L; cbn in H1; [ eauto | congruence].
      + destruct L; cbn in *; [congruence | ].
        constructor.
        * apply IHk; [lia | intros; apply H2; eauto | now inv H3].
        * now inv H3. 
        * intros v' Hel. apply H2; [eauto | eauto | ]. inv H3. intros ->. congruence.
    - induction 1 as [ | ? ? ? ? IH]. 
      + split; [ | split]; [now cbn | intros ? ? [] | constructor].
      + destruct IH as (IH1 & IH2 & IH3). split; [ | split].
        * cbn. lia.
        * intros v1 v2 [-> | H2] [-> | H3] H4; try congruence.
          -- now apply H1. 
          -- apply E_symm. now apply H1. 
          -- now apply IH2. 
        * now constructor.
  Qed. 
End fixGraph. 
  
Definition Clique (i : UGraph * nat) := let (g, k) := i in exists l, @isKClique g k l.  



