From PslBase Require Import FinTypes. 
From Undecidability.L.Complexity.Problems Require Import UGraph. 

Section fixGraph. 
  Variable (g : UGraph). 
  Notation V := (V g).
  Notation E := (@E g).

  Definition isClique (l : list V) := forall v1 v2, v1 el l -> v2 el l -> E (v1, v2). 
  Definition isKClique k (l : list V) := |l| = k /\ isClique l. 
End fixGraph. 
  
Definition Clique (i : UGraph * nat) := let (g, k) := i in exists l, @isKClique g k l.  


