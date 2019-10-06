Require Import PslBase.Base.

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

