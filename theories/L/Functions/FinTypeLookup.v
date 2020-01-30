From Undecidability.L.Tactics Require Import LTactics.
From Undecidability.L.Datatypes Require Import LFinType LBool LProd Lists.

Section Lookup.
  Variable X Y : Type.
  Variable eqb : X -> X -> bool.

  Fixpoint lookup (x:X) (A:list (X*Y)) d: Y :=
    match A with
      [] => d
    | (key,Lproc)::A =>
      if eqb x key then Lproc else lookup x A d
    end.

End Lookup.

Section funTable.

  Variable X : finType.
  Variable Y : Type.
  Variable f : X -> Y.

  Definition funTable :=
    map (fun x => (x,f x)) (elem X).

  Variable (eqb : X -> X -> bool).
  Variable (Heqb:forall x y, reflect (x = y) (eqb x y)).

  Lemma lookup_funTable x d:
    lookup eqb x funTable d = f x.
  Proof.
    unfold funTable.
    specialize (elem_spec x).
    generalize (elem X) as l.
    induction l;cbn;intros Hel.
    -tauto.
    -destruct (Heqb x a).
     +congruence.
     +destruct Hel. 1:congruence.
      eauto.
  Qed.
End funTable.

Section lookup_correct.
  Variable (X Y : Type). 
  Variable (eqb : X -> X -> bool).
  Variable (Heqb : forall x y, reflect (x = y) (eqb x y)). 

  Lemma lookup_sound (L : list (X * Y)) a b def : 
    (forall a' b1 b2, (a', b1) el L -> (a', b2) el L -> b1 = b2) -> (a, b) el L -> lookup eqb a L def = b.
  Proof. 
    intros H1 H2. induction L; cbn; [ destruct H2 | ]. 
    destruct a0. specialize (Heqb a x). apply reflect_iff in Heqb. 
    destruct eqb. 
    - specialize (proj2 Heqb eq_refl) as ->.
      destruct H2 as [H2 | H2]; [easy | ].
      apply (H1 x y b); easy.
    - assert (not (a = x)). { intros ->. easy. }
      destruct H2 as [H2 | H2]; [ congruence | ].
      apply IHL in H2; [easy | intros; now eapply H1]. 
  Qed. 

  Lemma lookup_complete (L : list (X * Y)) a def : 
    {(a, lookup eqb a L def) el L } + {~(exists b, (a, b) el L) /\  lookup eqb a L def = def}.
  Proof. 
    induction L; cbn; [ right; split; [ intros [? []] | reflexivity] | ]. 
    destruct a0. specialize (Heqb a x). apply reflect_iff in Heqb. 
    destruct eqb. 
    - left; left. f_equal. symmetry; now apply Heqb. 
    - destruct IHL as [IH | IH]. 
      + left; right; apply IH. 
      + right. split; [ intros (b & [H1 | H1]) | apply IH].
        * inv H1. easy.
        * apply (proj1 IH). eauto.
  Qed. 
End lookup_correct.

Definition lookupTime {X Y} `{registered X} (eqbT : timeComplexity (X ->X ->bool)) x (l:list (X*Y)):=
  fold_right (fun '(a,b) res => callTime2 eqbT x a + res +19) 4 l.


Global Instance term_lookup X Y `{registered X} `{registered Y}:
  computableTime' (@lookup X Y) (fun eqb T__eqb => (1, fun x _ => (5, fun l _ => (1, fun d _ => (lookupTime T__eqb x l,tt))))).
extract. unfold lookupTime. solverec.
Qed.

Lemma lookupTime_leq {X Y} `{registered X} (eqbT:timeComplexity (X -> X -> bool)) x (l:list (X*Y)) k:
  (forall y, callTime2 eqbT x y <= k)
  -> lookupTime eqbT x l <= length l * (k + 19) + 4.
Proof.
  intros H'.
  induction l as [ | [a b] l].
  -cbn. omega.
  -unfold lookupTime. cbn [fold_right]. fold (lookupTime eqbT x l).
   setoid_rewrite IHl. cbn [length]. rewrite H'.
   ring_simplify. omega.
Qed.
