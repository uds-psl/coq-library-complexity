(* ** Abstract Reduction Systems *)
(* Additional material building on top of Undecidability.L.Prelim.ARS *)

Require Export Undecidability.L.Prelim.ARS.

Import ARSNotations.

Section FixX.
  Variable X : Type.
  Implicit Types R S : X -> X -> Prop.
  Implicit Types x y z : X.

  (* classical *)
  Definition classical R x := terminal R x \/ exists y, R x y.

  (* Strong normalisation *)
  
  Inductive SN R : X -> Prop :=
  | SNC x : (forall y, R x y -> SN R y) -> SN R x.

  Fact SN_unfold R x :
    SN R x <-> forall y, R x y -> SN R y.
  Proof.
    split.
    - destruct 1 as [x H]. exact H.
    - intros H. constructor. exact H.
  Qed.
  
End FixX.

#[global]
Existing Instance star_PO.

(* A notion of a reduction sequence which keeps track of the largest occuring state *)

Inductive redWithMaxSize {X} (size:X -> nat) (step : X -> X -> Prop): nat -> X -> X -> Prop:=
  redWithMaxSizeR m s: m = size s -> redWithMaxSize size step m s s 
| redWithMaxSizeC s s' t m m': step s s' -> redWithMaxSize size step m' s' t -> m = max (size s) m' -> redWithMaxSize size step m s t.

Lemma redWithMaxSize_ge X size step (s t:X) m:
  redWithMaxSize size step m s t -> size s<= m /\ size t <= m.
Proof.
  induction 1;subst;firstorder (repeat eapply Nat.max_case_strong; try lia).
Qed.

Lemma redWithMaxSize_trans X size step (s t u:X) m1 m2 m3:
 redWithMaxSize size step m1 s t -> redWithMaxSize size step m2 t u -> max m1 m2 = m3 -> redWithMaxSize size step m3 s u.
Proof.
  induction 1 in m2,u,m3|-*;intros.
  -specialize (redWithMaxSize_ge H0) as [].
   revert H1;
     repeat eapply Nat.max_case_strong; subst m;intros. all:replace m3 with m2 by lia. all:eauto.
  - specialize (redWithMaxSize_ge H0) as [].
    specialize (redWithMaxSize_ge H2) as [].
    eassert (H1':=Nat.le_max_l _ _);rewrite H3 in H1'.
    eassert (H2':=Nat.le_max_r _ _);rewrite H3 in H2'.
    econstructor. eassumption.
     
    eapply IHredWithMaxSize. eassumption. reflexivity.
    subst m;revert H3;repeat eapply Nat.max_case_strong;intros;try lia. 
Qed.

Lemma redWithMaxSize_star {X} f (step : X -> X -> Prop) n x y:
  redWithMaxSize f step n x y -> star step x y.
Proof.
  induction 1;eauto using star.
Qed.

Lemma terminal_noRed {X} (R:X->X->Prop) x y :
  terminal R x -> star R x y -> x = y.
Proof.
  intros ? R'. inv R'. easy. edestruct H. eassumption.
Qed.

Lemma unique_normal_forms {X} (R:X->X->Prop) x y:
  confluent R -> ecl R x y -> terminal R x -> terminal R y -> x = y.
Proof.
  intros CR%confluent_CR E T1 T2.
  specialize (CR _ _ E) as (z&R1&R2).
  apply terminal_noRed in R1. apply terminal_noRed in R2. 2-3:eassumption. congruence.
Qed.

#[global]
Instance ecl_Equivalence {X} (R:X->X->Prop) : Equivalence (ecl R).
Proof.
  split.
  -constructor.
  -apply ecl_sym.
  -apply ecl_trans.
Qed.

#[global]
Instance star_ecl_subrel {X} (R:X->X->Prop) : subrelation (star R) (ecl R).
Proof.
  intro. eapply star_ecl.
Qed.

#[global]
Instance pow_ecl_subrel {X} (R:X->X->Prop) n : subrelation (pow R n) (ecl R).
Proof.
  intros ? ? H%pow_star. now rewrite H.
Qed.

Lemma uniform_confluence_parameterized_terminal (X : Type) (R : X -> X -> Prop) (m n : nat) (s t1 t2 : X):
  uniform_confluent R -> terminal R t1 ->
  pow R m s t1 -> pow R n s t2 -> exists n', pow R n' t2 t1 /\ m = n + n'.
Proof.
  intros H1 H2 H3 H4.
  specialize (parametrized_confluence H1 H3 H4) as (n0&n'&?&?&?&R'&?&?).
  destruct n0.
  -inv R'. exists n'. intuition lia.
  -exfalso. destruct R' as (?&?&?). eapply H2. eauto.
Qed.

Lemma uniform_confluence_parameterized_both_terminal (X : Type) (R : X -> X -> Prop) (n1 n2 : nat) (s t1 t2 : X):
  uniform_confluent R -> terminal R t1 -> terminal R t2 ->
  pow R n1 s t1 -> pow R n2 s t2 -> n1=n2 /\ t1 = t2.
Proof.
  intros H1 H2 H2' H3 H4.
  specialize (parametrized_confluence H1 H3 H4) as (n0&n'&?&?&?&R'&R''&?).
  destruct n0. destruct n'.
  -inv R'. inv H5. split;first [lia | easy].
  -exfalso. destruct R'' as (?&?&?). eapply H2'. eauto.
  -exfalso. destruct R' as (?&?&?). eapply H2. eauto.
Qed.

Lemma uniform_confluent_confluent (X : Type) (R : X -> X -> Prop):
  uniform_confluent R -> confluent R.
Proof.
  intros H x y y' Hy Hy'. apply ARS.star_pow in Hy as (?&Hy). apply ARS.star_pow in Hy' as (?&Hy').
  edestruct parametrized_confluence as (?&?&z&?&?&?&?&?).
  eassumption. exact Hy. exact Hy'. exists z. split;eapply pow_star. all:eauto.
Qed.

Definition computesRel {X Y} (f : X -> option Y) (R:X -> Y -> Prop) :=
  forall x, match f x with
         Some y => R x y
       | None => terminal R x
       end.

Definition evaluatesIn (X : Type) (R : X -> X -> Prop) n (x y : X) := pow R n x y /\ terminal R y.

Lemma evalevaluates_evaluatesIn X (step:X->X->Prop) s t:
  evaluates step s t -> exists k, evaluatesIn step k s t.
Proof.
  intros [(R&?)%star_pow ?]. unfold evaluatesIn. eauto.
Qed.
