From Undecidability.L Require Import L .
From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Import Lists LNat. 
From Complexity.L.Complexity.Problems Require Export SharedSAT.
Require Import Lia Nat. 

(** * Formula Satisfiability: the satisfiability problem on arbitrary Boolean formulas *)

Inductive formula : Type := 
  | Ftrue : formula
  | Fvar : var -> formula
  | Fand : formula -> formula -> formula
  | For : formula -> formula -> formula
  | Fneg : formula -> formula. 

Notation "a ∧ b" := (Fand a b) (at level 40).  
Notation "a ∨ b" := (For a b) (at level 40). 
Notation "¬ a" := (Fneg a) (at level 10). 
Coercion Fvar : var >-> formula. 

Notation "⋁ [ x , .. , z , y ]" := (For x .. (For z y) ..). 
Notation "⋀ [ x , .. , z , y ]" := (Fand x .. (Fand z y) ..). 

(** assignments: we list the variables which are assigned the value true; all other variables are assigned the value false *)
Implicit Types (a : assgn) (f : formula) (v : var). 

Fixpoint evalFormula a f := 
  match f with 
  | Ftrue => true
  | Fvar v => evalVar a v
  | Fand f1 f2 => evalFormula a f1 && evalFormula a f2
  | For f1 f2 => evalFormula a f1 || evalFormula a f2
  | Fneg f => negb (evalFormula a f)
  end. 

Lemma evalFormula_and_iff a f1 f2 : evalFormula a (f1 ∧ f2) = true <-> evalFormula a f1 = true /\ evalFormula a f2 = true. 
Proof. cbn. now rewrite andb_true_iff. Qed. 

Lemma evalFormula_and_iff' f1 f2 a: evalFormula a (f1 ∧ f2) = false <-> evalFormula a f1 = false \/ evalFormula a f2 = false. 
Proof. 
  cbn.  destruct (evalFormula a f1), (evalFormula a f2); cbn; tauto.
Qed. 

Lemma evalFormula_or_iff a f1 f2 : evalFormula a (f1 ∨ f2) = true <-> evalFormula a f1 = true \/ evalFormula a f2 = true. 
Proof. cbn. now rewrite orb_true_iff. Qed. 

Lemma evalFormula_not_iff a f : evalFormula a (¬ f) = true <-> not (evalFormula a f = true).
Proof. cbn. rewrite negb_true_iff. split; eauto. Qed. 

Lemma evalFormula_prim_iff a v : evalFormula a v = true <-> v el a. 
Proof. cbn. unfold evalVar. rewrite list_in_decb_iff; [easy | intros ]. now rewrite Nat.eqb_eq. Qed. 

(** satisfaction of formulas *)
Definition satisfies a f := evalFormula a f = true. 
Definition FSAT f := exists a, satisfies a f. 

(** bounds on the number of used variables *)
Inductive varInFormula (v : var) : formula -> Prop := 
  | varInFormulaV : varInFormula v v
  | varInFormuAndL f1 f2: varInFormula v f1 -> varInFormula v (f1 ∧ f2)
  | varInFormulaAndR f1 f2 : varInFormula v f2 -> varInFormula v (f1 ∧ f2)
  | varInFormulaOrL f1 f2 : varInFormula v f1 -> varInFormula v (f1 ∨ f2)
  | varInFormulaOrR f1 f2 : varInFormula v f2 -> varInFormula v (f1 ∨ f2)
  | varInFormulaNot f : varInFormula v f -> varInFormula v (¬ f).
Hint Constructors varInFormula : core.

Definition formula_varsIn (p : nat -> Prop) f := forall v, varInFormula v f -> p v. 

(** A computable notion of boundedness *)
Fixpoint formula_maxVar (f : formula) := match f with
  | Ftrue => 0
  | Fvar v => v
  | Fand f1 f2 => Nat.max (formula_maxVar f1) (formula_maxVar f2)
  | For f1 f2 => Nat.max (formula_maxVar f1) (formula_maxVar f2)
  | Fneg f => formula_maxVar f
end. 

Lemma formula_maxVar_varsIn f : formula_varsIn (fun n => n < S (formula_maxVar f)) f. 
Proof. 
  unfold formula_varsIn. 
  induction f. 
  - intros v H. inv H. 
  - intros v H. inv H. now cbn. 
  - intros v H. inv H. 
    + apply IHf1 in H1. cbn. lia. 
    + apply IHf2 in H1. cbn. lia. 
  - intros v H. inv H. 
    + apply IHf1 in H1. cbn. lia. 
    + apply IHf2 in H1. cbn. lia. 
  - intros v H. inv H. apply IHf in H1. cbn. lia. 
Qed.

Lemma formula_varsIn_bound f c : formula_varsIn (fun n => n <= c) f -> formula_maxVar f <= c. 
Proof. 
  unfold formula_varsIn. intros H. induction f; cbn. 
  - lia. 
  - now apply H. 
  - apply Nat.max_lub; [apply IHf1 | apply IHf2]; eauto.
  - apply Nat.max_lub; [apply IHf1 | apply IHf2]; eauto. 
  - apply IHf; eauto.
Qed. 

(** size of formulas *)
Fixpoint formula_size (f : formula) := match f with 
  | Ftrue => 1
  | Fvar _ => 1
  | For f1 f2 => formula_size f1 + formula_size f2 + 1
  | Fand f1 f2 => formula_size f1 + formula_size f2 + 1
  | Fneg f => formula_size f + 1
end. 

(** ** extraction *)
From Undecidability.L.Datatypes Require Import LNat.
From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Import  LProd LOptions LBool LUnit.
From Complexity.L.Complexity Require Import PolyBounds. 

MetaCoq Run (tmGenEncode "formula_enc" formula).
Hint Resolve formula_enc_correct : Lrewrite.

Lemma formula_enc_size f: size (enc f) = match f with 
  | Ftrue => 10
  | Fvar v => 10 + size (enc v )
  | Fand f1 f2 => 10 + size (enc f1) + size (enc f2) 
  | For f1 f2 => 9 + size (enc f1) + size (enc f2) 
  | Fneg f => 7 + size (enc f) 
  end. 
Proof.
  set (g:=enc (X:= formula)). unfold enc in g;cbn in g.
  destruct f; cbn; try lia. 
Qed. 

Instance term_Fvar : computableTime' Fvar (fun v _ => (1, tt)). 
Proof. 
  extract constructor. solverec. 
Defined. 

Instance term_Fand : computableTime' Fand (fun f1 _ => (1, fun f2 _ => (1, tt))).
Proof. 
  extract constructor. solverec. 
Defined. 

Instance term_For : computableTime' For (fun f1 _ => (1, fun f2 _ => (1, tt))). 
Proof. 
  extract constructor. solverec. 
Defined. 

Instance term_Fneg : computableTime' Fneg (fun f _ => (1, tt)). 
Proof. 
  extract constructor. solverec. 
Defined. 

(** the encoding size of a formula is bounded linearly by formula_size f * formula_maxVar f *)
Definition c__formulaBound1 := c__natsizeS. 
Definition c__formulaBound2 := size (enc Ftrue) + 10 + c__natsizeO.
Lemma formula_enc_size_bound : forall f, size (enc f) <= c__formulaBound1 * formula_size f * formula_maxVar f + c__formulaBound2 * formula_size f.
Proof. 
  induction f; rewrite formula_enc_size. 
  - unfold c__formulaBound2. cbn. nia.
  - rewrite size_nat_enc. unfold c__formulaBound1, c__formulaBound2. cbn -[Nat.add Nat.mul]. lia. 
  - cbn -[Nat.mul Nat.add].
    rewrite IHf1, IHf2. unfold c__formulaBound2. nia.
  - cbn -[Nat.mul Nat.add].
    rewrite IHf1, IHf2. unfold c__formulaBound2. nia.
  - cbn -[Nat.mul Nat.add]. 
    rewrite IHf. unfold c__formulaBound2. nia. 
Qed. 

(** conversely, we can only obtain a quadratic bound due to the overapproximation provided by maxVar *)

Lemma formula_size_enc_bound f : formula_size f <= size (enc f). 
Proof. 
  induction f; rewrite formula_enc_size; cbn -[Nat.add Nat.mul]; try lia.
Qed.  

Lemma formula_maxVar_enc_bound f : formula_maxVar f <= size (enc f).
Proof. 
  induction f; rewrite formula_enc_size; cbn -[Nat.add Nat.mul]; try lia. 
  rewrite (size_nat_enc_r n) at 1. unfold enc. cbn. nia. 
Qed. 

Lemma formula_total_size_enc_bound f : formula_size f * formula_maxVar f <= size (enc f) * size (enc f). 
Proof. 
  rewrite formula_size_enc_bound, formula_maxVar_enc_bound. lia. 
Qed. 


(**extraction of formula_maxVar *)

Definition c__formulaMaxVar := 13 + c__max1. 
Fixpoint formula_maxVar_time (f : formula) := match f with 
  | Ftrue => 0
  | Fvar _ => 0
  | Fand f1 f2 => formula_maxVar_time f1 + formula_maxVar_time f2 + max_time (formula_maxVar f1) (formula_maxVar f2)  
  | For f1 f2 => formula_maxVar_time f1 + formula_maxVar_time f2 + max_time (formula_maxVar f1) (formula_maxVar f2)
  | Fneg f => formula_maxVar_time f 
  end + c__formulaMaxVar. 
Instance term_formula_maxVar : computableTime' formula_maxVar (fun f _ => (formula_maxVar_time f, tt)). 
Proof. 
  extract. solverec. 
  - now unfold c__formulaMaxVar. 
  - now unfold c__formulaMaxVar. 
  - fold formula_maxVar. unfold c__formulaMaxVar; solverec. 
  - fold formula_maxVar. unfold c__formulaMaxVar; solverec. 
  - unfold c__formulaMaxVar; solverec. 
Defined. 

Definition c__formulaMaxVarBound1 := c__formulaMaxVar + c__max2.
Definition poly__formulaMaxVar n := (n+1) * (n + 1) * c__formulaMaxVarBound1.
Lemma formula_maxVar_time_bound (f : formula) : formula_maxVar_time f <= poly__formulaMaxVar (size (enc f)). 
Proof. 
  induction f; cbn -[Nat.add Nat.mul].
  - unfold poly__formulaMaxVar, c__formulaMaxVarBound1; nia.
  - unfold poly__formulaMaxVar, c__formulaMaxVarBound1; nia. 
  - rewrite IHf1, IHf2. unfold max_time. rewrite Nat.le_min_l. 
    rewrite formula_maxVar_enc_bound. setoid_rewrite formula_enc_size at 4. 
    unfold poly__formulaMaxVar, c__formulaMaxVarBound1. leq_crossout. 
  - rewrite IHf1, IHf2. unfold max_time. rewrite Nat.le_min_l. 
    rewrite formula_maxVar_enc_bound. setoid_rewrite formula_enc_size at 4. 
    unfold poly__formulaMaxVar, c__formulaMaxVarBound1. leq_crossout. 
  - rewrite IHf. setoid_rewrite formula_enc_size at 2. unfold poly__formulaMaxVar, c__formulaMaxVarBound1. leq_crossout. 
Qed. 
Lemma formula_maxVar_poly : monotonic poly__formulaMaxVar /\ inOPoly poly__formulaMaxVar. 
Proof. 
  split; unfold poly__formulaMaxVar; smpl_inO. 
Qed. 

