From Undecidability.L Require Import L.
From Undecidability.L.Datatypes Require Import LLists. 
From Undecidability.L.Complexity.Cook Require Export SharedSAT.
Require Import Lia. 

(** *Formula Satisfiability: the satisfiability problem on arbitrary Boolean formulas *)

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

(*assignments: we list the variables which are assigned the value true; all other variables are assigned the value false *)
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

Lemma evalFormula_or_iff a f1 f2 : evalFormula a (f1 ∨ f2) = true <-> evalFormula a f1 = true \/ evalFormula a f2 = true. 
Proof. cbn. now rewrite orb_true_iff. Qed. 

Lemma evalFormula_not_iff a f : evalFormula a (¬ f) = true <-> not (evalFormula a f = true).
Proof. cbn. rewrite negb_true_iff. split; eauto. Qed. 

Lemma evalFormula_prim_iff a v : evalFormula a v = true <-> v el a. 
Proof. cbn. unfold evalVar. rewrite list_in_decb_iff; [easy | intros ]. now rewrite Nat.eqb_eq. Qed. 

(*satisfaction of formulas *)
Definition satisfies a f := evalFormula a f = true. 
Definition FSAT f := exists a, satisfies a f. 

(** bounds on the number of used variables *)
Inductive varBound_formula (n : nat) : formula -> Prop :=
  | varBound_forVar v : n > v -> varBound_formula n v 
  | varBound_forTrue : varBound_formula n Ftrue
  | varBound_forAnd n1 n2 f1 f2 : varBound_formula n1 f1 -> varBound_formula n2 f2 -> n >= n1 -> n >= n2 -> varBound_formula n (f1 ∧ f2)
  | varBound_forOr n1 n2 f1 f2 : varBound_formula n1 f1 -> varBound_formula n2 f2 -> n >= n1 -> n >= n2 -> varBound_formula n (f1 ∨ f2)
  | varBound_forNeg f : varBound_formula n f -> varBound_formula n (¬ f). 
Hint Constructors varBound_formula. 

Lemma varBound_formula_monotonic (f : formula) (n n' : nat) : n <= n' -> varBound_formula n f -> varBound_formula n' f. 
Proof. 
  intros H0 H. induction H; econstructor; eauto; lia.
Qed. 

(*A computable notion of boundedness *)
Fixpoint formula_maxVar (f : formula) := match f with
  | Ftrue => 0
  | Fvar v => S v
  | Fand f1 f2 => Nat.max (formula_maxVar f1) (formula_maxVar f2)
  | For f1 f2 => Nat.max (formula_maxVar f1) (formula_maxVar f2)
  | Fneg f => formula_maxVar f
end. 

Lemma formula_bound_varBound f: varBound_formula (formula_maxVar f) f. 
Proof. 
  induction f; cbn.
  - eauto.
  - eauto. 
  - econstructor; eauto; lia. 
  - econstructor; eauto; lia. 
  - eauto.
Qed. 

Lemma formula_varBound_bound f n : varBound_formula n f -> formula_maxVar f <= n. 
Proof. 
  induction 1; cbn; lia.
Qed. 

(** size of formulas *)
Fixpoint formula_size (f : formula) := match f with 
  | Ftrue => 1
  | Fvar _ => 1
  | For f1 f2 => formula_size f1 + formula_size f2 + 1
  | Fand f1 f2 => formula_size f1 + formula_size f2 + 1
  | Fneg f => formula_size f + 1
end. 

(** extraction *)
From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Import  LProd LOptions LBool LLNat LLists LUnit.
From Undecidability.L.Complexity Require Import PolyBounds. 


Run TemplateProgram (tmGenEncode "formula_enc" formula).
Hint Resolve formula_enc_correct : Lrewrite.

(*the encoding size of a formula relates linearly to formula_size f * formula_maxVar f *)
Definition c__formulaBound1 := c__natsizeS. 
Definition c__formulaBound2 := size (enc Ftrue) + 10 + c__natsizeO.
Lemma formula_enc_size_bound : forall f, size (enc f) <= c__formulaBound1 * formula_size f * formula_maxVar f + c__formulaBound2 * formula_size f.
(** (formula_size f + 1).*)
Proof. 
  induction f. 
  - unfold c__formulaBound2. cbn. nia.
  - unfold enc. cbn -[Nat.mul]. rewrite size_nat_enc. unfold c__formulaBound1, c__formulaBound2. lia. 
  - unfold enc. cbn -[Nat.mul Nat.add].
    rewrite IHf1, IHf2. unfold c__formulaBound2. nia.
  - unfold enc. cbn -[Nat.mul Nat.add].
    rewrite IHf1, IHf2. unfold c__formulaBound2. nia.
  - unfold enc. cbn -[Nat.mul Nat.add]. 
    rewrite IHf. unfold c__formulaBound2. nia. 
Qed. 


