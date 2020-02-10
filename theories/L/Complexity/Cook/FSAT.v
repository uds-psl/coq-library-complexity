From Undecidability.L Require Import L.
From Undecidability.L.Datatypes Require Import LLists. 

(** *Formula Satisfiability: the satisfiability problem on arbitrary Boolean formulas *)

Notation var := (nat) (only parsing). 

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
Notation assgn := (list var). 
Implicit Types (a : assgn) (f : formula) (v : var). 

Definition evalVar a v  := list_in_decb Nat.eqb a v.
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

Lemma evalFormula_negb_iff a f : evalFormula a (¬ f) = true <-> not (evalFormula a f = true).
Proof. cbn. rewrite negb_true_iff. split; eauto. Qed. 

Lemma evalFormula_prim_iff a v : evalFormula a v = true <-> v el a. 
Proof. cbn. unfold evalVar. rewrite list_in_decb_iff; [easy | intros ]. now rewrite Nat.eqb_eq. Qed. 

(*satisfaction of formulas *)
Definition satisfies a f := evalFormula a f = true. 
Definition FSAT f := exists a, satisfies a f. 
