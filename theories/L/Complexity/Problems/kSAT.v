From Undecidability.L Require Import L.
From Undecidability.L.Tactics Require Import LTactics ComputableTactics.
From Undecidability.L.Datatypes Require Import LProd LTerm LNat Lists LOptions.
From Undecidability.L.Complexity Require Import NP Synthetic Monotonic.
From Undecidability.L.Functions Require Import Size.

From Undecidability.L.Complexity Require Export Problems.SAT Tactics.

Inductive kCNF (k : nat) : cnf -> Prop :=
| kCNFB : k > 0 -> kCNF k []
| kCNFS (c : cnf) (cl : clause) : (|cl|) = k -> kCNF k c -> kCNF k (cl :: c).               

Definition kSAT (k : nat) (c : cnf) : Prop := kCNF k c /\ exists (a : assgn), evalCnf a c = Some true. 

Definition kCNF_decb_pred (k : nat) := (fun (cl : clause) => Nat.eqb k (|cl|)).
Definition kCNF_decb (k : nat) (c : cnf) := leb 1 k && forallb (kCNF_decb_pred k) c. 

Lemma kCNF_decb_correct (k : nat) (c : cnf) : kCNF_decb k c = true <-> (k > 0 /\ forall (cl : clause), cl el c -> (k = |cl|)). 
Proof.
  unfold kCNF_decb, kCNF_decb_pred. 
  split.
  - intros H; simp_bool. rewrite forallb_forall in H1. split.
    apply leb_complete in H0; lia. intros. rewrite <- Nat.eqb_eq. now apply H1.  
  - intros [H1 H2]. simp_bool; split. apply Nat.leb_le; lia. 
    rewrite forallb_forall. intros. rewrite Nat.eqb_eq. now apply H2. 
Qed. 

Lemma kCNF_kge (k : nat) (c : cnf) : kCNF k c -> k > 0.
Proof. induction 1; assumption. Qed.

Lemma kCNF_clause_length (k : nat) (c : cnf) : kCNF k c -> forall cl, cl el c -> |cl| =k.
Proof.
  induction 1. 
  - intros cl [].
  - intros cl' [-> | Hel]; [assumption | now apply IHkCNF]. 
Qed. 

Instance term_kCNF_decb_pred : computableTime' kCNF_decb_pred (fun k _ => (1, fun cl _ => (11 * (|cl|) + 17 * min k (|cl|) + 23, tt))).  
Proof.
  extract. 
  solverec. 
Defined. 

Instance term_kCNF_decb : computableTime' kCNF_decb (fun k _ => (1, fun c _ => (forallb_time (fun cl _ => (11 * (|cl|) + 17 * min k (|cl|) + 23, tt)) c + 36, tt))).
Proof.
  extract. 
  solverec. 
Qed. 
  
