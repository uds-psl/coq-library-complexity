From Undecidability.L.Complexity.Problems Require Export SAT.
From Undecidability.L.Datatypes Require Import LProd LTerm LLNat LLists LOptions.
From Undecidability.L.Functions Require Import EqBool.

(** * k-SAT  *)
(** A CNF is a k-CNF if each of its clauses has exactly k literals. k-SAT is SAT restricted to k-CNFs. *)

Inductive kCNF (k : nat) : cnf -> Prop :=
| kCNFB : kCNF k []
| kCNFS (N : cnf) (C : clause) : (|C|) = k -> kCNF k N -> kCNF k (C ::  N).               

Hint Constructors kCNF.

Lemma kCNF_clause_length (k : nat) (N : cnf) : kCNF k N <-> forall C, C el N -> |C| =k.
Proof.
  split. 
  - induction 1. 
    + intros C [].
    + intros C' [-> | Hel]; [assumption | now apply IHkCNF]. 
  - intros H. induction N; [eauto | ].
    constructor; [now apply H | apply IHN; eauto].
Qed. 

Lemma kCNF_app (k : nat) (N1 N2 : cnf) : kCNF k (N1 ++ N2) <-> kCNF k N1 /\ kCNF k N2. 
Proof. 
  induction N1; cbn; split. 
  - eauto.
  - tauto.
  - intros H. inv H. apply IHN1 in H3 as (H3 & H4). split; eauto.
  - intros [H1 H2]. inv H1. constructor; [easy | ]. now apply IHN1. 
Qed. 

Definition kSAT (k : nat) (N : cnf) : Prop := k > 0 /\ kCNF k N /\ SAT N. 

(** boolean decider for kCNF *)
Definition clause_length_decb (k : nat) := (fun (C : clause) => Nat.eqb k (|C|)).
Definition kCNF_decb (k : nat) (N : cnf) := forallb (clause_length_decb k) N. 

Lemma kCNF_decb_iff (k : nat) (N : cnf) : kCNF_decb k N = true <-> kCNF k N. 
Proof.
  rewrite kCNF_clause_length. unfold kCNF_decb, clause_length_decb. 
  rewrite forallb_forall. setoid_rewrite Nat.eqb_eq. firstorder.
Qed. 

(** extraction of decider *)
From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Complexity Require Import PolyBounds. 

Definition c__clauseLengthDecb :=  c__length + 5 + 1.
Definition clause_length_decb_time (k : nat) (C : clause) := c__length * (|C|) + eqbTime (X := nat) (size (enc k)) (size (enc (|C|))) + c__clauseLengthDecb.
Instance term_clause_length_decb : computableTime' clause_length_decb (fun k _ => (1, fun C _ => (clause_length_decb_time k C, tt))). 
Proof. 
  extract. solverec. unfold clause_length_decb_time, c__clauseLengthDecb. solverec. 
Defined. 

Definition c__kCNFDecb := 3. 
Definition kCNF_decb_time (k : nat) (N : cnf) := forallb_time (fun C => clause_length_decb_time k C) N + c__kCNFDecb.
Instance term_kCNF_decb : computableTime' kCNF_decb (fun k _ => (1, fun N _ => (kCNF_decb_time k N, tt))). 
Proof. 
  extract. solverec. unfold kCNF_decb_time, c__kCNFDecb. solverec. 
Defined. 

Definition c__kCNFDecbBound1 := c__length + c__eqbComp nat.
Definition c__kCNFDecbBound2 := c__clauseLengthDecb + c__forallb + c__kCNFDecb.
Definition poly__kCNFDecb n := (n + 1) * (c__kCNFDecbBound1 * (n + 1)  + c__kCNFDecbBound2). 
Lemma kCNF_decb_time_bound k N : kCNF_decb_time k N <= poly__kCNFDecb (size (enc N) + size (enc k)). 
Proof. 
  unfold kCNF_decb_time. rewrite forallb_time_bound_env.
  2: { 
    split. 
    - intros C n. unfold clause_length_decb_time. 
      rewrite eqbTime_le_r. rewrite list_size_length at 1. rewrite list_size_enc_length. 
      instantiate (1 := registered_nat_enc).
      instantiate (1 := fun n => (c__length + c__eqbComp nat) * (n + 1) + c__clauseLengthDecb). 
      cbn -[Nat.add Nat.mul]. solverec. 
    - smpl_inO. 
  } 
  rewrite list_size_length. 
  unfold poly__kCNFDecb, c__kCNFDecbBound1, c__kCNFDecbBound2. nia. 
Qed. 
Lemma kCNF_decb_poly : monotonic poly__kCNFDecb /\ inOPoly poly__kCNFDecb. 
Proof. 
  unfold poly__kCNFDecb. split; smpl_inO. 
Qed. 
