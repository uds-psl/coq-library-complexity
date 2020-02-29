From Undecidability.L.Complexity.Cook Require Export SAT.
From Undecidability.L.Datatypes Require Import LProd LTerm LLNat LLists LOptions.

(** * k-SAT  *)
(** A CNF is a k-CNF if each of its clauses has exactly k literals. k-SAT is SAT restricted to k-CNFs. *)

Inductive kCNF (k : nat) : cnf -> Prop :=
| kCNFB : kCNF k []
| kCNFS (c : cnf) (cl : clause) : (|cl|) = k -> kCNF k c -> kCNF k (cl :: c).               

Hint Constructors kCNF.

Lemma kCNF_clause_length (k : nat) (c : cnf) : kCNF k c <-> forall cl, cl el c -> |cl| =k.
Proof.
  split. 
  - induction 1. 
    + intros cl [].
    + intros cl' [-> | Hel]; [assumption | now apply IHkCNF]. 
  - intros H. induction c; [eauto | ].
    constructor; [now apply H | apply IHc; eauto].
Qed. 

Lemma kCNF_app (k : nat) (c1 c2 : cnf) : kCNF k (c1 ++ c2) <-> kCNF k c1 /\ kCNF k c2. 
Proof. 
  induction c1; cbn; split. 
  - eauto.
  - tauto.
  - intros H. inv H. apply IHc1 in H3 as (H3 & H4). split; eauto.
  - intros [H1 H2]. inv H1. constructor; [easy | ]. now apply IHc1. 
Qed. 

Definition kSAT (k : nat) (c : cnf) : Prop := k > 0 /\ kCNF k c /\ SAT c. 

(** boolean decider for kCNF *)
Definition clause_length_decb (k : nat) := (fun (cl : clause) => Nat.eqb k (|cl|)).
Definition kCNF_decb (k : nat) (c : cnf) := forallb (clause_length_decb k) c. 

Lemma kCNF_decb_iff (k : nat) (c : cnf) : kCNF_decb k c = true <-> kCNF k c. 
Proof.
  rewrite kCNF_clause_length. unfold kCNF_decb, clause_length_decb. 
  rewrite forallb_forall. setoid_rewrite Nat.eqb_eq. firstorder.
Qed. 

(** extraction of decider *)
From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Complexity Require Import PolyBounds. 

Definition c__clauseLengthDecb :=  c__length + c__nat_eqb2 + 1.
Definition clause_length_decb_time (k : nat) (cl : clause) := c__length * (|cl|) + nat_eqb_time k (|cl|) + c__clauseLengthDecb.
Instance term_clause_length_decb : computableTime' clause_length_decb (fun k _ => (1, fun cl _ => (clause_length_decb_time k cl, tt))). 
Proof. 
  extract. solverec. unfold clause_length_decb_time, c__clauseLengthDecb. solverec. 
Defined. 


Definition c__kCNFDecb := 3. 
Definition kCNF_decb_time (k : nat) (c : cnf) := forallb_time (fun cl => clause_length_decb_time k cl) c + c__kCNFDecb.
Instance term_kCNF_decb : computableTime' kCNF_decb (fun k _ => (1, fun c _ => (kCNF_decb_time k c, tt))). 
Proof. 
  extract. solverec. unfold kCNF_decb_time, c__kCNFDecb. solverec. 
Defined. 

Definition c__kCNFDecbBound1 := c__length + c__nat_eqb.
Definition c__kCNFDecbBound2 := c__clauseLengthDecb + c__forallb + c__kCNFDecb.
Definition poly__kCNFDecb n := (n + 1) * (c__kCNFDecbBound1 * (n + 1)  + c__kCNFDecbBound2). 
Lemma kCNF_decb_time_bound k c : kCNF_decb_time k c <= poly__kCNFDecb (size (enc c) + size (enc k)). 
Proof. 
  unfold kCNF_decb_time. rewrite forallb_time_bound_env.
  2: { 
    split. 
    - intros cl n. unfold clause_length_decb_time. 
      rewrite nat_eqb_time_bound_r. rewrite list_size_length at 1. rewrite list_size_enc_length. 
      instantiate (1 := registered_nat_enc).
      instantiate (1 := fun n => (c__length + c__nat_eqb) * (n + 1) + c__clauseLengthDecb). 
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
