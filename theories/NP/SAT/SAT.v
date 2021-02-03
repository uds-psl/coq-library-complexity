From Complexity.NP.SAT Require Export SharedSAT.
Require Import Lia. 

From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Import  LProd LOptions LBool LNat Lists LUnit.
From Undecidability.L.Functions Require Import EqBool. 
From Complexity.Complexity Require Import UpToCPoly.
From Complexity.Libs.CookPrelim Require Import MorePrelim.

(** * SAT: Satisfiability of CNFs *)

(** ** Definition of SAT *)
(** Conjunctive normal forms (need not be canonical)*)
(* We use notations instead of definitions because the extraction mechanism does not cope well with aliases *)
Notation var := (nat) (only parsing). 
Notation literal := ((bool * var)%type) (only parsing).
Notation clause := (list literal) (only parsing). 
Notation cnf := (list clause) (only parsing).

(** Assignments as lists of natural numbers: contain the indices of variables that are mapped to true *)
Implicit Types (a : assgn) (N : cnf) (C : clause) (l :literal).

(** just a notation here; the definition is shared with FSAT *)
Notation evalVar := evalVar. 

Definition evalLiteral a l : bool := match l with
  | (s, v) => Bool.eqb (evalVar a v) s 
end. 

(**Empty disjunction evaluates to false*)
Definition evalClause a C := existsb (evalLiteral a) C. 

(**Empty conjunction evaluates to true *)
Definition evalCnf a N := forallb (evalClause a) N. 

(** Some helpful properties *)
(** A characterisation of one processing step of evaluation *)
Lemma evalClause_step_inv a C l b : 
  evalClause a (l::C) = b <-> exists b1 b2, evalClause a C = b2 /\ evalLiteral a l = b1 /\ b = b1 || b2.
Proof.
  cbn. split; intros. 
  - rewrite <- H. eauto.
  - destruct H as (b1 & b2 & <- & <- & ->). eauto.
Qed. 

Lemma evalCnf_step_inv a N C b : 
  evalCnf a (C :: N) = b <-> exists b1 b2, evalCnf a N = b2 /\ evalClause a C = b1 /\ b = b1 && b2. 
Proof. 
  cbn. split; intros. 
  - rewrite <- H. eauto. 
  - destruct H as (b1 & b2 & <- & <- & ->). eauto.
Qed. 

Lemma evalLiteral_var_iff a b v : 
  evalLiteral a (b, v) = true <-> evalVar a v = b. 
Proof. 
  unfold evalLiteral. destruct b, evalVar; cbn; firstorder.
Qed. 

Lemma evalClause_literal_iff a C : 
  evalClause a C = true <-> (exists l, l el C /\ evalLiteral a l = true). 
Proof. apply existsb_exists. Qed.

Corollary evalClause_app a C1 C2 : 
  evalClause a (C1 ++ C2) = true <-> (evalClause a C1 = true \/ evalClause a C2 = true). 
Proof. 
  rewrite !evalClause_literal_iff. setoid_rewrite in_app_iff. firstorder.
Qed.

Lemma evalCnf_clause_iff a N : 
  evalCnf a N = true <-> (forall C, C el N -> evalClause a C = true). 
Proof. apply forallb_forall. Qed.

Corollary evalCnf_app_iff a N1 N2 : 
  evalCnf a (N1 ++ N2) = true <-> (evalCnf a N1 = true /\ evalCnf a N2 = true). 
Proof. 
  rewrite !evalCnf_clause_iff. setoid_rewrite in_app_iff. firstorder.
Qed.

Definition satisfies a N := evalCnf a N = true.
Definition SAT N : Prop := exists (a : assgn), satisfies a N. 

Lemma evalLiteral_assgn_equiv a1 a2 l : a1 === a2 -> evalLiteral a1 l = evalLiteral a2 l. 
Proof. 
  intros [H1 H2]. destruct l as (b & v). unfold evalLiteral. destruct (evalVar a1 v) eqn:Hev1. 
  - apply (evalVar_monotonic H1) in Hev1. easy.
  - destruct (evalVar a2 v) eqn:Hev2; [ | easy]. 
    apply (evalVar_monotonic H2) in Hev2. congruence. 
Qed.

Lemma evalClause_assgn_equiv a1 a2 C : a1 === a2 -> evalClause a1 C = evalClause a2 C. 
Proof. 
  intros H. enough (evalClause a1 C = true <-> evalClause a2 C = true).
  - destruct evalClause; destruct evalClause; firstorder; easy. 
  - rewrite !evalClause_literal_iff. now setoid_rewrite (evalLiteral_assgn_equiv _ H). 
Qed.

Lemma evalCnf_assgn_equiv a1 a2 N : a1 === a2 -> evalCnf a1 N = evalCnf a2 N. 
Proof. 
  intros H. enough (evalCnf a1 N = true <-> evalCnf a2 N = true). 
  - destruct evalCnf; destruct evalCnf; firstorder; easy.
  - rewrite !evalCnf_clause_iff. now setoid_rewrite (evalClause_assgn_equiv _ H).
Qed. 

(** Bounds on the number of used variables*)
Definition varInLiteral v (l : literal) := exists b, l = (b, v).
Definition varInClause v c := exists l, l el c /\ varInLiteral v l. 
Definition varInCnf v cn := exists cl, cl el cn /\ varInClause v cl. 

Definition clause_varsIn (p : nat -> Prop) c := forall v, varInClause v c -> p v. 
Definition cnf_varsIn (p : nat -> Prop) c := forall v, varInCnf v c -> p v. 

Lemma cnf_varsIn_app c1 c2 p : cnf_varsIn p (c1 ++ c2) <-> cnf_varsIn p c1 /\ cnf_varsIn p c2. 
Proof. 
  unfold cnf_varsIn. unfold varInCnf. setoid_rewrite in_app_iff. split; [intros H  |intros [H1 H2]].
  - split; intros v [cl [H3 H4]]; apply H; eauto.
  - intros v [cl [[H3 | H3] H4]]; [apply H1 | apply H2]; eauto.
Qed.

Lemma cnf_varsIn_monotonic (p1 p2 : nat -> Prop) c : (forall n, p1 n -> p2 n) -> cnf_varsIn p1 c -> cnf_varsIn p2 c. 
Proof. 
  intros H H1 v H2. apply H, H1, H2. 
Qed. 

(** size of CNF in terms of number of operators *)
Definition size_clause C := length C. (*we should subtract 1 here, but this would only complicate things *)
Definition size_cnf N := sumn (map size_clause N) + length N. 

Lemma size_clause_app C1 C2 : size_clause (C1 ++ C2) = size_clause C1 + size_clause C2. 
Proof. 
  unfold size_clause. now rewrite app_length. 
Qed.

Lemma size_cnf_app N1 N2 : size_cnf (N1 ++ N2) = size_cnf N1 + size_cnf N2. 
Proof. 
  unfold size_cnf. rewrite map_app, sumn_app, app_length. lia.
Qed. 
