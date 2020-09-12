From Undecidability.L.Complexity.Problems Require Export SharedSAT.
Require Import Lia. 

From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Import  LProd LOptions LBool LNat Lists LUnit.
From Undecidability.L.Functions Require Import EqBool. 
From Undecidability.L.Complexity Require Import UpToCPoly MorePrelim. 

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

Definition evalLiteral a l : bool := match l with
  | (s, v) => Bool.eqb (evalVar a v) s 
end. 

(**Empty disjunction evaluates to false*)
Fixpoint evalClause a C := 
  match C with 
  | [] => false
  | (l :: C) => evalClause a C || evalLiteral a l
  end. 

(**Empty conjunction evaluates to true *)
Fixpoint evalCnf a N := 
  match N with 
  | [] => true
  | (C :: N) => evalCnf a N && evalClause a C
  end. 

(** Some helpful properties *)
(** A characterisation of one processing step of evaluation *)
Lemma evalClause_step_inv a C l b : 
  evalClause a (l::C) = b <-> exists b1 b2, evalClause a C = b1 /\ evalLiteral a l = b2 /\ b = b1 || b2.
Proof.
  cbn. split; intros. 
  - rewrite <- H. eauto. 
  - destruct H as (b1 & b2 & <- & <- & ->). eauto.
Qed. 

Lemma evalCnf_step_inv a N C b : 
  evalCnf a (C :: N) = b <-> exists b1 b2, evalCnf a N = b1 /\ evalClause a C = b2 /\ b = b1 && b2. 
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
Proof.
  induction C; cbn. 
  - split; [ congruence | firstorder].
  - split. 
    + intros [H1 | H2]%orb_true_iff.
      * apply IHC in H1 as (l & H1 & H2). eauto.
      * exists a0; eauto.
    + intros (l & [-> | H1] & H2). 
      * now rewrite H2, orb_true_r. 
      * fold (evalClause a C). erewrite (proj2 IHC); [easy | eauto].
Qed. 

Corollary evalClause_app a C1 C2 : 
  evalClause a (C1 ++ C2) = true <-> (evalClause a C1 = true \/ evalClause a C2 = true). 
Proof. 
  rewrite !evalClause_literal_iff. setoid_rewrite in_app_iff. firstorder.
Qed.

Lemma evalCnf_clause_iff a N : 
  evalCnf a N = true <-> (forall C, C el N -> evalClause a C = true). 
Proof. 
  induction N; cbn. 
  - firstorder. 
  - split. 
    + intros (H1 & H2)%andb_true_iff. intros C [-> | H3]; [easy | ].
      fold (evalCnf a N) in H1. eapply (proj1 IHN) in H1; eauto.
    + intros H. rewrite (H a0 (or_introl eq_refl)), andb_true_r. 
      apply IHN; eauto.
Qed. 

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

(** ** Verifier for SAT*)
(** The certificate is a satisfying assignment.
  The assignment needs to be short enough and must not contain variables not occuring in the CNF.
*)

(** Produce a list (possibly containing duplicates) of variables occuring in a CNF *)
Definition varsOfLiteral (l : literal) := match l with (_, v) => [v] end. 
Definition varsOfClause (C : clause) := concat (map varsOfLiteral C).
Definition varsOfCnf (N : cnf) := concat (map varsOfClause N).

Lemma varsOfLiteral_correct l v : v el varsOfLiteral l <-> exists b, l = (b, v). 
Proof. 
  unfold varsOfLiteral; destruct l; cbn. split. 
  - intros [-> | []]. now exists b.
  - intros [? H]. inv H. easy.
Qed. 

Lemma varsOfClause_correct C v : v el varsOfClause C <-> exists l, l el C /\ v el varsOfLiteral l. 
Proof. 
  unfold varsOfClause. now rewrite in_concat_map_iff. 
Qed. 

Lemma varsOfCnf_correct N v : v el varsOfCnf N <-> exists C, C el N /\ v el varsOfClause C. 
Proof. 
  unfold varsOfCnf. now rewrite in_concat_map_iff. 
Qed.

(** An assignment is small if it only contains variables used by the CNF and is duplicate-free *)
Definition assignment_small N a := a <<= varsOfCnf N /\ dupfree a.

Lemma varsOfLiteral_size (l : literal) : size (enc (varsOfLiteral l)) <= size (enc l) + c__listsizeCons + c__listsizeNil. 
Proof. 
  unfold varsOfLiteral. destruct l; cbn. rewrite size_list, size_prod. cbn. lia. 
Qed. 

Lemma varsOfClause_size C : size (enc (varsOfClause C)) <= size (enc C) + (|C|) * (c__listsizeCons + c__listsizeNil). 
Proof. 
  unfold varsOfClause. rewrite list_size_concat. 
  induction C; cbn -[Nat.add]; [easy | ].
  rewrite !list_size_cons, IHC. 
  rewrite varsOfLiteral_size. lia.
Qed. 

Lemma varsOfCnf_size N: size (enc (varsOfCnf N)) <= size (enc N) * (1 +( c__listsizeCons + c__listsizeNil)).
Proof. 
  unfold varsOfCnf. rewrite list_size_concat. 
  induction N; cbn -[Nat.add]; [rewrite !size_list; cbn -[Nat.add]; nia | ].
  rewrite !list_size_cons, IHN. 
  rewrite varsOfClause_size. 
  rewrite list_size_length. nia.
Qed. 


Lemma assignment_small_size N a : assignment_small N a -> size (enc a) <= size (enc N) * (1 + c__listsizeCons + c__listsizeNil). 
Proof. 
  intros [H1 H2].
  enough (size (enc a) <= size (enc (varsOfCnf N))) as H.
  { rewrite H. apply varsOfCnf_size. }
  now eapply list_incl_dupfree_size.
Qed. 

(** SAT verifier *)
Definition sat_verifier N (a : assgn) :=
  evalCnf a N = true. 

(** We need to show that, given a satisfying assignment for a CNF, we can obtain a small assignment that still satisfies the CNF*)
Section fixX. 
  Variable (X : Type).
  Variable (eqbX : X -> X -> bool). 
  Context (H : forall x y, x = y <-> eqbX x y = true).

  Fixpoint intersect (a b : list X) := match a with
  | [] => []
  | (x::a) => if list_in_decb eqbX b x then x :: intersect a b else intersect a b 
  end. 

  Lemma in_intersect_iff (a b : list X) : forall x, x el intersect a b <-> x el a /\ x el b. 
  Proof. 
    intros x. induction a; cbn; [tauto | ].
    destruct list_in_decb eqn:H1. 
    - apply list_in_decb_iff in H1; [ | apply H]. 
      split; [intros [-> | H2]; firstorder | intros ([-> | H2] & H3); [ easy| right; apply IHa; auto]]. 
    - apply list_in_decb_iff' in H1; [ | apply H]. 
      rewrite IHa. split; [ firstorder | intros [[-> | H2] H3]; [congruence | auto]]. 
  Qed. 

  Fixpoint dedup (a : list X) := match a with 
  | [] => []
  | x :: a => if list_in_decb eqbX a x then dedup a else x :: dedup a
  end. 

  Lemma in_dedup_iff (a : list X) : forall x, x el dedup a <-> x el a. 
  Proof. 
    intros x. induction a; cbn; [easy | ]. 
    destruct list_in_decb eqn:H1. 
    - apply list_in_decb_iff in H1; [ | apply H]. 
      rewrite IHa. split; [ easy | intros [-> | H2]; easy].  
    - apply list_in_decb_iff' in H1; [ | apply H]. 
      split.
      + intros [-> | H2]; [easy | right; easy]. 
      + intros [-> | H2]; [now left | right; easy]. 
  Qed. 

  Lemma dupfree_dedup (a : list X) : dupfree (dedup a). 
  Proof. 
    induction a; cbn; [ eauto using dupfree | ]. 
    destruct list_in_decb eqn:H1. 
    - apply list_in_decb_iff in H1; easy. 
    - apply list_in_decb_iff' in H1; [ | easy]. constructor. 
      + intros H2; apply H1, in_dedup_iff, H2.  
      + apply IHa. 
  Qed. 
End fixX. 

Definition compressAssignment a N := dedup Nat.eqb (intersect Nat.eqb a (varsOfCnf N)). 

Lemma compressAssignment_small a N: assignment_small N (compressAssignment a N).
Proof. 
  unfold assignment_small, compressAssignment. split; [ | apply dupfree_dedup; symmetry; apply Nat.eqb_eq].
  intros x H%in_dedup_iff; [ | symmetry; apply Nat.eqb_eq]. 
  apply in_intersect_iff in H; [ | symmetry; apply Nat.eqb_eq]. 
  apply H.  
Qed. 

Lemma compressAssignment_var_eq a N v : v el varsOfCnf N -> evalVar a v = evalVar (compressAssignment a N) v. 
Proof. 
  intros H. unfold compressAssignment. 
  unfold evalVar. destruct list_in_decb eqn:H1. 
  - symmetry. rewrite list_in_decb_iff by (symmetry; apply Nat.eqb_eq).
    apply in_dedup_iff; [ symmetry; apply Nat.eqb_eq | ]. 
    apply in_intersect_iff; [ symmetry; apply Nat.eqb_eq | ]. 
    apply list_in_decb_iff in H1; [ | symmetry; apply Nat.eqb_eq]. 
    easy.
  - symmetry. 
    rewrite list_in_decb_iff' by (symmetry; apply Nat.eqb_eq). 
    intros H2%in_dedup_iff; [ | symmetry; apply Nat.eqb_eq]. 
    apply in_intersect_iff in H2 as (H2 & _); [ | symmetry; apply Nat.eqb_eq]. 
    apply list_in_decb_iff' in H1; [ easy | symmetry; apply Nat.eqb_eq]. 
Qed. 

Lemma compressAssignment_cnf_equiv a N : evalCnf a N = true <-> evalCnf (compressAssignment a N) N = true. 
Proof. 
  rewrite !evalCnf_clause_iff. repeat setoid_rewrite evalClause_literal_iff. 
  split. 
  - intros H cl H1. specialize (H cl H1) as (l & H & H2). 
    exists l; split; [apply H | ]. 
    destruct l. rewrite evalLiteral_var_iff in *. 
    erewrite <- compressAssignment_var_eq; [ apply H2 | ]. 
    apply varsOfCnf_correct. exists cl; split; [easy | ].  
    apply varsOfClause_correct. exists (b, n); split; [easy | ]. 
    apply varsOfLiteral_correct. exists b; easy.
  - intros H cl H1. specialize (H cl H1) as (l & H & H2).
    exists l; split; [apply H | ]. 
    destruct l. rewrite evalLiteral_var_iff in *. 
    erewrite compressAssignment_var_eq; [ apply H2 | ]. 
    apply varsOfCnf_correct. exists cl; split; [easy | ]. 
    apply varsOfClause_correct. exists (b, n); split; [easy | ]. 
    apply varsOfLiteral_correct. exists b; easy.
Qed. 

(** Now that we've got the tools to verify the verifier, let's build a boolean verifier and prove its correctness*)
Definition sat_verifierb (input : cnf * assgn) :=
  let (N, a) := input in evalCnf a N.

Lemma sat_verifierb_correct N a : sat_verifier N a <-> sat_verifierb (N, a) = true.
Proof. reflexivity. Qed.

(** A computable notion of boundedness: calculate the maximum variable used by a CNF*)
Definition clause_maxVar C := fold_right (fun '(_, v) acc => Nat.max acc v) 0 C. 
Definition cnf_maxVar N := fold_right (fun C acc => Nat.max acc (clause_maxVar C)) 0 N.

Lemma cnf_maxVar_app N1 N2 : cnf_maxVar (N1 ++ N2) = Nat.max (cnf_maxVar N1) (cnf_maxVar N2). 
Proof. 
  induction N1. 
  - easy.
  - cbn. fold (cnf_maxVar (N1 ++ N2)). fold (cnf_maxVar N1). rewrite IHN1. lia. 
Qed. 

Lemma clause_maxVar_varsIn C: clause_varsIn (fun n => n < S (clause_maxVar C)) C. 
Proof. 
  unfold clause_varsIn, varInClause.
  induction C; cbn. 
  - intros v (l & [] & _). 
  - intros v (l & [-> | H1] & H2). 
    + destruct l. unfold varInLiteral in H2. 
      destruct H2 as (b' & H2). inv H2. 
      lia. 
    + specialize (IHC v ltac:(eauto)). destruct a. 
      unfold clause_maxVar in IHC. lia.
Qed.

Lemma cnf_maxVar_varsIn N : cnf_varsIn (fun n => n < S (cnf_maxVar N)) N. 
Proof. 
  unfold cnf_varsIn, varInCnf. induction N; cbn. 
  - intros v (cl & [] & _). 
  - intros v (cl & [-> | H1] & H2). 
    + apply clause_maxVar_varsIn in H2. lia.
    + specialize (IHN v ltac:(eauto)). unfold cnf_maxVar in IHN; lia. 
Qed.

Lemma clause_varsIn_bound C n : clause_varsIn (fun v => v <= n) C -> clause_maxVar C <= n. 
Proof. 
  unfold clause_varsIn. intros H. induction C; cbn; [lia | ]. 
  destruct a. rewrite IHC. 
  - rewrite (H n0); [ lia| ]. exists (b, n0). split; [eauto | exists b; eauto].
  - intros v H'. apply H. destruct H' as (l & H1 & H2). exists l; eauto. 
Qed.

Lemma cnf_varsIn_bound N n: cnf_varsIn (fun v => v <= n) N -> cnf_maxVar N <= n. 
Proof. 
  unfold cnf_varsIn. intros H. induction N; cbn; [lia | ].
  rewrite IHN. 
  - rewrite clause_varsIn_bound.
    2: { intros v H1. apply H. exists a. eauto. } 
    lia.  
  - intros v H1. apply H. destruct H1 as (C & H1 & H2). 
    exists C; eauto.
Qed.

(** ** extraction *)

(** size of encoding in terms of size of the cnf  *)
Definition c__clauseSize1 := c__listsizeCons + c__sizeBool + c__natsizeO + 4 + c__listsizeNil.
Lemma clause_enc_size_bound (c : clause) : size (enc c) <= c__natsizeS * (clause_maxVar c + 1) * (size_clause c + 1) + c__clauseSize1 * (size_clause c + 1). 
Proof. 
  induction c.
  - rewrite size_list; cbn -[Nat.mul Nat.add]. unfold c__clauseSize1. lia. 
  - rewrite list_size_cons. rewrite IHc. cbn -[Nat.mul Nat.add]. destruct a. 
    fold (clause_maxVar c). 
    rewrite size_prod; cbn -[Nat.mul Nat.add]. rewrite size_bool. rewrite size_nat_enc. 
    unfold size_clause. 
    rewrite (Nat.le_max_r (clause_maxVar c) n) at 1. 
    rewrite (Nat.le_max_l (clause_maxVar c) n) at 2.  
    unfold c__clauseSize1. nia. 
Qed. 

Definition c__cnfSize1 := c__listsizeNil + c__listsizeCons + c__clauseSize1.
Lemma cnf_enc_size_bound (c : cnf) : size (enc c) <= c__natsizeS * (cnf_maxVar c + 1) * (size_cnf c + 1) + (size_cnf c + 1) * c__cnfSize1.
Proof. 
  induction c. 
  - rewrite size_list. cbn -[Nat.mul Nat.add]. unfold c__cnfSize1. nia.
  - rewrite list_size_cons. rewrite clause_enc_size_bound. 
    cbn -[c__clauseSize1 c__cnfSize1 c__listsizeCons c__natsizeS].
    fold (cnf_maxVar c). 
    replace (size_clause a + sumn (map size_clause c) + S (|c|) + 1) with (size_clause a + size_cnf c + 2) by (unfold size_cnf; cbn; lia).
    rewrite IHc. 
    rewrite (Nat.le_max_l (cnf_maxVar c) (clause_maxVar a)) at 1. 
    rewrite (Nat.le_max_r (cnf_maxVar c) (clause_maxVar a)) at 1. 
    unfold c__cnfSize1. nia.
Qed. 

(** conversely, we can bound the size of the cnf in terms of the encoding size *)
(** we only get a quadratic bound because of the huge overapproximation by taking cnf_maxVar *)

Lemma clause_maxVar_size_enc_bound (c : clause) : clause_maxVar c + 1 <= size (enc c).
Proof. 
  induction c; cbn; [rewrite size_list; unfold c__listsizeNil; lia| ]. 
  fold (clause_maxVar c). destruct a. rewrite list_size_cons, size_prod. cbn. 
  rewrite size_nat_enc_r with (n := n) at 1. nia. 
Qed. 

Lemma clause_size_enc_bound (c : clause) : size_clause c + 1 <= size (enc c). 
Proof. 
  unfold size_clause. induction c. 
  - rewrite size_list; cbn; unfold c__listsizeNil; lia. 
  - rewrite list_size_cons; cbn. unfold c__listsizeCons; lia. 
Qed. 


Lemma clause_size_total_enc_bound (c : clause) : (size_clause c + 1) * (clause_maxVar c + 1) <= size (enc c) * size (enc c). 
Proof. 
  now rewrite clause_maxVar_size_enc_bound, clause_size_enc_bound. 
Qed. 

Lemma cnf_size_enc_bound (c : cnf) : (size_cnf c + 1) <= size (enc c). 
Proof. 
  induction c; cbn. 
  - rewrite size_list; unfold c__listsizeNil; lia. 
  - replace (size_clause a + sumn (map size_clause c) + S (|c|) + 1) with ((size_clause a + 1) + (size_cnf c + 1)). 
    2: { unfold size_cnf. lia. }
    rewrite IHc. rewrite list_size_cons. rewrite clause_size_enc_bound. lia.
Qed. 

Lemma cnf_maxVar_size_enc_bound (c : cnf) : cnf_maxVar c + 1 <= size (enc c). 
Proof. 
  induction c; cbn. 
  - rewrite size_list; unfold c__listsizeNil; lia.
  - fold (cnf_maxVar c). rewrite list_size_cons. 
    specialize (clause_maxVar_size_enc_bound a). unfold c__listsizeCons. lia. 
Qed. 

Lemma cnf_size_total_enc_bound (c : cnf) : (size_cnf c + 1) * (cnf_maxVar c + 1) <= size (enc c) * size (enc c). 
Proof. 
  rewrite cnf_maxVar_size_enc_bound, cnf_size_enc_bound.  lia. 
Qed. 

Require Import Undecidability.L.Complexity.UpToCPoly. 

(* we overwrite the already extracted version (eqbCompT instance) because we use that it is constant-time *)
Definition c__eqbBool := 7.
Instance term_bool_eqb : computableTime' Bool.eqb (fun _ _ => (1, fun _ _ => (c__eqbBool, tt))). 
Proof.
  extract. unfold c__eqbBool.
  solverec. 
Qed.

Section extraction.
  (** extraction of list_in_decb *)
  Section fixXeq. 
    Variable (X : Type).
    Context {H : registered X}.

    Context (eqbX : X -> X -> bool).
    Context {Xeq : eqbClass eqbX}. 
    Context {XeqbComp : eqbCompT X}. 

    Definition list_in_decb_time (L : list X) := ((|L|) + 1) * (maxSize L + 1) + 1.
    Fact _term_list_in_decb : { time : UpToC list_in_decb_time & computableTime' (@list_in_decb X eqbX) (fun L _ => (5, fun e _ => (time L, tt))) }. 
    Proof. 
      exists_const c.  
      { extract. solverec; cycle 1. 
        + unfold eqbTime. rewrite Nat.le_min_l. 
          unfold list_in_decb_time.
          pose (g := max (size (enc x)) (maxSize l)). 
          replace_le (size (enc x)) with g by (subst g; apply Nat.le_max_l) at 1. 
          replace_le (maxSize l) with g by (subst g; apply Nat.le_max_r) at 1 2. 
          cbn. fold (maxSize l) g. 
          instantiate (c := c__eqbComp X + 21). subst c. leq_crossout. 
        + subst c. unfold list_in_decb_time. cbn. lia. }
      smpl_upToC_solve. 
    Qed.
    Global Instance term_list_in_decb : computableTime' (@list_in_decb X eqbX) _ := projT2 _term_list_in_decb. 

    Lemma list_in_decb_poly: isPoly list_in_decb_time. 
    Proof. 
      evar (p : nat -> nat). [p] : intros n. exists p.
      { intros L. unfold list_in_decb_time. rewrite list_size_length, maxSize_enc_size.
        set (size _). subst p; hnf. reflexivity. } 
      all: subst p; smpl_inO. 
    Qed.

    Definition list_incl_decb_time (p :list X * list X) := let (L1, L2) := p in (|L1| + 1) * (((|L2| + 1) * (maxSize L2 + 1) + 1)) + 1. 
    Arguments list_incl_decb_time : simpl never. 
    Fact _term_list_incl_decb : { time : UpToC list_incl_decb_time & computableTime' (@list_incl_decb X eqbX) (fun L1 _ => (5, fun L2 _ => (time (L1, L2), tt))) }. 
    Proof. 
      exists_const c1. 
      { extract. solverec; cycle 1. 
        + rewrite !UpToC_le. 
          unfold list_incl_decb_time. cbn -[Nat.mul Nat.add]. 
          unfold list_in_decb_time. set (((|x2| + 1) * (maxSize x2 + 1) + 1)). 
          (* note that 
          instantiate (c1 := 21 + c_of _term_list_in_decb); subst c1; nia.
          does not work due to weird implicit argument inference in c_of *)
          set_consts. set (c1' := 21 + C). inst_with c1 c1'. nia.  
        + subst c1. unfold list_incl_decb_time. lia.
      } 
      smpl_upToC_solve. 
    Qed.
    Global Instance term_list_incl_decb : computableTime' (@list_incl_decb X eqbX) _ := projT2 _term_list_incl_decb. 


    Lemma list_incl_decb_poly : isPoly list_incl_decb_time. 
    Proof. 
      evar (p : nat -> nat). [p]: intros n. exists p. 
      { intros (L1 & L2). unfold list_incl_decb_time. 
        rewrite !list_size_length. rewrite maxSize_enc_size. 
        rewrite size_prod. cbn. set (L.size _). set (L.size _). 
        [p] : exact ((n + 1)^3). 
        subst p. cbn. lia. }
      all: subst p; smpl_inO. 
    Qed.
  End fixXeq. 

  (** extraction of evalVar *)
  (* evalVar *)
  Definition evalVar_time (a : assgn) := ((|a|) + 1) * (maxSize a + 1) + 1.
  Fact _term_evalVar : { time : UpToC evalVar_time & computableTime' evalVar (fun a _ => (1, fun v _ => (time a, tt))) }. 
  Proof. 
    exists_const c1. 
    { extract. solverec. erewrite !UpToC_le. unfold list_in_decb_time. set_consts. 
      set (c1' := C + 6). unfold evalVar_time. inst_with c1 c1'. 
      nia. }
    smpl_upToC_solve. 
  Qed.
  Instance term_evalVar : computableTime' evalVar _ := projT2 _term_evalVar. 

  (* evalLiteral*)
  Definition evalLiteral_time (a : assgn) := ((|a|) + 1) * (maxSize a + 1) + 1.
  Fact _term_evalLiteral : {time : UpToC evalLiteral_time & computableTime' evalLiteral (fun a _ => (1, fun l _ => (time a, tt)))}. 
  Proof. 
    exists_const c1. 
    { extract. solverec. erewrite !UpToC_le. unfold evalVar_time. 
      set_consts. set (c1' := C + c__eqbBool + 7). unfold evalLiteral_time. inst_with c1 c1'. lia. } 
    smpl_upToC_solve. 
  Qed.
  Instance term_evalLiteral : computableTime' evalLiteral _ := projT2 _term_evalLiteral. 

  (* evalClause *)
  Definition evalClause_time (p : assgn * clause) := let (a, C) := p in (|C| + 1) * (((|a|) + 1) * (maxSize a + 1)) + 1. 
  Fact _term_evalClause : { time : UpToC evalClause_time & computableTime' evalClause (fun a _ => (5, fun C _ => (time (a, C), tt))) }. 
  Proof. 
    exists_const c1. 
    { extract. recRel_prettify2; cycle 1.
      + rewrite !UpToC_le. unfold evalLiteral_time, evalClause_time. 
        cbn [length]. set_consts. set (c1' := 2*2*C + 22). inst_with c1 c1'. lia.
      + subst c1; solverec. } 
    smpl_upToC_solve. 
  Qed.
  Instance term_evalClause : computableTime' evalClause _ := projT2 _term_evalClause.

  Lemma evalClause_poly : isPoly evalClause_time. 
  Proof. 
    exists_poly p. [p]: intros n. 
    { intros (a & C). unfold evalClause_time. 
      rewrite !list_size_length. rewrite maxSize_enc_size. 
      rewrite size_prod. cbn. [p] : exact (n * n * n). 
      and_solve p. } 
    all: subst p; smpl_inO. 
  Qed.
  Arguments evalClause_time: simpl never. 

  (* evalCnf *)
  Definition evalCnf_time (p : assgn * cnf) := let (a, N) := p in sumn (map (fun C => evalClause_time (a, C)) N) + (|N|) + 1. 
  Fact _term_evalCnf : { time : UpToC evalCnf_time & computableTime' evalCnf (fun a _ => (5, fun N _ => (time (a, N), tt)))}. 
  Proof. 
    exists_const c1. 
    { extract. solverec; cycle 1. 
      + set (sumn _). rewrite UpToC_le.
        instantiate (c1 := c_of _term_evalClause + 21). subst c1. lia. 
      + subst c1. leq_crossout. 
    } 
    smpl_upToC_solve. 
  Qed.
  Instance term_evalCnf : computableTime' evalCnf _ := projT2 _term_evalCnf. 
  Arguments evalCnf_time : simpl never. 

  (* again: we would not want to use the above bound explicitly, so we give at least a polynomial bound which can be used. *)
  Lemma evalCnf_poly : isPoly evalCnf_time. 
  Proof. 
    exists_poly p. [p]: intros n. 
    { intros (a & N). unfold evalCnf_time. rewrite sumn_map_mono. 
      2: { intros x H. rewpoly evalClause_poly at 1. monopoly evalClause_poly at 1. 
        2: { instantiate (1 := size (enc (a, N))). rewrite !size_prod; cbn. now rewrite (list_el_size_bound H). } 
        inst_const. } 
      rewrite sumn_map_const. rewrite list_size_length. rewrite size_prod. 
      [p]: exact (n * isP__poly evalClause_poly n + n + 1). and_solve p. } 
    all: subst p; smpl_inO. 
  Qed.

  (** sat_verifierb *)
  Definition sat_verifierb_time (p : cnf * assgn) : nat := let '(N, a) := p in evalCnf_time (a, N) + 1. 
  Fact _term_sat_verifierb : { time : UpToC sat_verifierb_time & computableTime' sat_verifierb (fun p _ => (time p, tt))}. 
  Proof. 
    exists_const c1. 
    { extract. solverec. 
      rewrite !UpToC_le. set_consts. set (c1' := C + 10). inst_with c1 c1'. lia. 
    } 
    smpl_upToC_solve. 
  Qed.
  Instance term_sat_verifierb : computableTime' sat_verifierb _ := projT2 _term_sat_verifierb. 
End extraction.
       
(** We obtain that SAT is in NP *)
Require Import Undecidability.L.Complexity.NP. 
Lemma sat_NP : inNP (unrestrictedP SAT).
Proof.
  apply inNP_intro with (R:= fun (a : { cnf | True}) => sat_verifier (proj1_sig a)). 
  1 : apply linDec_polyTimeComputable.
  2 : {
    exists (fun n => n * (1 + c__listsizeCons + c__listsizeNil)). 
    3, 4: smpl_inO.
    - unfold SAT, sat_verifier.
      intros (cn & ?) a H.  cbn. exists a; tauto.  
    - unfold SAT, sat_verifier. intros (cn & ?) [a H]. exists (compressAssignment a cn). split. 
      + apply compressAssignment_cnf_equiv in H. cbn. apply H.
      + apply assignment_small_size. cbn. apply compressAssignment_small. 
  }

  unfold inTimePoly. exists_poly p. repeat split.  
  { exists (sat_verifierb). 
    + eexists. eapply computesTime_timeLeq. 2: apply term_sat_verifierb.
      cbn. intros [N a] _. split; [ | easy]. rewrite !UpToC_le. unfold sat_verifierb_time. 
      rewpoly evalCnf_poly. monopoly (evalCnf_poly). 2: { instantiate (1 := size (enc (N, a))). rewrite !size_prod. cbn; lia. }
      set (L.size _). [p]: intros n. and_solve p.
    + intros [N a] ?. cbn. apply sat_verifierb_correct.
  } 
  all: subst p; smpl_inO. 
Qed.
