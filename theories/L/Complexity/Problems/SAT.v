From Undecidability.L.Complexity.Cook Require Import Prelim.
From Undecidability.L.Complexity.Problems Require Export SharedSAT.
Require Import Lia. 
From Undecidability.L.Datatypes Require Import LLists. 

From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Import  LProd LOptions LBool LLNat LLists LUnit.
From Undecidability.L.Complexity Require Import PolyBounds. 

(*Conjunctive normal forms (need not be canonical)*)
Notation var := (nat) (only parsing). 
Notation literal := ((bool * var)%type) (only parsing).
Notation clause := (list literal) (only parsing). 
Notation cnf := (list clause) (only parsing).


(*Assignments as lists of natural numbers: contain the indices of variables that are mapped to true *)
Notation assgn := (list nat). 
Implicit Types (a : assgn) (N : cnf) (C : clause) (l :literal).

Definition evalLiteral a l : bool := match l with
  | (s, v) => Bool.eqb (evalVar a v) s 
end. 

(*Empty disjunction evaluates to false*)
Fixpoint evalClause a C := 
  match C with 
  | [] => false
  | (l :: C) => evalClause a C || evalLiteral a l
  end. 

(*Empty conjunction evaluates to true *)
Fixpoint evalCnf a N := 
  match N with 
  | [] => true
  | (C :: N) => evalCnf a N && evalClause a C
  end. 

(*more helpful properties *)
(*a characterisation of one processing step of evalClause *)
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
Inductive varBound_clause (n : nat) : clause -> Prop :=
  | varBound_clauseB : varBound_clause n []
  | varBound_clauseS : forall b v C, v < n -> varBound_clause n C -> varBound_clause n ((b, v) :: C).  

Inductive varBound_cnf (n : nat) : cnf -> Prop :=
   | varBound_cnfB : varBound_cnf n [] 
   | varBound_cnfS : forall C N, varBound_clause n C -> varBound_cnf n N -> varBound_cnf n (C :: N).  

Hint Constructors varBound_clause varBound_cnf. 

Lemma varBound_clause_iff (n : nat) C : varBound_clause n C <-> forall (s : bool) v, (s, v) el C -> v < n.
Proof.
  split.
  - induction 1.
    + intros s v []. 
    + intros s v0 [H1 | H1].
      * inv H1. now apply H. 
      * now apply IHvarBound_clause with (s := s). 
  - induction C.
    + intros. constructor. 
    + intros. destruct a. constructor.
      * apply H with (s := b). firstorder.  
      * apply IHC. firstorder.  
Qed. 

Lemma varBound_cnf_iff (n : nat) N : varBound_cnf n N <-> forall C, C el N -> varBound_clause n C.
Proof.
  split.
  - induction 1. 
    + intros C [].
    + intros C' [-> |Hel]. assumption. now apply IHvarBound_cnf. 
  - intros H. induction N; constructor.
    + now apply H. 
    + apply IHN. firstorder.
Qed. 

Lemma varBound_clause_monotonic C (n n' : nat) : n <= n' -> varBound_clause n C -> varBound_clause n' C. 
Proof. intros H1 H2. induction H2. constructor. constructor. lia. auto. Qed. 

Lemma varBound_cnf_monotonic N (n n' : nat) : n <= n' -> varBound_cnf n N -> varBound_cnf n' N.
Proof.
  intros H1 H2. induction H2; constructor.
  now apply varBound_clause_monotonic with (n:= n). assumption. 
Qed.

Lemma varBound_cnf_app N1 N2 (n : nat) : varBound_cnf n N1 /\ varBound_cnf n N2 <-> varBound_cnf n (N1 ++ N2).
Proof.
  induction N1; cbn. 
  - split; [ tauto | intros H; split; eauto  ]. 
  - split. 
    + intros (H1 & H2). inv H1. constructor; [eauto | now apply IHN1].
    + intros H. inv H. apply IHN1 in H3 as (H3 & H4). split; eauto. 
Qed. 

(*size of CNF in terms of number of operators *)
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

(** * Verifier for SAT*)
(** The certificate is a satisfying assignment.
  The assignment needs to be short enough and must not contain variables not occuring in the CNF.
*)

(*produce a list (possibly containing duplicates) of variables occuring in a CNF *)
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

Lemma list_dupfree_incl_length (X : eqType) (a b : list X) : a <<= b -> dupfree a -> |a| <= |b|. 
Proof. 
  intros H1 H2. eapply NoDup_incl_length. 
  - apply dupfree_Nodup, H2.
  - apply H1. 
Qed. 

Lemma rem_app_eq (X : eqType) (l1 l2 : list X) (x : X) : rem (l1 ++ l2) x = rem l1 x ++ rem l2 x. 
Proof. 
  induction l1; cbn; [easy | ].
  destruct Dec; cbn. 
  - fold (rem (l1 ++ l2) x). rewrite IHl1. easy.
  - fold (rem (l1 ++ l2) x). now rewrite IHl1. 
Qed. 

Lemma list_rem_size_le (X : eqType) `{H : registered X} (l : list X) x : size (enc (rem l x)) <= size (enc l). 
Proof. 
  induction l. 
  - cbn. lia. 
  - cbn. destruct Dec; cbn; rewrite !list_size_cons, IHl; lia. 
Qed. 

Lemma list_incl_dupfree_size (X : eqType) `{registered X} (a b : list X) : a <<= b -> dupfree a -> size (enc a) <= size (enc b). 
Proof. 
  intros H1 H2.  revert b H1.
  induction H2 as [ | a0 a H1 H2 IH]; intros. 
  - cbn. rewrite !size_list. cbn. lia.
  - specialize (IH (rem b a0)). 
    rewrite list_size_cons.
    cbn. rewrite IH. 
    2: { 
      assert (rem (a0 :: a) a0 = a).  
      { cbn. destruct Dec; [congruence | ]. cbn. 
       fold (rem a a0). now rewrite rem_id. 
      } 
      rewrite <- H3. now apply rem_mono. 
    } 
    specialize (H0 a0 (or_introl eq_refl)). apply In_explicit in H0 as (b1 & b2 & ->).
    rewrite !size_list, !rem_app_eq, !map_app, !sumn_app. cbn. 
    destruct Dec; cbn; [congruence | ]. 
    pose (elem_size := fun (x : X) => size (enc x) + c__listsizeCons). 
    fold elem_size.
    enough (sumn (map elem_size (rem b1 a0)) <= sumn (map elem_size b1) /\ sumn (map elem_size (rem b2 a0)) <= sumn (map elem_size b2)) as H0.
    { destruct H0 as [-> ->]. nia. }
    specialize (list_rem_size_le b1 a0) as F1. 
    specialize (list_rem_size_le b2 a0) as F2. 
    rewrite !size_list in F1. rewrite !size_list in F2. 
    fold elem_size in F1. fold elem_size in F2.
    split; nia. 
Qed. 

Lemma assignment_small_size N a : assignment_small N a -> size (enc a) <= size (enc N) * (1 + c__listsizeCons + c__listsizeNil). 
Proof. 
  intros [H1 H2].
  enough (size (enc a) <= size (enc (varsOfCnf N))) as H.
  { rewrite H. apply varsOfCnf_size. }
  now eapply list_incl_dupfree_size.
Qed. 

Definition sat_verifier N (a : assgn) :=
  evalCnf a N = true /\ assignment_small N a. 

(*we need to show that, given a satisfying assignment for a CNF, we can obtain a small assignment that still satisfies the CNF*)
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

  Hint Constructors dupfree. 
  Lemma dupfree_dedup (a : list X) : dupfree (dedup a). 
  Proof. 
    induction a; cbn; [ eauto| ]. 
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

(*now that we've got the tools to verify the verifier, let's build a boolean verifier and prove its correctness*)
Definition assignment_small_decb N a := list_incl_decb Nat.eqb a (varsOfCnf N) && dupfreeb Nat.eqb a. 
Definition sat_verifierb (input : cnf * assgn) :=
  let (N, a) := input in assignment_small_decb N a && evalCnf a N.

Lemma assignment_small_decb_iff N a : assignment_small_decb N a = true <-> assignment_small N a. 
Proof. 
  unfold assignment_small_decb, assignment_small. 
  rewrite andb_true_iff. 
  rewrite list_incl_decb_iff; [ | symmetry; apply Nat.eqb_eq]. 
  rewrite dupfreeb_iff; [ | symmetry; apply Nat.eqb_eq]. 
  easy.
Qed. 

Lemma sat_verifierb_correct N a : sat_verifier N a <-> sat_verifierb (N, a) = true.
Proof. 
  unfold sat_verifier, sat_verifierb. rewrite and_comm. 
  rewrite andb_true_iff. rewrite assignment_small_decb_iff. 
  tauto. 
Qed. 

(** A computable notion of boundedness *)
Definition clause_maxVar C := fold_right (fun '(_, v) acc => Nat.max acc v) 0 C. 
Definition cnf_maxVar N := fold_right (fun C acc => Nat.max acc (clause_maxVar C)) 0 N.

Lemma cnf_maxVar_app N1 N2 : cnf_maxVar (N1 ++ N2) = Nat.max (cnf_maxVar N1) (cnf_maxVar N2). 
Proof. 
  induction N1. 
  - easy.
  - cbn. fold (cnf_maxVar (N1 ++ N2)). fold (cnf_maxVar N1). rewrite IHN1. lia. 
Qed. 

Lemma clause_maxVar_bound C : varBound_clause (S (clause_maxVar C)) C.
Proof.
  induction C.
  - cbn. constructor.
  - destruct a. constructor; cbn.
    + lia.   
    + eapply varBound_clause_monotonic.
      2: apply IHC. unfold clause_maxVar. cbn. lia. 
Qed.

Lemma cnf_maxVar_bound N : varBound_cnf (S (cnf_maxVar N)) N.
Proof.
  induction N.
  - cbn; constructor.
  - constructor.
    + cbn. eapply varBound_clause_monotonic. 2: apply clause_maxVar_bound. lia. 
    + eapply varBound_cnf_monotonic. 2: apply IHN. cbn. unfold cnf_maxVar. lia.  
Qed. 

(** In principle, we would expect a strict inequality here. The reason for non-strictness is that cnf_maxVar returns 0 in case of an empty CNF. *)
Lemma clause_maxVar_bound_le C n : varBound_clause n C -> clause_maxVar C <= n.
Proof. 
  induction 1 as [ | ? ? ? ? ? IH]; cbn; [lia | ].
  rewrite IH. lia. 
Qed. 

Lemma cnf_maxVar_bound_le N n : varBound_cnf n N -> cnf_maxVar N <= n. 
Proof. 
  induction 1 as [ | ? ? ? ? IH]; cbn; [ lia | ].
  rewrite IH. rewrite clause_maxVar_bound_le by apply H. lia. 
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
    (*nia and leq_crossout need some help to see that this holds*)
    replace_le (c__natsizeS * (clause_maxVar a + 1) * (size_clause a + 1) + c__clauseSize1 * (size_clause a + 1) + (c__natsizeS * (cnf_maxVar c + 1) * (size_cnf c + 1) + (size_cnf c + 1) * c__cnfSize1) + c__listsizeCons) 
    with (c__natsizeS * (Nat.max (cnf_maxVar c) (clause_maxVar a) + 1) * (size_clause a + size_cnf c + 2) + c__clauseSize1 * (size_clause a + 1) + (size_cnf c + 1) * c__cnfSize1 + c__listsizeCons) by nia. 
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


(** extraction of evalVar *)
Definition c__evalVar := 7. 
Definition evalVar_time a (v : var) := list_in_decb_time (fun x y => c__nat_eqb2 + nat_eqb_time x y) a v + c__evalVar.
Instance term_evalVar : computableTime' evalVar (fun a _ => (1, fun v _ => (evalVar_time a v, tt))). 
Proof. 
  extract. solverec. unfold evalVar_time, c__evalVar; solverec. 
Defined. 

Definition c__evalVarBound := c__nat_eqb2 + c__list_in_decb. 
Definition poly__evalVar n := (n + 1) * (c__evalVarBound + (n + size(enc tt)+ 1) * c__nat_eqb) + c__evalVar.
Lemma evalVar_time_bound a v : evalVar_time a v <= poly__evalVar (size (enc a) + size (enc v)). 
Proof. 
  unfold evalVar_time. 
  change (fun x y => c__nat_eqb2 + nat_eqb_time x y) with ((fun z x y => c__nat_eqb2 + nat_eqb_time x y) tt). 
  rewrite list_in_decb_time_bound_env. 
  2: { 
    split. 
    - intros. rewrite nat_eqb_time_bound_l. replace_le (size (enc a0)) with (size (enc a0) + size (enc b) + size (enc y)) by nia at 1. instantiate (2 := fun n => c__nat_eqb2 + (n + 1) * c__nat_eqb).
      cbn -[Nat.add]. instantiate (1 := registered_unit_enc). nia. 
    - smpl_inO. 
  } 
  rewrite list_size_length. unfold poly__evalVar, c__evalVarBound. nia. 
Qed. 

Lemma evalVar_poly : monotonic poly__evalVar /\ inOPoly poly__evalVar. 
Proof. 
  split; unfold poly__evalVar; smpl_inO. 
Qed. 


Definition c__eqbBool := 7.
Instance term_bool_eqb : computableTime' Bool.eqb (fun _ _ => (1, fun _ _ => (c__eqbBool, tt))). 
Proof.
  extract. unfold c__eqbBool.
  solverec. 
Qed.

(*evalLiteral*)
Definition c__evalLiteral := c__eqbBool + 7. 
Definition evalLiteral_time a (l : literal) := match l with (_, v) => evalVar_time a v + c__evalLiteral end. 
Instance term_evalLiteral : computableTime' evalLiteral (fun a _ => (1, fun l _ => (evalLiteral_time a l, tt))). 
Proof. 
  extract. solverec. unfold c__evalLiteral. solverec. 
Qed. 

Definition c__evalLiteralBound := 1. 
Definition poly__evalLiteral n := poly__evalVar n + c__evalLiteral.
Lemma evalLiteral_time_bound a l : evalLiteral_time a l <= poly__evalLiteral (size (enc a) + size (enc l)). 
Proof. 
  unfold evalLiteral_time. destruct l. rewrite evalVar_time_bound. 
  poly_mono evalVar_poly. 
  2: (replace_le (size (enc n)) with (size (enc (b, n))) by (rewrite size_prod; cbn; lia)); reflexivity. 
  unfold poly__evalLiteral; lia.
Qed. 
Lemma evalLiteral_poly : monotonic poly__evalLiteral /\ inOPoly poly__evalLiteral. 
Proof. 
  split; unfold poly__evalLiteral; smpl_inO; apply evalVar_poly.
Qed. 


(*evalClause *)

Definition c__evalClause := 17.
Fixpoint evalClause_time a (C : clause) :=
  match C with 
  | [] => 0
  | (l :: C) => evalLiteral_time a l + evalClause_time a C
  end + c__evalClause.
Instance term_evalClause : computableTime' evalClause (fun a _ => (5, fun C _ => (evalClause_time a C, tt))). 
Proof. 
  extract. solverec. 
  all: unfold c__evalClause; solverec. 
Defined.

Definition poly__evalClause n := n * poly__evalLiteral n + (n + 1) * c__evalClause.
Lemma evalClause_time_bound a C : evalClause_time a C <= poly__evalClause (size (enc a) + size (enc C)). 
Proof. 
  unfold evalClause_time. induction C. 
  - unfold poly__evalClause. nia. 
  - rewrite evalLiteral_time_bound. rewrite IHC. 
    poly_mono evalLiteral_poly. 
    2: { instantiate (1 := size (enc a) + size (enc (a0 :: C))). rewrite list_size_cons. nia. }
    unfold poly__evalClause. poly_mono evalLiteral_poly at 2. 
    2: { instantiate (1 := size (enc a) + size (enc (a0 :: C))). rewrite list_size_cons. nia. }
    rewrite list_size_cons. unfold c__listsizeCons. leq_crossout. 
Qed.
Lemma evalClause_poly : monotonic poly__evalClause /\ inOPoly poly__evalClause. 
Proof. 
  split; unfold poly__evalClause; smpl_inO; apply evalLiteral_poly. 
Qed.

(*evalCnf *)
Definition c__evalCnf := 21.
Fixpoint evalCnf_time a (N : cnf) :=
  match N with 
  | [] => 0
  | (C :: N) => evalClause_time a C + evalCnf_time a N
  end + c__evalCnf.
Instance term_evalCnf : computableTime' evalCnf (fun a _ => (5, fun c _ => (evalCnf_time a c, tt))). 
Proof. 
  extract. solverec. 
  all: unfold c__evalCnf; solverec. 
Defined.

Definition poly__evalCnf n := n * poly__evalClause n + (n + 1) * c__evalCnf.
Lemma evalCnf_time_bound a N : evalCnf_time a N <= poly__evalCnf (size (enc a) + size (enc N)). 
Proof. 
  unfold evalCnf_time. induction N. 
  - unfold poly__evalCnf. nia. 
  - rewrite evalClause_time_bound. rewrite IHN. 
    poly_mono evalClause_poly. 
    2: { instantiate (1 := size (enc a) + size (enc (a0:: N))). rewrite list_size_cons. nia. } 
    unfold poly__evalCnf. 
    poly_mono evalClause_poly at 2. 
    2: { instantiate (1 := size (enc a) + size (enc (a0 :: N))). rewrite list_size_cons. nia. }
    rewrite list_size_cons. unfold c__listsizeCons. leq_crossout.
Qed.
Lemma evalCnf_poly : monotonic poly__evalCnf /\ inOPoly poly__evalCnf. 
Proof. 
  split; unfold poly__evalCnf; smpl_inO; apply evalClause_poly. 
Qed. 

(*varsOfLiteral *)
Definition c__varsOfLiteral := 7.
Instance term_varsOfLiteral : computableTime' varsOfLiteral (fun l _ => (c__varsOfLiteral, tt)). 
Proof. 
  extract. solverec. unfold c__varsOfLiteral; solverec. 
Defined. 

(*varsOfClause *)
Definition c__varsOfClause := 2.
Definition varsOfClause_time (c : clause) := map_time (fun _ => c__varsOfLiteral) c + concat_time (map varsOfLiteral c) + c__varsOfClause. 
Instance term_varsOfClause : computableTime' varsOfClause (fun c _ => (varsOfClause_time c, tt)). 
Proof. 
  extract. solverec. unfold varsOfClause_time, c__varsOfClause. solverec. 
Defined. 

Definition c__varsOfClauseBound1 := (c__varsOfLiteral + 1) * (c__map + 1). 
Definition c__varsOfClauseBound2 := (c__listsizeCons + c__listsizeNil + 1). 
Definition poly__varsOfClause n := (n + 1) * c__varsOfClauseBound1 + poly__concat (n * c__varsOfClauseBound2) + c__varsOfClause.
Lemma varsOfClause_time_bound c : varsOfClause_time c <= poly__varsOfClause (size (enc c)).
Proof. 
  unfold varsOfClause_time. 
  change (fun _ : bool * nat => c__varsOfLiteral) with ((fun _ (_ : bool * nat) => c__varsOfLiteral) tt). 
  rewrite map_time_bound_env. 
  2: { 
    split.
    - intros. instantiate (1 := registered_unit_enc). instantiate (1 := fun (n : nat) => c__varsOfLiteral). cbn; nia.
    - smpl_inO. 
  } 
  rewrite concat_time_bound. 
  poly_mono concat_poly. 
  2: { 
    instantiate (1 := size (enc c) + (|c|) * (c__listsizeCons + c__listsizeNil)). 
    induction c; cbn -[Nat.add]; [easy | ].
    rewrite !list_size_cons. rewrite varsOfLiteral_size, IHc. nia.
  }
  unfold poly__varsOfClause, c__varsOfClauseBound1, c__varsOfClauseBound2. 
  poly_mono concat_poly. 
  2 : { instantiate (1 := size (enc c) * (c__listsizeCons + c__listsizeNil + 1)). rewrite list_size_length. 
        nia.
  }
  rewrite list_size_length. 
  nia. 
Qed. 
Lemma varsOfClause_poly : monotonic poly__varsOfClause /\ inOPoly poly__varsOfClause. 
Proof. 
  split; unfold poly__varsOfClause; smpl_inO. 
  - apply concat_poly. 
  - apply inOPoly_comp; [apply concat_poly | apply concat_poly | smpl_inO]. 
Qed. 

(*varsOfCnf *)
Definition c__varsOfCnf := 2.
Definition varsOfCnf_time (cn : cnf) := map_time (fun cl => varsOfClause_time cl) cn + concat_time (map varsOfClause cn) + c__varsOfCnf.
Instance term_varsOfCnf : computableTime' varsOfCnf (fun c _ => (varsOfCnf_time c, tt)). 
Proof. 
  extract. solverec. unfold varsOfCnf_time, c__varsOfCnf; solverec. 
Defined. 

Definition c__varsOfCnfBound := (c__listsizeCons + c__listsizeNil + 1). 
Definition poly__varsOfCnf n := (n + 1) * (poly__varsOfClause (size (enc tt) + n) + 1) * (c__map + 1) + poly__concat (n * c__varsOfCnfBound + c__listsizeNil) + c__varsOfCnf.
Lemma varsOfCnf_time_bound c : varsOfCnf_time c <= poly__varsOfCnf (size (enc c)).
Proof. 
  unfold varsOfCnf_time. 
  change (fun cl => varsOfClause_time cl) with ((fun _ cl => varsOfClause_time cl) tt). 
  rewrite map_time_bound_env. 
  2: { 
    split.
    - intros. instantiate (1 := registered_unit_enc). 
      rewrite varsOfClause_time_bound. poly_mono varsOfClause_poly. 
      2: { instantiate (1 := size (enc env) + size (enc ele)); lia. }
      reflexivity.
    - apply varsOfClause_poly.
  } 
  rewrite concat_time_bound. 
  poly_mono concat_poly. 
  2: { 
    instantiate (1 := (size (enc c) * (c__listsizeCons + c__listsizeNil + 1)) + c__listsizeNil). 
    induction c; cbn -[Nat.add]; [rewrite size_list; cbn -[Nat.add]; nia | ].
    rewrite !list_size_cons. rewrite varsOfClause_size, IHc. rewrite list_size_length. nia.
  }
  unfold poly__varsOfCnf, c__varsOfCnfBound.
  rewrite list_size_length. 
  nia. 
Qed. 
Lemma varsOfCnf_poly : monotonic poly__varsOfCnf /\ inOPoly poly__varsOfCnf. 
Proof. 
  split; unfold poly__varsOfCnf; smpl_inO. 
  - apply varsOfClause_poly.
  - apply concat_poly. 
  - apply inOPoly_comp; [apply varsOfClause_poly | apply varsOfClause_poly | smpl_inO].
  - apply inOPoly_comp; [apply concat_poly | apply concat_poly | smpl_inO]. 
Qed. 

(*assignment_small_decb *)
Definition c__assignmentSmallDecb := 17.
Definition assignment_small_decb_time (cn : cnf) a := varsOfCnf_time cn + list_incl_decb_time (fun x y => c__nat_eqb2 + nat_eqb_time x y) a (varsOfCnf cn) + dupfreeb_time (fun x y => c__nat_eqb2 + nat_eqb_time x y) a + c__assignmentSmallDecb.
Instance term_assignment_small_decb : computableTime' assignment_small_decb (fun cn _ => (1, fun a _ => (assignment_small_decb_time cn a, tt))). 
Proof. 
  extract. solverec. unfold assignment_small_decb_time, c__assignmentSmallDecb. solverec. 
Defined. 

(*we first bound the components separately *)
Definition c__assignmentSmallDecbBound1 := (1 + c__listsizeCons + c__listsizeNil).
Definition c__assignmentSmallDecbBound2 := c__nat_eqb2 + c__list_in_decb.
Definition poly__assignmentSmallDecb1 n := (n + 1) * (n * c__assignmentSmallDecbBound1 + 1) * (c__assignmentSmallDecbBound2 + (n * c__assignmentSmallDecbBound1 + n + size (enc tt) + 1) * c__nat_eqb) + (n + 1) * c__list_incl_decb.
Lemma assignment_small_decb_time_bound1 a cn: list_incl_decb_time (fun x y => c__nat_eqb2 + nat_eqb_time x y)a (varsOfCnf cn) <= poly__assignmentSmallDecb1 (size (enc cn) + size (enc a)).
Proof. 
  change (fun x y => c__nat_eqb2 + nat_eqb_time x y) with ((fun env x y => c__nat_eqb2 + nat_eqb_time x y) tt). 
  rewrite list_incl_decb_time_bound_env. 
  2: { 
    split. 
    - intros x y env. rewrite nat_eqb_time_bound_l. 
      instantiate (1 := registered_unit_enc).
      instantiate (1 := fun n => c__nat_eqb2 + (n + 1) * c__nat_eqb). nia. 
    - smpl_inO. 
  }
  rewrite !list_size_length. rewrite varsOfCnf_size.
  unfold poly__assignmentSmallDecb1, c__assignmentSmallDecbBound1, c__assignmentSmallDecbBound2.

  (*help nia to achieve an acceptable rt *)
  replace_le (size (enc a)) with (size (enc cn) + size (enc a)) by lia at 1. 
  replace_le (size (enc cn)) with (size (enc cn) + size (enc a)) by lia at 2.
  replace_le (size (enc cn)) with (size (enc cn) + size (enc a)) by lia at 3. 
  replace_le (size (enc a)) with (size (enc cn) + size (enc a)) by lia at 4. 
  replace_le (size (enc a)) with (size (enc cn) + size (enc a)) by lia at 5. 
  generalize (size (enc cn) + size (enc a)). intros n. nia.
Qed.
Lemma assignment_small_decb_poly1 : monotonic poly__assignmentSmallDecb1 /\ inOPoly poly__assignmentSmallDecb1. 
Proof. 
  unfold poly__assignmentSmallDecb1; split; smpl_inO.
Qed. 

Definition poly__assignmentSmallDecb2 n := (n + 1) * (n + 1) * (c__nat_eqb2 + (2 * n + size (enc tt) + 1) * c__nat_eqb + c__dupfreeBound).
Lemma assignment_small_decb_time_bound2 a : dupfreeb_time (fun x y => c__nat_eqb2 + nat_eqb_time x y) a <= poly__assignmentSmallDecb2 (size (enc a)). 
Proof. 
  change (fun x y => c__nat_eqb2 + nat_eqb_time x y) with ((fun env x y => c__nat_eqb2 + nat_eqb_time x y) tt).
  rewrite dupfreeb_time_bound_env. 
  2: { 
    split.
    - intros x y env. rewrite nat_eqb_time_bound_l. 
      instantiate (1 := registered_unit_enc).
      instantiate (1 := fun n => c__nat_eqb2 + (n + 1) * c__nat_eqb). nia. 
    - smpl_inO. 
  } 
  rewrite list_size_length. 
  unfold poly__assignmentSmallDecb2. nia.
Qed.
Lemma assignment_small_decb_poly2 : monotonic poly__assignmentSmallDecb2 /\ inOPoly poly__assignmentSmallDecb2. 
Proof. 
  unfold poly__assignmentSmallDecb2; split; smpl_inO.
Qed.

Definition c__assignmentSmallDecbBound3 := c__nat_eqb2 + c__dupfreeBound.
  
Definition poly__assignmentSmallDecb n := 
  poly__varsOfCnf n 
  + poly__assignmentSmallDecb1 n 
  + poly__assignmentSmallDecb2 n
  + c__assignmentSmallDecb.
Lemma assignment_small_decb_time_bound cn a : assignment_small_decb_time cn a <= poly__assignmentSmallDecb (size (enc cn) + size (enc a)). 
Proof. 
  unfold assignment_small_decb_time.
  rewrite varsOfCnf_time_bound. 
  rewrite assignment_small_decb_time_bound1. 
  rewrite assignment_small_decb_time_bound2.  
  poly_mono varsOfCnf_poly. 
  2: { instantiate (1 := size (enc cn) + size (enc a)); lia. }
  poly_mono assignment_small_decb_poly2.
  2: { instantiate (1 := size (enc cn) + size (enc a)); lia. } 
  unfold poly__assignmentSmallDecb; lia. 
Qed. 

Lemma assignment_small_decb_poly : monotonic poly__assignmentSmallDecb /\ inOPoly poly__assignmentSmallDecb.
Proof. 
  unfold poly__assignmentSmallDecb; split; smpl_inO.
  3, 6: apply assignment_small_decb_poly2. 
  2, 4: apply assignment_small_decb_poly1. 
  1, 2: apply varsOfCnf_poly.
Qed. 

(*sat_verifierb *)
Definition c__satVerifierb := 16. 
Definition sat_verifierb_time (p : cnf * assgn) := match p with (cn, a) => assignment_small_decb_time cn a + evalCnf_time a cn + c__satVerifierb end.
Instance term_sat_verifierb : computableTime' sat_verifierb (fun p _ => (sat_verifierb_time p, tt)). 
Proof. 
  extract. solverec. unfold sat_verifierb_time, c__satVerifierb. solverec. 
Defined. 

Definition poly__sat_verifierb n := poly__assignmentSmallDecb n + poly__evalCnf n + c__satVerifierb.
Lemma sat_verifierb_time_bound p : sat_verifierb_time p <= poly__sat_verifierb (size (enc p)). 
Proof. 
  unfold sat_verifierb_time. 
  destruct p as [cn a].
  rewrite assignment_small_decb_time_bound.
  rewrite evalCnf_time_bound. 
  rewrite size_prod; cbn.

  poly_mono assignment_small_decb_poly. 
  2: { instantiate (1 := size (enc cn) + size (enc a) + 4). lia. }
  poly_mono evalCnf_poly.
  2: { instantiate (1 := size (enc cn) + size (enc a) + 4). lia. }
  unfold poly__sat_verifierb. nia.
Qed. 
Lemma sat_verifierb_poly : monotonic poly__sat_verifierb /\ inOPoly poly__sat_verifierb. 
Proof. 
  split; unfold poly__sat_verifierb; smpl_inO. 
  2, 4: apply evalCnf_poly.
  1, 2: apply assignment_small_decb_poly.
Qed. 

(** We obtain that SAT is in NP *)
Lemma sat_NP : inNP (unrestrictedP SAT).
Proof.
  apply inNP_intro with (R:= fun (a : { cnf | True}) => sat_verifier (proj1_sig a)). 
  1 : apply linDec_polyTimeComputable.
  2 : {
    exists (fun n => n * (1 + c__listsizeCons + c__listsizeNil)). 
    3, 4: smpl_inO.
    - unfold SAT, sat_verifier.
      intros (cn & ?) a (H1 & H2). cbn. exists a; tauto.  
    - unfold SAT, sat_verifier. intros (cn & ?) [a H]. exists (compressAssignment a cn). split. 
      + apply compressAssignment_cnf_equiv in H. cbn. split; [apply H | apply compressAssignment_small]. 
      + apply assignment_small_size. cbn. apply compressAssignment_small. 
  }

  unfold inTimePoly. exists poly__sat_verifierb. repeat split.
  - exists (sat_verifierb). 
    + eexists. 
      eapply computesTime_timeLeq. 2: apply term_sat_verifierb.
      cbn. intros [N a] _. split; [ apply sat_verifierb_time_bound | easy]. 
    + intros [N a] ?. cbn. apply sat_verifierb_correct.
  - apply sat_verifierb_poly. 
  - apply sat_verifierb_poly. 
Qed. 
