From PslBase Require Import Base. 
From PslBase Require Import Vectors.Vectors. 
From PslBase Require Import FiniteTypes. 
From Undecidability Require Import L.Complexity.Cook.Prelim.
Require Import Lia.


(*use an explicit representation instead of vectors of size 3 since this will make the problem closer to the flattened extractable problem *)
Inductive TCSRWinP (Sigma : finType) := winp : Sigma -> Sigma -> Sigma -> TCSRWinP Sigma. 
Record TCSRWin (Sigma : finType) := {
                                            prem : TCSRWinP Sigma;
                                            conc : TCSRWinP Sigma
                                   }.

Definition TCSRWinP_to_list (sig : finType) (a : TCSRWinP sig) := match a with winp a b c => [a; b; c] end. 
Coercion TCSRWinP_to_list : TCSRWinP >-> list. 

Notation "'{' a ',' b ',' c '}'" := (winp a b c) (format "'{' a ',' b ',' c '}'"). 
Notation "a / b" := ({|prem := a; conc := b|}). 

Instance TCSRWinP_eqTypeC (Sigma : finType) : eq_dec (TCSRWinP Sigma). 
Proof.
  unfold dec. destruct Sigma. destruct type. decide equality. 
  destruct (eqType_dec e1 e4); auto. 
  destruct (eqType_dec e0 e3); auto. 
  destruct (eqType_dec e e2); auto. 
Defined. 

Instance TCSRWin_eqTypeC (Sigma : finType) : eq_dec (TCSRWin Sigma). 
Proof. 
  unfold dec. decide equality.
  destruct (TCSRWinP_eqTypeC conc0 conc1); auto. 
  destruct (TCSRWinP_eqTypeC prem0 prem1); auto. 
Defined. 

Record TCSR := {
               Sigma : finType;
               init : list Sigma;  (* length is encoded implicitly as the length of init*) 
               windows : list (TCSRWin Sigma);
               final : list (list Sigma);
               steps : nat
             }.

Implicit Type (C : TCSR).

Section fixInstance.
  Variable (Sigma : finType).
  Variable (init : list Sigma).
  Variable (windows : list (TCSRWin Sigma)).
  Variable (final : list (list Sigma)).
  Variable (steps : nat). 

  Definition string := list Sigma. 
  Definition window := TCSRWin Sigma. 

  Implicit Type (s a b: string). 
  Implicit Type (r rule : window).
  Implicit Type (x y : Sigma).

  Definition isRule r := r el windows.
  Lemma isRule_length r : length (prem r) = 3 /\ length (conc r) = 3.
  Proof. 
    intros. destruct r. 
    cbn. destruct prem0, conc0. now cbn. 
  Qed. 

  (* the final constraint*)
  Definition satFinal s := exists subs, subs el final /\ substring subs s.

  (* rewrites inside a string *)
  Definition rewritesHead rule a b :=
    prefix (prem rule) a /\ prefix (conc rule) b.

  Lemma rewritesHead_length_inv rule a b : rewritesHead rule a b -> isRule rule -> length a >= 3 /\ length b >= 3. 
  Proof. 
    intros. unfold rewritesHead, prefix in *. firstorder.
    - rewrite H. rewrite app_length, (proj1 (isRule_length rule)). lia.  
    - rewrite H1. rewrite app_length, (proj2 (isRule_length rule)). lia. 
  Qed. 

  Definition rewritesAt rule (i : nat) a b := rewritesHead rule (skipn i a) (skipn i b).
  Lemma rewritesAt_head rule a b : rewritesHead rule a b <-> rewritesAt rule 0 a b. 
  Proof. 
    unfold rewritesAt.
    rewrite <- firstn_skipn with (n:= 0) (l:= a) at 1.
    rewrite <- firstn_skipn with (n:= 0) (l:= b) at 1.
    repeat rewrite firstn_O; now cbn. 
  Qed. 

  Lemma rewritesAt_step rule a b x y (i:nat) : rewritesAt rule i a b <-> rewritesAt rule (S i) (x :: a) (y:: b). 
  Proof. intros. unfold rewritesAt. now cbn. Qed. 

  (*validity of a rewrite *)
  Inductive valid : string -> string -> Prop :=
  | validB: valid [] [] 
  | validSA a b x y: valid a b -> length a < 2 -> valid (x:: a) (y:: b)
  | validS a b x y rule: valid a b -> rule el windows -> rewritesHead rule (x::a) (y::b) -> valid (x::a) (y::b). 

  Lemma valid_length_inv a b : valid a b -> length a = length b. 
  Proof.
    induction 1. 
    - now cbn.
    - cbn; congruence.
    - cbn; congruence. 
  Qed. 

  Definition validExplicit a b := length a = length b /\ forall i, 0 <= i < length a - 2  -> exists rule, rule el windows  /\ rewritesAt rule i a b.

  Lemma valid_iff a b :
    valid a b <-> validExplicit a b.
  Proof.
    unfold validExplicit. split.
    - induction 1. 
      + cbn; split; [reflexivity | ]. 
        intros; lia. 
      + destruct IHvalid as (IH1 & IH2). split; [cbn; congruence | ]. 
        cbn [length]; intros. lia. 
      + destruct IHvalid as (IH1 & IH2); split; [cbn; congruence | ].
        cbn [length]; intros.
        destruct i. 
        * eauto. 
        * specialize (rewritesHead_length_inv H1) as (H3 & H4); [assumption | ]. cbn in H3.
          assert (0 <= i < (|a|) - 2) by lia.
          eauto. 
    - revert b. induction a; intros b (H1 & H2). 
      + inv_list. constructor. 
      + inv_list. destruct (le_lt_dec 2 (length a0)). 
        * cbn [length] in H2.
          assert (0 <= 0 < S (|a0|) - 2) by lia. destruct (H2 0 H) as (rule & H3 & H4). 
          eapply (@validS a0 b a e rule). 2-3: assumption. 
          apply IHa. split; [congruence | ]. 
          intros. assert (0 <= S i < S (|a0|) - 2) by lia. 
          destruct (H2 (S i) H5) as (rule' & F1 & F2). 
          eauto. 
        * constructor. 
          2: assumption. 
          apply IHa. split; [congruence | intros ]. 
          cbn [length] in H2. assert (0 <= S i < S(|a0|) - 2) by lia. 
          destruct (H2 (S i) H0) as (rule & H3 & H4). 
          eauto. 
  Qed. 
End fixInstance. 

Arguments valid {Sigma}. 
(* Notation "s |= c" := (satFinal c s) (at level 60). *)
(* Notation "a ⇝ b" := (valid a b) (at level 90, left associativity).  *)
(* Notation "a '⇝(' n ')' b" := (relpower valid n a b) (at level 90, left associativity, format "a '⇝(' n ')' b"). *)

Definition TCSRLang (C : TCSR) :=  exists (sf : string (Sigma C)), relpower (valid (windows C)) (steps C) (init C) sf /\ satFinal (final C) sf. 
