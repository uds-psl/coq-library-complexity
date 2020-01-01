From PslBase Require Import Base. 
From PslBase Require Import Vectors.Vectors. 
From PslBase Require Import FiniteTypes. 
From Undecidability Require Import L.Complexity.Cook.Prelim.
Require Import Lia.


(*use an explicit representation instead of vectors of size 3 since this will make the problem closer to the flattened extractable problem *)
Record TCSRWinP (Sigma : Type) := {
                                   winEl1 : Sigma;
                                   winEl2 : Sigma;
                                   winEl3 : Sigma
                                 }.

Record TCSRWin (Sigma : Type) := {
                                            prem : TCSRWinP Sigma;
                                            conc : TCSRWinP Sigma
                                   }.

Definition TCSRWinP_to_list (sig : Type) (a : TCSRWinP sig) := match a with Build_TCSRWinP a b c => [a; b; c] end. 
Coercion TCSRWinP_to_list : TCSRWinP >-> list. 

Notation "'{' a ',' b ',' c '}'" := (Build_TCSRWinP a b c) (format "'{' a ',' b ',' c '}'").
Notation "a / b" := ({|prem := a; conc := b|}). 

(* Instance TCSRWinP_eqTypeC (Sigma : finType) : eq_dec (TCSRWinP Sigma).  *)
(* Proof. *)
(*   unfold dec. destruct Sigma. destruct type. decide equality.  *)
(*   destruct (eqType_dec e1 e4); auto.  *)
(*   destruct (eqType_dec e0 e3); auto.  *)
(*   destruct (eqType_dec e e2); auto.  *)
(* Defined.  *)

(* Instance TCSRWin_eqTypeC (Sigma : finType) : eq_dec (TCSRWin Sigma).  *)
(* Proof.  *)
(*   unfold dec. decide equality. *)
(*   destruct (TCSRWinP_eqTypeC conc0 conc1); auto.  *)
(*   destruct (TCSRWinP_eqTypeC prem0 prem1); auto.  *)
(* Defined.  *)

Record TCSR := {
               Sigma : finType;
               init : list Sigma;  (* length is encoded implicitly as the length of init*) 
               windows : list (TCSRWin Sigma);
               final : list (list Sigma);
               steps : nat
             }.


Implicit Type (C : TCSR).

Section fixInstance.
  Variable (Sigma : Type).
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
  (*We define the following notions over an abstract rewritesHead predicate. A concrete instance can be obtained using rewritesHead_pred *)
  Definition rewritesHeadAbstract := string -> string -> Prop. 
  Definition rewritesAt (p : rewritesHeadAbstract) (i : nat) a b := p (skipn i a) (skipn i b).
  Lemma rewritesAt_head p a b : p a b <-> rewritesAt p 0 a b. 
  Proof. 
    unfold rewritesAt.
    rewrite <- firstn_skipn with (n:= 0) (l:= a) at 1.
    rewrite <- firstn_skipn with (n:= 0) (l:= b) at 1.
    repeat rewrite firstn_O; now cbn. 
  Qed. 

  Lemma rewritesAt_step p a b x y (i:nat) : rewritesAt p i a b <-> rewritesAt p (S i) (x :: a) (y:: b). 
  Proof. intros. unfold rewritesAt. now cbn. Qed. 


  (*validity of a rewrite *)
  Inductive valid (p : rewritesHeadAbstract): string -> string -> Prop :=
  | validB: valid p [] [] 
  | validSA a b x y: valid p a b -> length a < 2 -> valid p (x:: a) (y:: b)
  | validS a b x y : valid p a b -> p (x::a) (y::b) -> valid p (x::a) (y::b). 

  Hint Constructors valid. 

  Lemma valid_length_inv p a b : valid p a b -> length a = length b. 
  Proof.
    induction 1. 
    - now cbn.
    - cbn; congruence.
    - cbn; congruence. 
  Qed. 

  (*valid is congruent for equivalent rewriteHead predicates *)
  Lemma valid_congruent' (p1 p2 : rewritesHeadAbstract) : (forall u v, p1 u v -> p2 u v) -> forall a b, valid p1 a b -> valid p2 a b. 
  Proof. 
    intros.
    induction H0. 
    - constructor. 
    - now constructor. 
    - constructor 3. apply IHvalid. 
      now apply H. 
  Qed.

  Corollary valid_congruent p1 p2 : (forall u v, p1 u v <-> p2 u v) -> forall a b, valid p1 a b <-> valid p2 a b.
  Proof.
    intros; split; [apply valid_congruent'; intros; now apply H | ].
    assert (forall u v, p2 u v <-> p1 u v) by (intros; now rewrite H).
    apply valid_congruent'. intros; now apply H. 
  Qed.

  Lemma valid_base (p : rewritesHeadAbstract) (a b c d e f : Sigma) : valid p [a; b ; c] [d; e; f] <-> p [a; b; c] [d; e; f]. 
  Proof. 
    split.
    - intros; inv H. cbn in H5; lia. apply H5.  
    - constructor 3. 2: apply H. repeat constructor.
  Qed. 

  (*the explicit characterisation using bounded quantification *)
  Definition validExplicit p a b := length a = length b /\ forall i, 0 <= i < length a - 2  -> rewritesAt p i a b.

  Lemma valid_iff p a b :
    valid p a b <-> validExplicit p a b.
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
        * assert (0 <= i < (|a|) - 2) by lia. eauto. 
    - revert b. induction a; intros b (H1 & H2). 
      + inv_list. constructor. 
      + inv_list. destruct (le_lt_dec 2 (length a0)). 
        * cbn [length] in H2.
          assert (0 <= 0 < S (|a0|) - 2) by lia. specialize (H2 0 H) as H3. 
          eapply (@validS p a0 b a s). 2-3: assumption. 
          apply IHa. split; [congruence | ]. 
          intros. assert (0 <= S i < S (|a0|) - 2) by lia. 
          specialize (H2 (S i) H4). eauto. 
        * constructor. 
          2: assumption. 
          apply IHa. split; [congruence | intros ]. 
          cbn [length] in H2. assert (0 <= S i < S(|a0|) - 2) by lia. 
          specialize (H2 (S i) H0); eauto. 
  Qed. 

  (*we now define a concrete rewrite predicate based on a set of rules *)
  Definition rewritesHead rule a b :=
    prefix (prem rule) a /\ prefix (conc rule) b.

  Lemma rewritesHead_length_inv rule a b : rewritesHead rule a b -> isRule rule -> length a >= 3 /\ length b >= 3. 
  Proof. 
    intros. unfold rewritesHead, prefix in *. firstorder.
    - rewrite H. rewrite app_length, (proj1 (isRule_length rule)). lia.  
    - rewrite H1. rewrite app_length, (proj2 (isRule_length rule)). lia. 
  Qed. 

  Definition rewritesHead_pred ruleset a b := exists rule, rule el ruleset /\ rewritesHead rule a b. 

  Lemma rewritesHead_pred_subset ruleset1 ruleset2 a b :
    ruleset1 <<= ruleset2 -> rewritesHead_pred ruleset1 a b -> rewritesHead_pred ruleset2 a b.
  Proof. intros H (r & H1 & H2). exists r. split; [ apply H, H1 | apply H2]. Qed. 


  Lemma rewritesHead_rule_inv r a b (σ1 σ2 σ3 σ4 σ5 σ6 : Sigma) : rewritesHead r (σ1 :: σ2 :: σ3 :: a) (σ4 :: σ5 :: σ6 :: b) -> r = {σ1, σ2 , σ3} / {σ4 , σ5, σ6}. 
  Proof. 
    unfold rewritesHead. unfold prefix. intros [(b' & H1) (b'' & H2)]. destruct r. destruct prem0, conc0. cbn in H1, H2. congruence. 
  Qed. 

  Lemma rewritesAt_Head_pred_add_at_end i ruleset (a b c d : string) : rewritesAt (rewritesHead_pred ruleset) i a b -> rewritesAt (rewritesHead_pred ruleset) i (a ++ c) (b ++ d). 
  Proof. 
    intros. unfold rewritesAt, rewritesHead_pred in *.
    destruct H as (rule & H0 & H). exists rule; split; [assumption | ]. 
    unfold Prelim.prefix in *. destruct H as ((b1 & H1) & (b2 & H2)). 
    split.
    - exists (b1 ++ c). rewrite app_assoc. apply skipn_app2 with (c := prem rule ++ b1); [ | assumption]. 
      destruct rule, prem. now cbn.  
    - exists (b2 ++ d). rewrite app_assoc. apply skipn_app2 with (c := conc rule ++ b2); [ | assumption]. 
      destruct rule, conc. now cbn. 
   Qed. 
End fixInstance. 


Ltac inv_valid := match goal with
                    | [ H : valid _ _ _ |- _] => inv H
                  end;
                  try match goal with
                  | [ H : | _ | < 2 |- _] => now cbn in H
                  end.

Arguments valid {Sigma}. 
(* Notation "s |= c" := (satFinal c s) (at level 60). *)
(* Notation "a ⇝ b" := (valid a b) (at level 90, left associativity).  *)
(* Notation "a '⇝(' n ')' b" := (relpower valid n a b) (at level 90, left associativity, format "a '⇝(' n ')' b"). *)

(*we define it using the rewritesHead_pred rewrite predicate *)
Definition TCSRLang (C : TCSR) :=  exists (sf : string (Sigma C)), relpower (valid (rewritesHead_pred(windows C))) (steps C) (init C) sf /\ satFinal (final C) sf. 
