From PslBase Require Import Base. 
From PslBase Require Import Vectors.Vectors. 
From PslBase Require Import FiniteTypes. 
Require Import Lia.
From Undecidability Require Import L.Complexity.Cook.Prelim.

Record CSRWin (Sigma : finType) (w : nat) := {
                                            prem : Vector.t Sigma w;
                                            conc : Vector.t Sigma w
                                          }.

Record CSR := {
               Sigma : finType;
               offset : nat; 
               width : nat;  
               init : list Sigma;  (* length is encoded implicitly as the length of init*) (*length should be a multiple of offset *)
               windows : list (CSRWin Sigma width);
               final : list (list Sigma);
               steps : nat
             }.

Definition CSR_wellformed (c : CSR) := exists k, length (init c) = k * offset c.

Implicit Type (C : CSR).

Section fixInstance.
  Variable (c : CSR). 
  Context (F0 : width c > 0).

  Definition string := list (Sigma c). 
  Definition window := CSRWin (Sigma c) (width c). 

  Implicit Type (s a b: string). 
  Implicit Type (r rule : window).
  Implicit Type (x y : Sigma c).

  Coercion Vector.to_list : Vector.t >-> list.

  Definition isRule r := r el windows c.
  Lemma isRule_length r : length (prem r) = width c /\ length (prem r) = width c.
  Proof. 
    intros. destruct r. 
    split; now rewrite vector_to_list_length. 
  Qed. 

  (* the final constraint*)
  Definition satFinal s := exists subs, subs el final c /\ substring subs s.


  (* rewrites inside a string *)
  Definition rewritesHead rule a b :=
    prefix (prem rule) a /\ prefix (prem rule) b.

  Lemma rewritesHead_length_inv rule a b : rewritesHead rule a b -> isRule rule -> length a >= width c /\ length b >= width c. 
  Proof. 
    intros. unfold rewritesHead, prefix in *. firstorder.
    - rewrite H. rewrite app_length, (proj1 (isRule_length rule)). lia.  
    - rewrite H1. rewrite app_length, (proj1 (isRule_length rule)). lia. 
  Qed. 

  Definition rewritesAt rule (i : nat) a b := rewritesHead rule (skipn i a) (skipn i b).
  Lemma rewritesAt_head rule a b : rewritesHead rule a b <-> rewritesAt rule 0 a b. 
  Proof. 
    unfold rewritesAt.
    rewrite <- firstn_skipn with (n:= 0) (l:= a) at 1.
    rewrite <- firstn_skipn with (n:= 0) (l:= b) at 1.
    repeat rewrite firstn_O; now cbn. 
  Qed. 

  Lemma rewritesAt_step rule a b u v (i:nat) : length u = offset c -> length v = offset c -> rewritesAt rule i a b <-> rewritesAt rule (i + offset c) (u ++ a) (v ++ b). 
  Proof.
    intros. unfold rewritesAt.
    rewrite Nat.add_comm. now repeat rewrite skipn_add. 
  Qed. 

  (*validity of a rewrite *)
  Inductive valid : string -> string -> Prop :=
  | validB: valid [] [] 
  | validSA a b u v : valid a b -> length a < (width c) - offset c -> length u = offset c -> length v = offset c -> valid (u++ a) (v++ b)
  | validS a b u v rule: valid a b -> length u = offset c -> length v = offset c -> rule el (windows c) -> rewritesHead rule (u ++ a) (v ++ b) -> valid (u ++ a) (v ++ b). 

  Lemma valid_length_inv a b : valid a b -> length a = length b. 
  Proof.
    induction 1. 
    - now cbn.
    - repeat rewrite app_length. firstorder. 
    - repeat rewrite app_length; firstorder. 
  Qed. 

  Definition validExplicit a b := length a = length b /\ (exists k, length a = k * offset c) /\ forall i, 0 <= i < length a + 1 - width c /\ (exists j, i = j * offset c) -> exists rule, rule el windows c  /\ rewritesAt rule i a b.



  Lemma valid_iff a b :
    valid a b <-> validExplicit a b.
  Proof.
    unfold validExplicit. split.
    - induction 1.
      + split; [now cbn |split; [now exists 0 | ] ]. intros. cbn [length] in H. lia.  
      + specialize (valid_length_inv H) as H'. split; [ repeat rewrite app_length; now rewrite H', H1, H2 | ].
        destruct IHvalid as (IH1 & IH2 & IH3). 
        split.
        1: { destruct IH2 as (k & IH2). exists (S k). rewrite app_length; lia. }
        rewrite app_length; intros. lia. 
      + destruct IHvalid as (IH1 & IH2 & IH3). split; [repeat rewrite app_length; firstorder | ].  
        split.
        1: { destruct IH2 as (k & IH2). exists (S k). rewrite app_length; lia. }
        rewrite app_length. intros i (iH1 & (j & iH2)). destruct j. 
        * exists rule. split; [assumption | ]. rewrite Nat.mul_0_l in iH2. rewrite iH2 in *. now rewrite <- rewritesAt_head.  
        * cbn in iH2. assert (0 <= i - offset c < (|a|) + 1 - width c) by lia.
          assert (exists j, i - offset c = j * offset c) by (exists j; lia). 
          specialize (IH3 (i -offset c) (conj H4 H5)) as (rule' & F1 & F2). 
          exists rule'; split; [assumption | ]. rewrite (@rewritesAt_step rule' a b u v (i -offset c) H0 H1) in F2. rewrite Nat.sub_add in F2; [assumption | lia]. 
    - intros (H1 & (k & H2) & H3). revert a b H1 H2 H3. induction k; intros. 
      + rewrite Nat.mul_0_l in H2; rewrite H2 in *. inv_list. constructor.
      + cbn in H2. rewrite H2 in H1; symmetry in H1.
        apply length_app_decompose in H2 as (u & a' & -> & H2 & H4).
        apply length_app_decompose in H1 as (v & b' & -> & H1 & H5). 
        destruct (le_lt_dec (width c - offset c) (length a')). 
        * (*have to find a rule to apply*)
          rewrite app_length in H3. 
          assert (0 <= 0 < (|u|) + (|a'|) + 1 - width c) by lia. 
          assert (exists j, 0 = j * offset c) as H' by (exists 0; lia). 
          destruct (H3 0 (conj H H')) as (rule & F1 & F2%rewritesAt_head). 
          eapply (@validS a' b' u v rule). 2-5: assumption. 
          apply IHk; [lia | apply H4 | ]. 
          intros i (H0 & (j & H6)). assert (0 <= i + (|u|) < (|u|) + (|a'|) + 1 - width c) by lia. 
          assert (exists j, i + (|u|) = j * offset c) by (exists (S j); lia). 
          destruct (H3 (i + (|u|)) (conj H7 H8)) as (rule' & F3 & F4). 
          exists rule'; split; [assumption | ]. 
          rewrite H2 in F4. now apply (proj2 (@rewritesAt_step rule' a' b' u v (i ) H2 H1)) in F4. 
        * (* the rewrite is vacuously valid *)
          constructor.
          2-4: assumption. 
          apply IHk; [congruence | assumption | ]. 
          intros i (F1 & (j & F2)). rewrite app_length in H3. 
          assert (0 <= i + (|u|) < (|u|) + (|a'|) + 1 - width c) by lia.
          assert (exists j, i + (|u|) = j * offset c) by (exists (S j); lia). 
          destruct (H3 (i + (|u|)) (conj H H0)) as (rule & H6 & H7). 
          exists rule; split; [assumption | ]. 
          rewrite H2 in H7. now apply (proj2 (@rewritesAt_step rule a' b' u v i H2 H1)) in H7. 
  Qed. 

End fixInstance. 

Arguments valid {c}. 
(* Notation "s |= c" := (satFinal c s) (at level 60).  *)
(* Notation "a ⇝ b" := (valid a b) (at level 90, left associativity).  *)
(* Notation "a '⇝(' n ')' b" := (relpower valid n a b) (at level 90, left associativity, format "a '⇝(' n ')' b"). *)

Definition CSRLang (C : CSR) := CSR_wellformed C /\ exists (sf : string C), relpower valid (steps C) (init C) sf /\ satFinal sf. 
