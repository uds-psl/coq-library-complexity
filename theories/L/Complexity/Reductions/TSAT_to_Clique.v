From Undecidability.L.Complexity Require Import NP Synthetic Problems.SAT Problems.Clique Problems.kSAT.
From Undecidability.L Require Import Tactics.LTactics.
From Undecidability.L.Complexity Require Import Problems.LGraph.
Require Import Coq.Init.Nat.

(*we first design the reduction function*)
(* idea: for every clause c, create three nodes n^c_1, n^c_2, n^c_3 , corresponding to the three literals*)
(* connect n^c_i to n^d_j iff c <> d and the literals corresponding to n^c_i and n^d_j are not conflicting*)
(* if there are k clauses, we have a k clique iff the cnf is satisfiable*)

(*Layout of the constructed instance: for every clause with index i the three nodes with indices 3i..3i+2 *)
(*construction of the edge set: iterate over clauses. for each literal of each clause, iterate over all clauses*)
(*this should run in quadratic time*)

(*the instance has 3 * num_clauses nodes and at most 9 * num_clauses^2 edges *)
(*care needs to be taken to show that this is indeed the case *)

Definition tripToList (X : Type) (a : X * X * X) := [fst(fst a); snd(fst a); snd a]. 

Definition literalsConflict (a b : literal) := match a, b with (s1, v1), (s2, v2) => s1 <> s2 /\ v1 = v2 end.
Definition literalsConflictb (a b : literal) := match a, b with (s1, v1), (s2, v2) => negb(Bool.eqb s1 s2) && Nat.eqb v1 v2 end. 

Definition enumerateLiteral' (c : clause) (n : nat) := nth_error c n.
Definition enumerateLiteral (c : cnf) (k : nat) (n : nat) := match nth_error c (n / k) with Some cl => enumerateLiteral' cl (n mod k) 
                                                                           | None => None
                                                                            end.

Lemma enumerateLiteral_clstep (c : cnf) (cl :clause) (k : nat) (n : nat) : kCNF k (cl ::c) -> enumerateLiteral (cl::c) k (n + k) = enumerateLiteral c k n. 
Proof. 
  intros H.
  unfold enumerateLiteral. cbn.
  replace k with (1*k) at 1 by lia. rewrite Nat.div_add. cbn. replace (n/k + 1) with (S (n/k)) by lia. 
  replace (n+k) with (n + 1 * k) by lia. rewrite Nat.mod_add.
  reflexivity. all: apply kCNF_kge in H; lia. 
Qed.

Lemma enumerateLiteral'_Some (c : clause) (k : nat) : |c| = k -> forall n, n < k -> exists (l : literal), enumerateLiteral' c n = Some l.
Proof. 
  intros H n H1. 
  unfold enumerateLiteral'. rewrite <- H in H1. destruct (Prelim.nthe_length H1). now exists x.
Qed.                                                                                      

Lemma enumerateLiteral_Some (c : cnf) (k : nat) :   kCNF k c -> forall n, n < |c| * k -> exists (l : literal), enumerateLiteral c k n = Some l.
Proof.
  intros H n H1. specialize (kCNF_kge H) as H0. destruct (enumerateLiteral c k n) eqn:H2. now exists p. 
  exfalso. revert n H1 H2. induction c. 
  + intros n H1 H2. cbn in H1; lia. 
  + intros n H1 H2. cbn in H1. inv H.
    destruct (le_lt_dec (|a|) n).
    - apply (IHc H6 (n - |a|)). lia. replace n with ((n - |a|) + |a|) in H2.  
      rewrite (enumerateLiteral_clstep (c:= c) (cl:= a)) in H2. apply H2.
      now constructor. lia. 
    - clear IHc. unfold enumerateLiteral in H2. replace (n/(|a|)) with 0 in H2. cbn in H2.
      assert (n mod (|a|) < |a|). { rewrite Nat.mod_small; auto. }
      destruct (enumerateLiteral'_Some (c := a) (n := n mod (|a|)) eq_refl H) as (l' & H'). 
      congruence.
      now rewrite Nat.div_small. 
Qed.

Definition enumLiteral_different_clause (c : cnf) (k : nat) (u : nat) (v : nat) := (u / k) <> (v /k).

(* I am dumb. This obviously can't be extracted...*)
(* Definition redGraph (c :cnf) : UndirectedGraph. *)
(*   destruct (kCNF_decb 3 c) eqn:H1.  *)
(*   - exists ( 3 * (|c|)) *)
(*     (fun (u : Fin.t (3 * |c|)) (v : Fin.t (3 * |c|)) => match enumerateLiteral c 3 (finToNat u) with Some l1 => *)
(*                                               match enumerateLiteral c 3 (finToNat v) with Some l2 => *)
(*                                                  not (literalsConflict l1 l2) /\ *)
(*                                                 enumLiteral_different_clause c 3 (finToNat u) (finToNat v) *)
(*                                                | None => False end | None => False end). *)
(*     + intros u v. *)
(*       pose (u' := finToNat u). pose (v' := finToNat v). *)
(*       destruct (enumerateLiteral c 3 (finToNat u)), (enumerateLiteral c 3 (finToNat v)). *)
(*       destruct p, p0. cbn. destruct (Bool.eqb b b0) eqn:H2, (Nat.eqb n n0) eqn:H3.  *)
(*       1,2,4: destruct (Nat.eqb (u' / 3) (v'/3)) eqn:H4.   *)
(*       all: try (right; intros [_ H]; now eqdec_bool); try (left; split; eqdec_bool; tauto).  *)
(*       1 : right; intros [H H']; apply H; eqdec_bool.   *)
(*       1-3: now right. *)
(*     + (*symmetry*) *)
(*       intros u v. pose (u' := finToNat u). pose(v' := finToNat v).  *)
(*       destruct (enumerateLiteral c 3 (finToNat u)), (enumerateLiteral c 3 (finToNat v)). *)
(*       2-4: tauto.  *)
(*       destruct p, p0. cbn. unfold enumLiteral_different_clause. intros [H2 H3]. split; firstorder.  *)
(*   - (*invalid instance*) *)
(*     exists 0 (fun u v => False); tauto. (*empty graph, the reduction then  *) *)
(* Defined.  *)

(* Definition redGraph' (c : cnf)   *)
(* Definition redLraph (c : cnf)  *)

Lemma tsat_to_clique  : reducesPolyMO (kSAT 3) LClique. 
Proof. 
  
Admitted. 

