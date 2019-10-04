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

(*We proceed in the following way: *)
(*First, we define a relation on cnf * UndirectedGraph that connects sat instances to clique instances *)

(*a labelling function for a graph with 3*num nodes that assigns a clause and a literal index *)
Definition labGraph (g : UndirectedGraph) (num : nat) := Fin.t g -> {'(n, k)| n < num /\ k < 3}.
Definition literal_in_CNF (c : cnf) (l : literal) := exists cl, cl el c /\ l el cl.

Definition flatLab (g : UndirectedGraph) (n : nat) (f : labGraph g n) (h : Fin.t g) := proj1_sig (f h). 

Definition literalsConflict (a b : literal) := match a, b with (s1, v1), (s2, v2) => s1 <> s2 /\ v1 = v2 end.
Definition literalsConflictb (a b : literal) := match a, b with (s1, v1), (s2, v2) => negb(Bool.eqb s1 s2) && Nat.eqb v1 v2 end. 

Section enumLiteral.
  Variable (k :nat).

  Definition enumerateLiteral' (c : clause) (n : nat) := nth_error c n.
  Definition enumerateLiteral (c : cnf) (pos : nat * nat) := let (cl, n) := pos in  match nth_error c cl with Some cl => enumerateLiteral' cl n 
                                                                           | None => None
                                                                            end.

Lemma enumerateLiteral'_Some (c : clause) : |c| = k -> forall (n : nat), n < k -> exists (l : literal), enumerateLiteral' c n = Some l.
Proof. 
  intros H n H1.  
  unfold enumerateLiteral'. rewrite <- H in H1. destruct (Prelim.nthe_length H1). now exists x.
Qed.                                                                                      

Lemma enumerateLiteral_Some (c : cnf) : kCNF k c -> forall (n :nat) (n' : nat), n < |c| -> n' < k -> 
      exists (l : literal), enumerateLiteral c (n, n') = Some l.
Proof.
  intros H n n' H1 H2. specialize (kCNF_kge H) as H0. destruct (enumerateLiteral c (n, n')) eqn:H3. now exists p. 
  exfalso. revert n H1 H3. induction c. 
  + intros n H1. cbn in H1; lia.  
  + intros n H1 H3. cbn in H1.
    destruct n. cbn in H3. inversion H.  specialize (enumerateLiteral'_Some H6 H2) as (l & H8). congruence. 
    unfold enumerateLiteral in H3. cbn in H3. apply IHc with (n := n). now inv H. lia. apply H3.
Qed. 

Definition enumLiteral_different_clause (l1 : nat * nat) (l2 : nat * nat) := fst l1 <> snd l2. 
End enumLiteral.

Definition redRel (c : cnf) (cl : UndirectedGraph * nat) := let (g, k) := cl in V g = (3 * |c|) /\  
  exists (labF : labGraph g (|c|)), injective (flatLab labF) /\ (forall (u v : Fin.t (V g)), @E g u v <->
      (enumLiteral_different_clause (flatLab labF u) (flatLab labF v) /\
       not (exists (l1 l2 : literal), enumerateLiteral c (flatLab labF u) = Some l1 /\ enumerateLiteral c (flatLab labF v) = Some l2 /\ literalsConflict l1 l2))).


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

(*contruction principle: enumerate the literals from left to right; for each literal go through the literals *)
(*of the clauses to the right of it and make appropriate edges *)
(* this suffices since we are dealing with an undirected graph*)
Fixpoint makeEdgesLiteral' (l : literal) (numL : nat) (cl :clause) (numAcc : nat) :=
  match cl with [] => []
              | (l' :: cl) => if literalsConflictb l l' then makeEdgesLiteral' l numL cl (S numAcc) else (numL, numAcc) :: makeEdgesLiteral' l numL cl (S numAcc)
  end.
Fixpoint makeEdgesLiteral (l : literal) (numL : nat) (cn : cnf) (numAcc : nat) := match cn with [] => []
  | (cl::cn) => makeEdgesLiteral' l numL cl numAcc ++ makeEdgesLiteral l numL cn (3 + numAcc) end.
Fixpoint makeEdges' (c : clause) (numL : nat) (cn : cnf) := match c with [] => []
                                                           | (l :: c) => makeEdgesLiteral l numL cn 0
                                                           end. 
Fixpoint makeEdges (c : cnf) (numL : nat) := match c with [] => []
             | (cl::c) => makeEdges' cl numL c ++ makeEdges c (3 + numL) end.
Definition redGraph (c : cnf) : Lgraph := if kCNF_decb 3 c then (3 * |c|, makeEdges c 0)
                                                            else (0, []). 



Lemma makeEdges_correct (c : cnf) : kCNF 3 c -> forall (l l' : literal) (n n' : nat), (n < 3 * (|c|) /\ n' < 3 * (|c|) /\ enumerateLiteral c 3 n = Some l /\ enumerateLiteral c 3 n' = Some l')
                                               -> (not (literalsConflict l l') /\ enumLiteral_different_clause c 3 n n'  <->
                                                  Lgraph_edge_in_dec' (makeEdges c 0) n n'). 
Abort. 

Lemma tsat_to_clique  : reducesPolyMO (kSAT 3) LClique. 
Proof. 
  
Admitted. 

