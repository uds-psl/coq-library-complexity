From Undecidability.L.Complexity Require Import NP Synthetic Problems.SAT Problems.Clique Problems.kSAT.
From Undecidability.L Require Import Tactics.LTactics.
From Undecidability.L.Complexity Require Import Problems.LGraph.
Require Import Coq.Init.Nat.
Import PslBase.Bijection.

(*we first design the reduction function*)
(* idea: for every clause c, create three nodes n^c_1, n^c_2, n^c_3 , corresponding to the three literals*)
(* connect n^c_i to n^d_j iff c <> d and the literals corresponding to n^c_i and n^d_j are not conflicting*)
(* if there are k clauses, we have a k clique iff the cnf is satisfiable*)

(*Layout of the constructed instance: for every clause with index i the three nodes with indices 3i..3i+2 *)
(*construction of the edge set: iterate over clauses. for each literal of each clause, iterate over all clauses*)
(*this should run in quadratic time*)

(*We proceed in the following way: *)
(*First, we define a relation on cnf * UndirectedGraph that connects sat instances to clique instances *)

(*a labelling function for a graph that assigns a clause and a literal index *)
(*we use finite types as domain because this enables us to talk about the labelling function as a bijection*)
(*(in case of valid reduction instances) between literals and nodes in the graph *)
Definition labGraph (nodes : nat) (numcl : nat) := (Fin.t nodes) -> (Fin.t numcl * Fin.t 3).
Definition labGraphInv (nodes : nat) (numcl : nat) := Fin.t numcl * Fin.t 3 -> Fin.t nodes. 
Definition literal_in_CNF (c : cnf) (l : literal) := exists cl, cl el c /\ l el cl.

Definition literalsConflict (a b : literal) := match a, b with (s1, v1), (s2, v2) => s1 <> s2 /\ v1 = v2 end.

Lemma literalsConflict_eval (s s' : bool) (n n' : nat) (a : assgn) : n' < |a| -> n < |a| -> (literalsConflict (s, n) (s', n') <-> (evalLiteral a (s, n) <> evalLiteral a (s', n') /\ n = n')). 
Proof.
  intros H1 H2. split.
  - intros [F1 F2]. rewrite F2. cbn. apply (nth_error_Some a n') in H1. destruct (nth_error a n'). 2: split; auto.
    split; try reflexivity. enough (Bool.eqb s b <> Bool.eqb s' b) by congruence. destruct s, b, s'; cbn; congruence.
  - intros [F1 ->]. split. 2: reflexivity. cbn in F1. apply (nth_error_Some a n') in H1. destruct (nth_error a n').
    2: auto. destruct s, s', b; cbn in F1; congruence. 
Qed. 


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

Lemma enumerateLiteral_Some_conv (c : cnf) : kCNF k c -> forall n n', (exists (l : literal), enumerateLiteral c (n, n') = Some l) -> n < |c| /\ n' < k. 
Proof.
  intros H n n' (l & H1). induction c. 
  - cbn in H1. destruct n; cbn in H1; congruence.  
  - cbn in H1. destruct n; cbn in H1. apply nth_error_Some_lt in H1. inv H. split; cbn; lia. 
    (* inv H. cbn in IHc. destruct c. destruct n; cbn in H1; congruence. destruct (nth_error c n); try congruence.  *)
Admitted. 

Definition enumLiteral_different_clause (l1 : nat * nat) (l2 : nat * nat) := fst l1 <> snd l2. 
End enumLiteral.

Definition finToNat (n : nat) (k : Fin.t n) := proj1_sig (Fin.to_nat k). 
Definition labGraphNat (nodes : nat) (numcl : nat) (f : labGraph nodes numcl) (m : Fin.t nodes) :=
  let '(a, b) := f m in (finToNat a, finToNat b).

(* the reduction relation *)
Definition redRel (c : cnf) (cl : Lgraph * nat) := let (g, k) := cl in
                                                 let (n, e) := g in n = (3 * |c|) /\  
  exists (labF : labGraph n (|c|)) (labFInv : labGraphInv n (|c|)), inverse labF labFInv /\
     (forall (u v : Fin.t n), Lgraph_edge_in_dec (n, e) (finToNat u) (finToNat v) <->
      (enumLiteral_different_clause (labGraphNat labF u) (labGraphNat labF v) /\
      (forall (l1 l2 : literal), enumerateLiteral c (labGraphNat labF u) = Some l1 ->
                               enumerateLiteral c (labGraphNat labF v) = Some l2 ->
                               not (literalsConflict l1 l2)))).

(*construction of a set of literal indices, one for each clause, that is satisfied for an assignment*)
Section constructClique.
  Fixpoint constructClique_clause' (a : assgn) (cl_index : nat) (cl : clause) (lit_index : nat):=
  match cl with [] => None
              | (l :: cl) => match evalLiteral a l with Some true => Some (cl_index, lit_index)
                                               | _  => constructClique_clause' a cl_index cl (S lit_index)
  end end. 
  Definition constructClique_clause (a : assgn) (cl_index : nat) (cl : clause) :=
  constructClique_clause' a cl_index cl 0.

  Fixpoint constructClique_cnf' (a:assgn) (cn : cnf) (cl_index : nat) :=
  match cn with [] => []
              | (l :: cn) => match constructClique_clause a cl_index l with Some l => l :: constructClique_cnf' a cn (S cl_index)
                                                                          | None => []
                            end
  end. 
  Definition constructClique_cnf (a : assgn) (cn : cnf) := constructClique_cnf' a cn 0.


  Lemma everyClause' (a : assgn) (cn : cnf): evalCnf a cn = Some true -> forall cl, cl el cn -> forall n, exists k, constructClique_clause a n cl = Some (n, k).
  Proof.
    intros H cl H1 n.
    enough (forall m : nat, exists k, constructClique_clause' a n cl m = Some (n, m + k)) by apply H0.
    assert (evalClause a cl = Some true ) by (apply (proj1 (evalCnf_clause_iff a cn) H cl H1)).
    clear H1. induction cl. 
    - cbn in H0; congruence. 
    - intros m. cbn. destruct (evalLiteral a a0) eqn:eq.
      2 : rewrite evalClause_step_inv in H0; destruct H0 as (b1 & b2 & F1 & F2 & F3); congruence. 
      destruct b eqn:eq2. now exists 0. 
      rewrite evalClause_step_inv in H0; destruct H0 as (b1 & b2 & F1 & F2 & F3).
      destruct b2; try congruence. simp_bool'. apply IHcl  with (m := S m) in F1.
      destruct F1 as (k & F1). exists (S k). now rewrite Nat.add_succ_r. 
  Qed. 

  Lemma everyClause (a : assgn) (cn : cnf): evalCnf a cn = Some true -> forall n, n < |cn| -> exists k, (n, k) el constructClique_cnf a cn. 
  Proof.
    intros H.
    enough (forall (m n: nat), n < |cn| -> exists k, (m + n, k) el constructClique_cnf' a cn m) by (apply (H0 0)).
    induction cn; intros m n H1; cbn in H1; try lia. 
    destruct n. 
    - cbn. destruct (everyClause' H (or_introl eq_refl) m). rewrite H0. exists x. now rewrite Nat.add_0_r.  
    - cbn. destruct (everyClause' H (or_introl eq_refl) m).
      apply evalCnf_step_inv in H. destruct H as (b1 & b2 & F1 & F2 & F3). simp_bool'.
      assert (n < (|cn|)) by lia. specialize (IHcn F1 (S m) n H) as (k & H2).
      cbn. rewrite H0. exists k. right; now rewrite Nat.add_succ_r. 
  Qed. 

  Lemma construct_length_bound (a : assgn) (cn : cnf): |constructClique_cnf a cn| <= |cn|. 
  Proof.
    enough (forall (m : nat), |constructClique_cnf' a cn m| <= |cn|) by apply (H 0). 
    induction cn; intros m; cbn; try lia.
    destruct (constructClique_clause a m a0); try cbn; try lia. rewrite IHcn. lia.
  Qed. 

  Lemma construct_length (a : assgn) (cn : cnf) : evalCnf a cn = Some true -> |constructClique_cnf a cn| = |cn|. 
  Proof.
    intros H. enough (|constructClique_cnf a cn| >= |cn|).
    {specialize (construct_length_bound a cn); lia. }
    specialize (everyClause  H) as H1.
  Admitted. 

  Lemma construct_literals_positive (a : assgn) (cn : cnf) : forall (pos : nat * nat), pos el constructClique_cnf a cn
                                                            -> exists (l : literal), enumerateLiteral cn pos = Some l
                                                                 /\ evalLiteral a l = Some true. 
  Proof.
    (*by induction over the structure of the CNF again*)
  Admitted. 

  Lemma construct_literals_no_conflict (a : assgn) (cn : cnf) : forall (pos pos' : nat * nat), pos el constructClique_cnf a cn -> pos' el constructClique_cnf a cn -> pos <> pos'
    -> exists l l', Some l = enumerateLiteral cn pos /\ Some l' = enumerateLiteral cn pos' /\ not(literalsConflict l l').
  Proof.
    intros pos pos' H1 H2 H3. destruct (construct_literals_positive H1) as (l1 & F1 & F2). 
    destruct (construct_literals_positive H2) as (l2 & G1 & G2). exists l1, l2. 
    split; try split; firstorder. intros H. destruct l1, l2. rewrite literalsConflict_eval with (a := a)in H. 
    now rewrite F2, G2 in H.
    - now apply evalLiteral_varBound with (sign:= b0).
    - now apply evalLiteral_varBound with (sign:=b). 
  Qed. 

  Lemma construct_literals_bound (a : assgn) (cn : cnf) (k : nat) : kCNF k cn -> forall (n m : nat), (n, m) el constructClique_cnf a cn -> n < |cn| /\ m < k. 
  Proof.
    intros H n m H1. apply enumerateLiteral_Some_conv. apply H.
    destruct (construct_literals_positive H1) as (l & H2 & _). exists l; apply H2. 
  Qed. 

  Definition liftList (X : Type) (l : list X) : {a : list ({e | e el l}) | map (@proj1_sig X (fun a => a el l)) a = l}. 
  Proof.
    induction l. 
    - exists []. now cbn. 
    - destruct IHl as (l' & H). 
      exists ((exist (fun x => x el a ::l) a (or_introl eq_refl)) :: (map (fun m => match m with exist _  elm p => exist (fun x => x el a ::l) elm (or_intror p) end) l')). 
      cbn. enough (map (proj1_sig (P:=fun a0 : X => a = a0 \/ a0 el l))
       (map
          (fun
             m : {elm : X |
                 (fix In (a0 : X) (l0 : list X) {struct l0} : Prop :=
                    match l0 with
                    | [] => False
                    | b :: m => b = a0 \/ In a0 m
                    end) elm l} => let (elm, p) := m in exist (fun x : X => a = x \/ x el l) elm (or_intror p)) l')  = l) by now rewrite H0. revert l' H. induction l. 
      + intros l' H. destruct l'. cbn. reflexivity. now destruct s.
      + intros l' H. destruct l'. cbn in H; congruence. cbn. destruct s. cbn. cbn in H.
        assert (x = a0) by congruence. rewrite H0. enough (map (proj1_sig (P:=fun a1 : X => a = a1 \/ a0 = a1 \/ a1 el l))
       (map
          (fun
             m : {elm : X |
                 a0 = elm \/
                 (fix In (a1 : X) (l0 : list X) {struct l0} : Prop :=
                    match l0 with
                    | [] => False
                    | b :: m => b = a1 \/ In a1 m
                    end) elm l} =>
           let (elm, p) := m in exist (fun x0 : X => a = x0 \/ a0 = x0 \/ x0 el l) elm (or_intror p)) l') = l) by now rewrite H1.  rewrite <- IHl with (l' := l').
        Admitted. 

  Definition constructClique_fin (a : assgn) (cn : cnf) (k : nat) : kCNF k cn -> list (Fin.t (|cn|) * Fin.t k). 
  Proof. 
    intros H. remember (constructClique_cnf a cn) as l. 
    specialize (construct_literals_bound (a := a) H) as H'. rewrite <- Heql in H'.
    induction l. exact []. 


End constructClique.

Lemma redRel_reduces (c : cnf) (cl : Lgraph * nat) : redRel c cl -> (SAT c <-> LClique cl ).
Proof. 
  split. 
  + intros (a & H1). destruct cl as (g & k). destruct g. cbn in H.
    destruct H as (neq & labF & labFInv & labinv & H2).
    (*now need to lift the constructClique output to Fin.t and prove, using H2, that it is indeed a clique *)
    (* exists (constructClique_cnf a c).  *)
    admit.
  + destruct cl as (g, k). destruct g as (n, e). intros (clique & H1).
Admitted. 

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



(* Lemma makeEdges_correct (c : cnf) : kCNF 3 c -> forall (l l' : literal) (n n' : nat), (n < 3 * (|c|) /\ n' < 3 * (|c|) /\ enumerateLiteral c 3 n = Some l /\ enumerateLiteral c 3 n' = Some l') *)
(*                                                -> (not (literalsConflict l l') /\ enumLiteral_different_clause c 3 n n'  <-> *)
(*                                                   Lgraph_edge_in_dec' (makeEdges c 0) n n').  *)
(* Abort.  *)

Lemma tsat_to_clique  : reducesPolyMO (kSAT 3) LClique. 
Proof. 
  
Admitted. 

