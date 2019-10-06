From Undecidability.L.Complexity Require Import NP Synthetic Problems.SAT Problems.Clique Problems.kSAT MorePrelim.
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
Definition labGraph:= nat -> nat * nat.
Definition labGraphInv := nat * nat -> nat. 
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

Definition enumLiteral_different_clause (l1 : nat * nat) (l2 : nat * nat) := fst l1 <> fst l2. 
End enumLiteral.

Definition isLabelling (c : cnf) (f : labGraph) (fInv : labGraphInv) := inverse f fInv /\ (forall n, n < 3 * (|c|) -> fst(f n) < (|c|) /\ snd (f n) < 3). 


(*a few technical lemmas that are needed in order to work with the labelling function *)
Lemma dupfree_map_bijection (X Y : Type) (l : list X) (f : X -> Y) (g : Y -> X) : inverse f g -> dupfree l <-> dupfree (map f l). 
Proof.
Admitted.

Lemma map_el (X Y : Type) (l : list X) (f : X -> Y) (e : Y) : e el (map f l) -> exists e', e' el l /\ f e' = e. 
Proof.
  induction l. 
  - cbn. intros []. 
  - intros [H1 | H2].
    + exists a. split; firstorder. 
    + destruct (IHl H2) as (e' & F1 & F2). exists e'. split; firstorder. 
Qed. 

Lemma inverse_symmetric (X Y : Type) (f : X -> Y) (g : Y -> X) : inverse f g -> inverse g f.
Proof. intros [H1 H2]. split; tauto. Qed.

Lemma isLabelling_range_inv (c : cnf) (f : labGraph) (fInv : labGraphInv) : isLabelling c f fInv -> forall (n m : nat), n < (|c|) /\ m < 3 -> fInv (n, m) < 3 * (|c|).
Proof.
  intros [H1 H2]. intros n m [F1 F2]. unfold inverse in H1.
  (*would need cardinality arguments at this point *)
Admitted. 

(* the reduction relation *)
Definition redRel (c : cnf) (cl : Lgraph * nat) := let (g, k) := cl in
                                                 let (n, e) := g in n = (3 * |c|) /\ k = |c| /\ kCNF 3 c /\ 
  exists (labF : labGraph) (labFInv : labGraphInv), isLabelling c labF labFInv /\
     (forall (u v : nat), u < n /\ v < n -> (Lgraph_edge_in_dec (n, e) u v = true <->
      (enumLiteral_different_clause (labF u) (labF v) /\
      (forall (l1 l2 : literal), enumerateLiteral c (labF u) = Some l1 ->
                               enumerateLiteral c (labF v) = Some l2 ->
                               not (literalsConflict l1 l2))))).

(*construction of a set of literal indices, one for each clause, that is satisfied for an assignment*)
(*from this, we directly get a clique in a suitable reduction graph*)
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

  Lemma construct_literals_different_clause (a : assgn) (cn : cnf) : forall (pos pos' : nat * nat), pos el constructClique_cnf a cn -> pos' el constructClique_cnf a cn -> pos <> pos' -> enumLiteral_different_clause pos pos'. 
  Proof. 
  Admitted. 

  Lemma construct_literals_bound (a : assgn) (cn : cnf) (k : nat) : kCNF k cn -> forall (n m : nat), (n, m) el constructClique_cnf a cn -> n < |cn| /\ m < k. 
  Proof.
    intros H n m H1. apply enumerateLiteral_Some_conv. apply H.
    destruct (construct_literals_positive H1) as (l & H2 & _). exists l; apply H2. 
  Qed. 

  Lemma construct_dupfree ( a : assgn) (cn : cnf) : dupfree(constructClique_cnf a cn). 
  Proof.
  Admitted. 
End constructClique.

(*now the converse: from a clique, we can construct a satisfying assignment for the corresponding CNF*)
(*since the reduction relation redRel is inherently asymmetric, the structure of this proof is different from the proof above *)
(*we need argue directly over the target CNF and use the facts given by redRel *)

  (*we proceed in the following way *)
  (*1) graph g, cnf c, and clique cl; g, c satisfy redRel and the clique cl is a |c|-clique of that graph *) 
  (*2) list of (clause, literal)-positions - non-conflicting and exactly one for every clause, i.e. also bounded *)
  (*3) list of literals, mapped by enumLiteral from the positions - non-conflicting, if all are satisfied, then the cnf evals to true *)
  (* the list in 3) can be interpreted as a list of fixed assignments list (nat * bool) -*)
  (* - if all other variables are set arbitrarily, then the cnf evals to true*)
  (*4) expand to complete assignment using cnf_maxVar - under this assignment, c evaluates to true *)

Section constructAssgnToPos.
  (*1 -> 2*)
  Variable (c : cnf) (g : Lgraph).
  Variable (f : labGraph) (fInv: labGraphInv). 

  Context (nc : fst g = 3 * |c|).
  Context (kc : kCNF 3 c). 
  Context (islab : isLabelling c f fInv). 
  Context (red : forall (u v : nat), u < fst g /\ v < fst g -> (Lgraph_edge_in_dec g u v = true <->
      (enumLiteral_different_clause (f u) (f v) /\
      (forall (l1 l2 : literal), enumerateLiteral c (f u) = Some l1 ->
                               enumerateLiteral c (f v) = Some l2 ->
                               not (literalsConflict l1 l2))))). 

  Definition toPos (cl : list Lnode) := map f cl. 

  Lemma toPos_bounded (cl : list Lnode) : isLClique g cl (|c|) -> forall a b, (a, b) el toPos cl -> a < (|c|) /\ b < 3. 
  Proof. 
    intros H a b Hel. unfold toPos in Hel; apply map_el in Hel. destruct Hel as (node & Hel1 & Hel2). specialize (isLClique_node_in H Hel1) as Hel3.  
    unfold Lgraph_node_in_dec in Hel3. destruct g. dec_bool. destruct islab. cbn [fst] in nc; rewrite <- nc in H1. specialize (H1 node). 
    rewrite Hel2 in H1. apply H1. lia. 
  Qed. 

  Lemma toPos_exists_literal (cl : list Lnode) : isLClique g cl (|c|) -> forall pos, pos el toPos cl -> exists l, enumerateLiteral c pos = Some l.
  Proof.
    intros H (a & b) Hel. apply enumerateLiteral_Some with (k:= 3).  apply kc. 
    all: now specialize (toPos_bounded H Hel). 
  Qed. 

  Lemma toPos_no_conflict (cl : list Lnode) : isLClique g cl (|c|) -> forall pos1 pos2, pos1 el toPos cl -> pos2 el toPos cl -> pos1 <> pos2 ->
                                              enumLiteral_different_clause pos1 pos2 /\ exists l1 l2, enumerateLiteral c pos1 = Some l1 /\ enumerateLiteral c pos2 = Some l2 /\ not(literalsConflict l1 l2). 
  Proof. 
    intros H (cl1 & lit1) (cl2 & lit2) H1 H2 H3.
    unfold toPos in H1, H2. destruct (map_el H1) as (node1 & D1 & D2). destruct (map_el H2) as (node2 & G1 & G2). 
    destruct (toPos_exists_literal H H1) as (l1 & F1). destruct (toPos_exists_literal H H2) as (l2 & F2). 
    assert (node1 < fst g /\ node2 < fst g). 
    { specialize (isLClique_node_in H D1) as E1. specialize (isLClique_node_in H G1) as E2. unfold Lgraph_node_in_dec in E1, E2. destruct g.  dec_bool. }
    specialize (red H0); clear H0.
    destruct (proj1(isLClique_explicit_correct g cl (|c|)) H) as (_ & _ & _ & edge_in).
    assert (node1 <> node2). { contradict H3. rewrite <-D2, <- G2. now rewrite H3. }
    specialize (edge_in node1 node2 H0 D1 G1). apply red in edge_in.    
    destruct edge_in as (edge_in1 & edge_in2).
    split.
    - now rewrite <- D2, <- G2. 
    - exists l1, l2. split; try split; try tauto. now apply edge_in2. 
  Qed. 

  Lemma toPos_for_all_clauses (cl : list Lnode) : isLClique g cl (|c|) -> forall k, k < (|c|) -> exists l, (k, l) el toPos cl. 
  Proof. 
    intros H k H1. 
    (*proof idea: pigeon hole principle. we have a |c|-clique in a graph with 3 * |c| nodes, and we only have edges between vertices of different clauses *)
  Admitted. 
End constructAssgnToPos. 

Section constructAssgnToLiterals. 
  Variable (c : cnf).
  Context (kc : kCNF 3 c). 

  Definition toLiterals' (posl : list (nat * nat)) := map (enumerateLiteral c) posl. 

  Lemma toLiterals'_Some (posl : list (nat * nat)) : (forall a b, (a, b) el posl -> a < (|c|) /\ b < 3) -> forall l', l' el toLiterals' posl -> exists l, l' = Some l.
  Proof.
    intros H l' Hel. 
    unfold toLiterals' in Hel. destruct (map_el Hel) as (pos & H1 & H2). destruct pos as (a & b). specialize (H a b H1). 
    destruct (enumerateLiteral_Some kc (proj1 H) (proj2 H)) as (l & H0). exists l. now rewrite <- H2, H0.
  Qed. 

  (*strip away the Some wrappers*)
  Definition toLiterals (posl : list (nat * nat)) := fold_right (fun (a : option (bool * nat)) acc => match a with Some a' => a'::acc | _ => acc end) [] (toLiterals' posl). 

  Proposition toLiterals_enum (posl : list (nat * nat)) (a : nat * nat):  (forall a b, (a, b) el posl -> a < (|c|) /\ b < 3) -> a el posl -> enumerateLiteral c a <> None. 
  Proof. 
    intros H Hel F. enough (exists l, enumerateLiteral c a = Some l) by (destruct H0; congruence). 
    apply toLiterals'_Some with (posl := posl). apply H.
    unfold toLiterals'. now apply in_map. 
  Qed. 

  Lemma toLiterals_Some (posl :  (list (nat * nat))) : (forall a b, (a, b) el posl -> a < (|c|) /\ b < 3) -> map Some (toLiterals posl) = toLiterals' posl. 
  Proof.
    intros H1.
    induction posl. 
    - now cbn. 
    - cbn. destruct (enumerateLiteral c a) eqn:H. cbn. unfold toLiterals, toLiterals' in IHposl. rewrite IHposl; firstorder. 
      now specialize (toLiterals_enum H1 (or_introl eq_refl)). 
  Qed. 

  Lemma toLiterals_inv (posl: (list (nat * nat))) : (forall a b, (a, b) el posl -> a < (|c|) /\ b < 3) -> forall l, l el toLiterals posl -> exists pos, pos el posl /\ enumerateLiteral c pos = Some l. 
  Proof.
    intros H l Hel. induction posl. 
    - destruct Hel.
    - cbn in Hel. destruct (enumerateLiteral c a) eqn:H1. 2: now specialize (toLiterals_enum H (or_introl eq_refl)). 
      destruct Hel as [-> | Hel]. 
      + now exists a. 
      + destruct (IHposl).
        * firstorder. 
        * apply Hel. 
        * now exists x. 
  Qed. 

  Lemma toLiterals_el (posl : list (nat * nat)) (p : literal) : Some p el toLiterals' posl -> p el toLiterals posl.
  Proof.
    induction posl. 
    - now cbn. 
    - intros [H | H]. 
      + cbn. rewrite H; now left.
      + cbn. destruct (enumerateLiteral c a); [ right | ]; now apply IHposl. 
  Qed. 
    
  (*the no-conflict property transfers from posl to toLiterals posl *)
  Lemma toLiterals_no_conflict (posl : list (nat * nat)): (forall a b, (a, b) el posl -> a < (|c|) /\ b < 3) -> 
    (forall pos1 pos2, pos1 el posl -> pos2 el posl -> (pos1 <> pos2 -> enumLiteral_different_clause pos1 pos2 /\
     exists l1 l2, enumerateLiteral c pos1 = Some l1 /\ enumerateLiteral c pos2 = Some l2 /\ not(literalsConflict l1 l2) ))
        -> (forall l1 l2, l1 el toLiterals posl -> l2 el toLiterals posl -> not (literalsConflict l1 l2)). 
  Proof. 
    intros H0 H l1 l2 H1 H2. 
    specialize (toLiterals_inv H0 H1) as (pos1 & F1 & F2). specialize (toLiterals_inv H0 H2) as (pos2 & E1 & E2). 
    destruct (pair_eqb Nat.eqb Nat.eqb pos1 pos2) eqn:eq. 
    + rewrite <- pair_eqb_correct in eq. rewrite eq in F2. assert (l1 = l2) by congruence. unfold literalsConflict.
      destruct l1, l2. intros H'. assert (b = b0) by congruence. tauto. all: apply nat_eqb_correct. 
    + assert (pos1 <> pos2). {intros H'; rewrite pair_eqb_correct in H'. 2-3: apply nat_eqb_correct. congruence. }
      clear eq. destruct (H pos1 pos2 F1 E1 H3) as (_ & (lit1 & lit2 & G1 & G2 & G3)). 
      assert (lit1 = l1) by congruence. assert (lit2 = l2) by congruence. now rewrite <- H4, <- H5. 
   Qed. 

  (* satisfying the literal list given by toLiterals is enough to satisfy the cnf*)

  Lemma toLiterals_eval_cnf (posl : list (nat * nat)) (a : assgn):
    (forall a b, (a, b) el posl -> a < (|c|) /\ b < 3) 
    -> (forall k, k < (|c|) -> exists l, (k, l) el posl)
    -> (forall l, l el toLiterals posl -> evalLiteral a l = Some true)
    -> varBound_cnf (|a|) c -> evalCnf a c = Some true. 
  Proof. 
    intros H0 H1 H2 H3. 
    apply evalCnf_clause_iff.
    (*we modify the statement in order to get additional information on the index of the clause *)
    enough (forall n, n < |c| -> exists cl, nth_error c n = Some cl /\ evalClause a cl = Some true).
    {
      intros cl Hel. apply In_nth_error in Hel. destruct Hel as (clpos & Hel).
      specialize (nth_error_Some_lt Hel) as Hel'. 
      specialize (H clpos Hel') as (cl' & F1 & F2). assert (cl = cl') by congruence. now rewrite H. 
    }
    intros clpos Hclpos. 
    destruct (nth_error c clpos) as [cl | ] eqn:H4. 
    2: { specialize (proj2 (nth_error_Some c clpos) Hclpos) as H5; congruence. }
    exists cl; split. reflexivity. 
    apply evalClause_literal_iff. split. 2: {rewrite varBound_cnf_iff in H3. apply H3. now apply nth_error_In with (n := clpos).  } 
    specialize (H1 clpos Hclpos) as (lpos & Hlpos). 
    assert (lpos < 3) by firstorder. assert (|cl| = 3).
    {apply kCNF_clause_length with (c:= c); [assumption | now apply nth_error_In with (n:= clpos) ].  }
    rewrite <- H1 in H; clear H1. 
    destruct (nth_error cl lpos) eqn:lEl. 2: { specialize (proj2 (nth_error_Some cl lpos) H); congruence. }
    exists p. split; [now apply nth_error_In with (n:= lpos) | ]. 
    apply H2. 
    assert (enumerateLiteral c (clpos, lpos) el toLiterals' posl ). 
    { apply in_map_iff. exists (clpos, lpos). tauto.  }
    assert (enumerateLiteral c (clpos, lpos) = Some (p)). 
    { unfold enumerateLiteral. rewrite H4. unfold enumerateLiteral'. now apply lEl. }
    rewrite H5 in H1; clear H5. now apply toLiterals_el. 
  Qed. 
End constructAssgnToLiterals.  

(*3 -> 4*)
Section constructAssgnComplete.
  Fixpoint lookup (n: nat) (l : list literal) :=
    match l with [] => None
            | ((a, b)::ls) => if Nat.eqb n b then Some a else lookup n ls
    end. 
  Fixpoint expandAssignment (largestVar : nat) (partial : list literal) :=
    (match lookup largestVar partial with None => false | Some a => a end) :: (match largestVar with 0 => [] | S l => expandAssignment l partial end). 

  Lemma expandAssignment_partial (largestVar : nat) (partial : list literal) :
    forall l, l el partial -> evalLiteral (expandAssignment largestVar partial) l = Some true.
  Proof.
    intros l Hel. 
  Admitted. 

  Lemma expandAssignment_correct (c : cnf) (partialAssign : list literal) (n : nat):
    varBound_cnf n c -> (forall (a : assgn), (forall l, l el partialAssign -> evalLiteral a l = Some true) -> varBound_cnf (|a|) c -> evalCnf a c = Some true)
    -> evalCnf (expandAssignment n partialAssign) c = Some true. 
  Proof.
  Admitted. 

End constructAssgnComplete. 
      

(*now the key result: if a reduction function satisfies the redRel, then it admits a "correct" reduction from SAT to LClique *)
Lemma redRel_reduces (c : cnf) (cl : Lgraph * nat) : redRel c cl -> (SAT c <-> LClique cl ).
Proof. 
  split. 
  + intros (a & H1). destruct cl as (g & k). destruct g. cbn in H.
    destruct H as (neq & keq & tcnf & labF & labFInv & labinv & H2).
    exists (map labFInv (constructClique_cnf a c)).
    rewrite isLClique_explicit_correct. 
    split; try split; try split. 
    - rewrite map_length. rewrite construct_length. 2: apply H1. now rewrite keq. 
    - clear H2. rewrite <- dupfree_map_bijection. 
      2: {apply inverse_symmetric. now destruct labinv. }
      apply construct_dupfree. 
    - intros node H.
      enough (node < 3 * |c|) by ( unfold Lgraph_node_in_dec; apply leb_correct; lia ).
      destruct (map_el H) as (nodepos & F1 & F2). rewrite <- F2. destruct nodepos as (clpos & litpos).
      apply isLabelling_range_inv with (f:=labF); [apply labinv | apply construct_literals_bound with (a:=a); [apply tcnf | apply F1]]. 
    - intros u v F1 F2 F3. destruct (map_el F2) as ((ucl & ulit) & G1 & G2). destruct (map_el F3) as ((vcl & vlit) & D1 & D2). 
      specialize (H2 u v). change (n = 3 * (|c|)) in neq. 
      assert (u < n). { rewrite neq. rewrite <- G2. apply (isLabelling_range_inv labinv). apply construct_literals_bound with (a:=a);
                      [ apply tcnf | apply G1]. }
      assert (v < n). {rewrite neq. rewrite <- D2. apply (isLabelling_range_inv labinv). apply construct_literals_bound with (a:=a);
                       [apply tcnf | apply D1]. }
      specialize (H2 (conj H H0)).  cbn. apply H2. assert ((ucl, ulit) <> (vcl, vlit)).
      {contradict F1. rewrite <- G2, <- D2. now rewrite F1. }
      split.
      -- rewrite <- G2, <- D2. repeat rewrite (match labinv with conj inve _ => match inve with conj _ re => re end end).
         now apply (construct_literals_different_clause G1 D1). 
      -- intros l1 l2 E1 E2. rewrite <- G2 in E1. rewrite <- D2 in E2.
         rewrite (match labinv with conj inve _ => match inve with conj _ re => re end end) in E1.
         rewrite (match labinv with conj inve _ => match inve with conj _ re => re end end) in E2. 
         destruct (construct_literals_no_conflict G1 D1 H3) as (l1' & l2' & H4 & H5 & H6).  rewrite <- H4 in E1. rewrite <- H5 in E2. 
         easy. 
  +  

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

Definition reduction (c : cnf) : Lgraph * nat := (redGraph c, |c|). 

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

Lemma reduction_sat_redRel (c : cnf) : redRel c (reduction c). 
Proof. 
  unfold redRel. destruct (reduction c) as (g, k) eqn:H. destruct g as (n, e). 
  unfold reduction in H. inversion H. unfold redGraph in H1. destruct (kCNF_decb 3 c) eqn:H3. 
  - inv H1. split. reflexivity. 


(* Lemma makeEdges_correct (c : cnf) : kCNF 3 c -> forall (l l' : literal) (n n' : nat), (n < 3 * (|c|) /\ n' < 3 * (|c|) /\ enumerateLiteral c 3 n = Some l /\ enumerateLiteral c 3 n' = Some l') *)
(*                                                -> (not (literalsConflict l l') /\ enumLiteral_different_clause c 3 n n'  <-> *)
(*                                                   Lgraph_edge_in_dec' (makeEdges c 0) n n').  *)
(* Abort.  *)

Lemma tsat_to_clique  : reducesPolyMO (kSAT 3) LClique. 
Proof. 
  
Admitted. 

