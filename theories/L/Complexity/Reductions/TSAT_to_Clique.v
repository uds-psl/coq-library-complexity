From Undecidability.L.Complexity Require Import NP Synthetic Problems.SAT Problems.Clique Problems.kSAT MorePrelim.
From Undecidability.L Require Import Tactics.LTactics.
From Undecidability.L.Complexity Require Import Problems.LGraph MorePrelim.
Require Import Coq.Init.Nat.
Import PslBase.Bijection.


(** TODO: might factor out some parts to a new variant of SAT that does work with list (bool * nat) assignments *)

(*We proceed in the following way: *)
(*First, we define a relation on cnf * (LGraph * nat) that connects 3-SAT instances to Clique instances *)
(* This graph has to satisfy the following properties with relation to the CNF: *)
(* For every clause c, there are three nodes n^c_1, n^c_2, n^c_3 , corresponding to the three literals.*)
(* Nodes n^c_i and n^d_j are connected iff c <> d and the literals corresponding to n^c_i and n^d_j are not conflicting.*)
(* If there are k clauses, we then have a k-clique iff the CNF is satisfiable.*)
(*The above construction implies that the graph should have 3 * |c| nodes, where c is the CNF *)

(*The relation will abstract away from specific connections between literals and nodes by working with an abstract labelling function*)

(*a labelling function for a graph that assigns a clause and a literal index *)
Definition labGraph:= nat -> nat * nat.
Definition labGraphInv := nat * nat -> nat. 

(*The labelling function should form a bijection between literals and graph nodes *)
Definition inverseOn (X Y : Type) (f : X -> Y) (g : Y -> X) (p : X -> Prop) (q : Y -> Prop) :=
  (forall x, p x -> q (f x) /\ x = g(f x)) /\ (forall y, q y -> p (g y) /\ y = f(g y)). 
Definition isLabelling (c : cnf) (f : labGraph) (fInv : labGraphInv) :=
  inverseOn f fInv (fun n => n < 3 * |c|) (fun n => let (a, b):= n in a < (|c|) /\ b < 3). 

(*A technical lemma that we will later need to work with the labelling function*)
Lemma map_inverse_el (X Y : Type) (f : X -> Y) (g : Y -> X) (p : X -> Prop) (q : Y -> Prop) (l : list Y) :
  inverseOn f g p q -> (forall x, x el l -> q x) -> forall x, q x -> g x el (map g l) -> x el l /\ p (g x).
Proof.
  intros [H1 H2] H3 y H4 H5. induction l.
  + destruct H5.
  + destruct H5 as [H5 | H5].
    - clear IHl. split.
      * left. rewrite (proj2(H2 y H4)). rewrite (proj2(H2 a (H3 a (or_introl eq_refl)))). 
        now rewrite H5.
      * now apply H2. 
    - assert (forall x, x el l -> q x) by firstorder. specialize (IHl H H5). split; [right|]; apply IHl. 
Qed. 

Lemma inverseOn_symmetric {X Y : Type} {f : X -> Y} {g : Y -> X} {p : X -> Prop} {q : Y->Prop}:
  inverseOn f g p q <-> inverseOn g f q p.
Proof. unfold inverseOn. tauto. Qed. 

Lemma dupfree_map_inverse (X Y : Type) (f : X -> Y) (g : Y -> X) (p : X -> Prop) (q : Y -> Prop) (l : list Y): inverseOn f g p q -> dupfree l -> (forall x, x el l -> q x) -> dupfree (map g l). 
Proof.
  intros H1 H3 H4.   
  induction H3. 
  - cbn; constructor. 
  - cbn. constructor.
    + contradict H. apply (map_inverse_el (l:=A) H1); firstorder. 
    + apply IHdupfree. firstorder. 
Qed. 

(*The notion of conflicting literals, i.e. literals that cannot simultaneously be positive for any assignment*)
Definition literalsConflict (a b : literal) := match a, b with (s1, v1), (s2, v2) => s1 <> s2 /\ v1 = v2 end.

Lemma literalsConflict_eval (s s' : bool) (n n' : nat) (a : assgn) : n' < |a| -> n < |a| -> (literalsConflict (s, n) (s', n') <-> (evalLiteral a (s, n) <> evalLiteral a (s', n') /\ n = n')). 
Proof.
  intros H1 H2. split.
  - intros [F1 F2]. rewrite F2. cbn. apply (nth_error_Some a n') in H1. destruct (nth_error a n'). 2: split; auto.
    split; try reflexivity. enough (Bool.eqb s b <> Bool.eqb s' b) by congruence. destruct s, b, s'; cbn; congruence.
  - intros [F1 ->]. split. 2: reflexivity. cbn in F1. apply (nth_error_Some a n') in H1. destruct (nth_error a n').
    2: auto. destruct s, s', b; cbn in F1; congruence. 
Qed. 


(*A boolean decider *)
Definition literalsConflictb (a b : literal) := match a, b with (s1, v1), (s2, v2) => negb(Bool.eqb s1 s2) && Nat.eqb v1 v2 end. 
Lemma literalsConflictb_correct (a b : literal) : literalsConflict a b <-> literalsConflictb a b = true. 
  split; unfold literalsConflictb; destruct a, b.
  - intros H. simp_bool; split; simp_bool. all: destruct H; dec_bool. 
  - intros H. simp_bool. split; dec_bool. 
Qed. 

Section enumLiteral.
  (*In this section, we derive from a (clause, literal) index pair the corresponding literal in a kCNF *)
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

  Lemma enumerateLiteral_Some_inv (c : cnf) : kCNF k c -> forall n n', (exists (l : literal), enumerateLiteral c (n, n') = Some l) -> n < |c| /\ n' < k. 
  Proof.
     induction c. 
    - intros H n n' (l & H1). cbn in H1. destruct n; cbn in H1; congruence.  
    - intros H n n' (l & H1). cbn in H1. destruct n; cbn in H1.
      + apply nth_error_Some_lt in H1. inv H. split; cbn; lia. 
      + inv H. cbn. enough (n < |c| /\ n' < |a|) by lia. apply IHc; [apply H4|]. 
        exists l. apply H1. 
  Qed.

  Definition enumLiteral_different_clause (l1 : nat * nat) (l2 : nat * nat) := fst l1 <> fst l2. 
  Hint Unfold enumLiteral_different_clause. 
End enumLiteral.



(*The reduction relation, as described above *)
(*We explicitly enforce that the graph has a suitable number of nodes *)
(*TODO: maybe remove the kCNF constraint? *)
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
  (*Given a clause cl, find the index of a literal that is satisfied by the assignment a *)
  (*If there is none, return None*)
  Fixpoint constructClique_clause' (a : assgn) (cl_index : nat) (cl : clause) (lit_index : nat):=
  match cl with [] => None
              | (l :: cl) => match evalLiteral a l with Some true => Some (cl_index, lit_index)
                                               | _  => constructClique_clause' a cl_index cl (S lit_index)
  end end. 
  Definition constructClique_clause (a : assgn) (cl_index : nat) (cl : clause) := constructClique_clause' a cl_index cl 0.

  (*Given a cnf cn, find a list of (clause, literal) indices, one for each clause, that is satisfied by the assignment*)
  (*If there is no such literal for some clause (the assignment is not satisfying), return an empty list *)
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
    intros H.
    enough (forall (m : nat), |constructClique_cnf' a cn m| = |cn|) by apply (H0 0). 
    induction cn. 
    - intros; now cbn.
    - intros m. 
      cbn. specialize (everyClause' H (or_introl eq_refl) m ) as (k & ->). cbn. 
      rewrite IHcn; [lia|].  
      apply evalCnf_step_inv in H as (b1 & b2 & H1 & H2 & H3). simp_bool'.
  Qed. 

  Lemma constructClique_clause_pos (a : assgn) (cl_index : nat) (cl : clause) : forall pos, constructClique_clause  a cl_index cl = Some pos -> fst pos = cl_index.
  Proof. 
    intros (p1 & p2). cbn [fst].
    unfold constructClique_clause. generalize 0. induction cl.
    - intros; cbn in H; congruence. 
    - intros. cbn in H. destruct (evalLiteral a a0) eqn:H1. destruct b.
      * congruence. 
      * now apply IHcl with (n:= S n). 
      * now apply IHcl with (n:= S n). 
  Qed. 

  Lemma constructClique_cnf'_pos (a : assgn) (cn : cnf) (clpos: nat): forall pos, pos el constructClique_cnf' a cn clpos -> fst pos >= clpos. 
  Proof.
    intros pos H. revert clpos H; induction cn.
    - intros; destruct H.
    - intros; cbn in H. destruct (constructClique_clause a clpos a0) eqn:H1. destruct H as [-> | H2]. 
      * destruct pos. apply constructClique_clause_pos in H1. firstorder.   
      * apply IHcn in H2. lia. 
      * destruct H. 
  Qed. 

  (* We prove this slightly awkward version using nth_error since this also allows us to show that the result is duplicate-free *)
  Lemma construct_literals_different_clause' (a : assgn) (cn : cnf) : forall (pos pos' : nat * nat) (i j: nat),
      nth_error (constructClique_cnf a cn) i = Some pos -> nth_error (constructClique_cnf a cn) j = Some pos'
      -> i <> j -> enumLiteral_different_clause pos pos'.
  Proof.
    intros pos pos'. unfold constructClique_cnf. generalize 0. induction cn.
    - cbn; intros.  destruct i; cbn in H; congruence. 
    - intros. cbn in H, H0. destruct (constructClique_clause a n a0) eqn:H2; destruct i, j; cbn in H, H0. 
      + congruence. 
      + apply nth_error_In in H0. apply constructClique_clause_pos in H2. apply constructClique_cnf'_pos in H0. destruct pos, pos', p; cbn in H0, H2.  
        unfold enumLiteral_different_clause; cbn. rewrite H2 in H. inv H.  lia. 
      + apply nth_error_In in H. apply constructClique_clause_pos in H2. apply constructClique_cnf'_pos in H. destruct pos, pos', p; cbn in H, H2.  
        unfold enumLiteral_different_clause; cbn. rewrite H2 in H0. inv H0. lia.
      + now apply IHcn with (n := S n) (i:= i) (j:= j).
      + congruence. 
      + congruence. 
      + congruence. 
      + congruence. 
   Qed. 

  Corollary construct_literals_different_clause (a : assgn) (cn : cnf) : forall (pos pos' : nat * nat), pos el constructClique_cnf a cn -> pos' el constructClique_cnf a cn -> pos <> pos' -> enumLiteral_different_clause pos pos'. 
  Proof.
    intros. apply In_nth_error in H as (n & H). apply In_nth_error in H0 as (n' & H0).
    now apply construct_literals_different_clause' with (a:=a) (cn:=cn) (i:=n)(j:=n').
  Qed. 

  Corollary construct_dupfree ( a : assgn) (cn : cnf) : dupfree(constructClique_cnf a cn). 
  Proof.
    apply dupfree_nthe. intros. 
    specialize (construct_literals_different_clause' H H0 H1). unfold enumLiteral_different_clause. firstorder.
  Qed. 

  Lemma construct_literals_positive' (a : assgn) (m : nat) (cl : clause)  : forall n, constructClique_clause a m cl = Some (m, n)
                                                                               -> exists (l : literal), enumerateLiteral' cl n = Some l
                                                                                    /\ evalLiteral a l = Some true.
  Proof.
    intros n. unfold constructClique_clause. replace (enumerateLiteral' cl n) with (enumerateLiteral' cl (n - 0)) by (now rewrite Nat.sub_0_r).
    generalize 0. induction cl. 
    - cbn. congruence. 
    - intros n'. cbn. destruct (evalLiteral a a0) eqn:H1. 
      + destruct b.
        * intros [=]. rewrite H0, <- minus_diag_reverse. exists a0. firstorder. 
        * intros H2. destruct (IHcl (S n') H2) as (l & F1 & F2). exists l.
          destruct n. cbn. 
  Admitted. 
                                                                                  
                                                                                                                               

  Lemma construct_literals_positive (a : assgn) (cn : cnf) : forall (pos : nat * nat), pos el constructClique_cnf a cn
                                                            -> exists (l : literal), enumerateLiteral cn pos = Some l
                                                                 /\ evalLiteral a l = Some true. 
  Proof.
    enough (forall m pos, pos el constructClique_cnf' a cn m -> exists l, enumerateLiteral cn pos = Some l /\ evalLiteral a l = Some true) by firstorder.
    induction cn. 
    - intros m pos []. 
    - cbn. intros m pos. destruct (constructClique_clause a m a0) eqn:H1. 2: intros []. 
      intros [-> | H2]. 
      + destruct pos. 
    (*by induction over the structure of the CNF again*)
  Admitted. 

  Lemma construct_literals_no_conflict (a : assgn) (cn : cnf) : forall (pos pos' : nat * nat), pos el constructClique_cnf a cn -> pos' el constructClique_cnf a cn -> pos <> pos'
    -> exists l l', Some l = enumerateLiteral cn pos /\ Some l' = enumerateLiteral cn pos' /\ not(literalsConflict l l').
  Proof.
    intros pos pos' H1 H2 H3. destruct (construct_literals_positive H1) as (l1 & F1 & F2). 
    destruct (construct_literals_positive H2) as (l2 & G1 & G2). exists l1, l2. 
    split; try split; firstorder. intros H. destruct l1, l2. rewrite literalsConflict_eval in H.
    2: { eapply evalLiteral_varBound. exists true; apply G2.  }
    2: { eapply evalLiteral_varBound. exists true; apply F2. }
    destruct H; congruence.  
  Qed. 


  Lemma construct_literals_bound (a : assgn) (cn : cnf) (k : nat) : kCNF k cn -> forall (n m : nat), (n, m) el constructClique_cnf a cn -> n < |cn| /\ m < k. 
  Proof.
    intros H n m H1. apply enumerateLiteral_Some_inv. apply H.
    destruct (construct_literals_positive H1) as (l & H2 & _). exists l; apply H2. 
  Qed. 

End constructClique.

(*Now the converse: from a clique, we can construct a satisfying assignment for the corresponding CNF*)
(*Since the reduction relation redRel is inherently asymmetric, the structure of this proof is different from the other direction above.*)
(*We need argue directly over the target CNF and use the facts given by redRel. *)

  (*We proceed in the following way *)
  (*1) We start with a graph g, CNF c, and a |c|-clique cl; g, c need to satisfy redRel*) 
  (*2) This is translated to a list of (clause, literal)-positions, giving the positions of literals corresponding to the nodes in cl *)
  (*   The literals at these positions are non-conflicting and there is exactly one for every clause*)
  (*3) We then map this to a list of literals at these positions*)
  (*   again these are non-conflicting and if all of them are satisfied, then the CNF evaluates to true. *)
  (*   The list in 3) can also be interpreted as a list of fixed assignments list (nat * bool) *)
  (*   - if all other variables are set arbitrarily, then the CNF evals to true*)
  (*4) This is expanded to a complete assignment using cnf_maxVar - under this assignment, c evaluates to true *)

Section constructAssgnToPos.
  (*1 -> 2*)
  Variable (c : cnf) (g : Lgraph).
  Variable (f : labGraph) (fInv: labGraphInv). 
  Context (islab : isLabelling c f fInv). 

  (*c, g are associated via redRel using the labelling f, fInv *)
  Context (nc : fst g = 3 * |c|).
  Context (kc : kCNF 3 c). 
  Context (red : forall (u v : nat), u < fst g /\ v < fst g -> (Lgraph_edge_in_dec g u v = true <->
      (enumLiteral_different_clause (f u) (f v) /\
      (forall (l1 l2 : literal), enumerateLiteral c (f u) = Some l1 ->
                               enumerateLiteral c (f v) = Some l2 ->
                               not (literalsConflict l1 l2))))). 

  Definition toPos (cl : list Lnode) := map f cl. 

  Lemma toPos_bounded (cl : list Lnode) : isLClique g cl (|c|) -> forall a b, (a, b) el toPos cl -> a < (|c|) /\ b < 3. 
  Proof. 
    intros H a b Hel. unfold toPos in Hel; apply map_el in Hel. destruct Hel as (node & Hel1 & Hel2). specialize (isLClique_node_in H Hel1) as Hel3.  
    unfold Lgraph_node_in_dec in Hel3. destruct g. dec_bool. destruct islab. cbn [fst] in nc; specialize (H0 node); rewrite <- nc, Hel2 in H0. tauto. 
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

  Proposition demorgan_not_exists_forall (X : Type) (p : X -> Prop) : (not (exists x, p x)) -> forall x, not (p x). 
  Proof. intros H x px. now apply H. Qed.
  Lemma toPos_for_all_clauses (cl : list Lnode) : isLClique g cl (|c|) -> forall k, k < (|c|) -> exists l, (k, l) el toPos cl.
  Proof.
    intros H k H1. 
    (* We can constructively assume that ¬ (∃ l, (k, l) ∈ toPos cl), since the range of possible values for l is bounded by 3.*)
    enough (not (not  (exists l, (k, l) el toPos cl))). 
    {destruct (list_in_decb (pair_eqb Nat.eqb Nat.eqb) (toPos cl) (k, 0)) eqn:F1; 
    [apply (list_in_decb_iff (eqb := pair_eqb Nat.eqb Nat.eqb)) in F1 | apply (list_in_decb_iff' (eqb := pair_eqb Nat.eqb Nat.eqb)) in F1].
    2, 4: apply pair_eqb_correct; apply nat_eqb_correct. now exists 0.
    
    destruct (list_in_decb (pair_eqb Nat.eqb Nat.eqb) (toPos cl) (k, 1)) eqn:F2; 
    [apply (list_in_decb_iff (eqb := pair_eqb Nat.eqb Nat.eqb)) in F2 | apply (list_in_decb_iff' (eqb := pair_eqb Nat.eqb Nat.eqb)) in F2].
    2, 4: apply pair_eqb_correct; apply nat_eqb_correct. now exists 1.

    destruct (list_in_decb (pair_eqb Nat.eqb Nat.eqb) (toPos cl) (k, 2)) eqn:F3; 
    [apply (list_in_decb_iff (eqb := pair_eqb Nat.eqb Nat.eqb)) in F3 | apply (list_in_decb_iff' (eqb := pair_eqb Nat.eqb Nat.eqb)) in F3].
    2, 4: apply pair_eqb_correct; apply nat_eqb_correct. now exists 2.

    exfalso. apply H0. intros (l & H2). destruct l; try destruct l; try destruct l; try congruence.  
    specialize (toPos_bounded H H2); firstorder. }

    intros H2.

    specialize (demorgan_not_exists_forall H2) as H3. cbn in H3. clear H2. 

    (*If we can show that there are is a clause that occurs twice in toPos, we are finished *)
    enough (rep (map fst (toPos cl))). 
    {
      apply (rep_sigma _) in H0 as (A1 & k' & A2 & A3 & H0).
      assert (exists p1 p2 h1 h2, p1 <> p2 /\ nth_error (toPos cl) p1 = Some (k', h1) /\ nth_error (toPos cl) p2 = Some (k', h2)).
      {
        exists (|A1|), (1 + |A1| + |A2|).
        assert (|toPos cl| = 2 + |A1| + |A2| + |A3|).
        { erewrite <- map_length. rewrite H0. repeat (rewrite app_length; cbn). lia. }
        destruct nth_error eqn:F1. 2: {apply nth_error_None in F1. lia. }
        destruct (nth_error (toPos cl) (1 + ((|A1|) + (|A2|)))) eqn:F2. 2: {apply nth_error_None in F2. lia. }
        destruct p, p0. 
        (* n = n1 = k by H0*)
        (*for F1 *)
        apply (map_nth_error (B:= nat) (fst) ) in F1. rewrite H0 in F1. rewrite nth_error_app2 in F1; [|lia].
        rewrite Nat.sub_diag in F1. cbn in F1. 
        (*for F2*)
        apply (map_nth_error (B:= nat) (fst) ) in F2. rewrite H0 in F2. rewrite nth_error_app2 in F2; [|lia].
        replace (1 + (|A1| + |A2|) - |A1|) with (1 + |A2|) in F2 by lia. cbn in F2.
        rewrite nth_error_app2 in F2; [|lia]. rewrite Nat.sub_diag in F2. cbn in F2.

        exists n0, n2. split; [lia|split;congruence ]. 
      }
      (*we make a case distinction: *)
      (*if h1 = h2, then there was a duplicate in the clique cl, since the labelling f in toPos is injective *)
      (*otherwise, we get a contradiction by toPos_no_conflict*)
      destruct H2 as (p1 & p2 & h1 & h2 & F1 & F2 & F3).
      destruct (Nat.eqb h1 h2) eqn:H2.
      - dec_bool. 
        specialize (proj1(isLClique_explicit_correct g cl (|c|)) H) as (_ & cldupfree & clnodein & _).
        apply (dupfree_map_inverse (proj1 (inverseOn_symmetric) islab)) in cldupfree.
        2: {
          unfold Lgraph_node_in_dec in clnodein. destruct g. cbn [fst] in nc; rewrite nc in clnodein.
          intros x H4. specialize (clnodein x H4). dec_bool. 
        }
        rewrite dupfree_nthe in cldupfree. specialize (cldupfree p1 p2 (k', h1) (k', h2) F2 F3 F1). 
        congruence. 
      - dec_bool. apply nth_error_In in F2. apply nth_error_In in F3.
        assert ((k', h1) <> (k', h2)) by congruence. 
        specialize (toPos_no_conflict H F2 F3 H4) as (diffcl & _).
        unfold enumLiteral_different_clause in diffcl; cbn in diffcl; congruence.
    }

    (*Now we apply the pigeonhole principle: There are |c| elements in map fst (toPos c), but only |c|-1 in [0, ..., |c| -1] \ [k] *)
    eapply (pigeonhole _).
    - enough (map fst (toPos cl) <<= remove nat_eq_dec k (seq 0 (|c|)) ) by apply H0.
      specialize (toPos_bounded H) as H4. 
      clear red kc H. 
      induction cl; cbn.
      + firstorder. 
      + apply incl_cons.
        * apply remove_el. rewrite in_seq. cbn in H3, H4. split; destruct (f a).
          -- specialize (H4 n n0 (or_introl eq_refl)). cbn. lia. 
          -- specialize (H3 n0). cbn. contradict H3. left; congruence.
        * apply IHcl. firstorder. intros a0 b; specialize (H4 a0 b). firstorder.  
   - repeat rewrite map_length.
     assert (k el seq 0 (|c|)) by (apply in_seq; lia). 
     specialize (remove_length_el nat_eq_dec H0) as H4.
     rewrite seq_length in H4. 
     specialize (proj1 (isLClique_explicit_correct g cl (|c|)) H) as (clsize &_). lia. 
  Qed. 
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

  Lemma expandAssignment_length (n : nat) (partial : list literal) : |expandAssignment n partial| = S n.
  Proof.
    induction n. 
    - now cbn. 
    - cbn. now rewrite IHn. 
  Qed. 

  Lemma expandAssignment_partial (largestVar : nat) (partial : list literal) : varBound_clause largestVar partial ->
    forall l, l el partial -> evalLiteral (expandAssignment largestVar partial) l = Some true.
  Proof.

  Admitted. 

  Lemma expandAssignment_correct (c : cnf) (partialAssign : list literal) (n : nat):
    varBound_cnf (S n) c -> (forall (a : assgn), (forall l, l el partialAssign -> evalLiteral a l = Some true) -> varBound_cnf (|a|) c -> evalCnf a c = Some true)
    -> evalCnf (expandAssignment n partialAssign) c = Some true. 
  Proof.
  Admitted. 

End constructAssgnComplete. 
      
Section constructAssgn.
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


  Definition clique_to_assgn (cl : list Lnode) := expandAssignment (cnf_maxVar c) (toLiterals c (toPos f cl)).

  Lemma assgn_satisfies (cl : list Lnode) : isLClique g cl (|c|) -> evalCnf (clique_to_assgn cl) c = Some true.
  Proof. 
    intros Hclique. 
    unfold clique_to_assgn. apply expandAssignment_correct. 1: now apply cnf_maxVar_bound. 
    intros a. apply toLiterals_eval_cnf. 1: now apply kc. 
    - apply toPos_bounded with (g := g) (fInv := fInv); [apply islab | apply nc | apply red | apply Hclique]. 
    - apply toPos_for_all_clauses with (g := g) (fInv := fInv); [apply islab | apply nc | apply kc | apply red | apply Hclique]. 
  Qed. 
End constructAssgn. 


(*now the key result: if a reduction function satisfies the redRel, then it admits a "correct" reduction from SAT to LClique *)
Lemma redRel_reduces (c : cnf) (cl : Lgraph * nat) : redRel c cl -> (kSAT 3 c <-> LClique cl ).
Proof. 
  split. 
  + intros (_ & a & H1). destruct cl as (g & k). destruct g. cbn in H.
    destruct H as (neq & keq & tcnf & labF & labFInv & labinv & H2).
    exists (map labFInv (constructClique_cnf a c)).
    rewrite isLClique_explicit_correct. 
    split; try split; try split. 
    - rewrite map_length. rewrite construct_length. 2: apply H1. now rewrite keq. 
    - clear H2. destruct labinv. apply dupfree_map_inverse with (f:= labF) (p := fun x => x < 3 * |c|) (q:=fun (y : nat * nat)=> let (a, b):= y in a < |c| /\ b < 3);
      [apply (conj H H0) | apply construct_dupfree |  intros (x & y); now apply construct_literals_bound]. 
    - intros node H.
      enough (node < 3 * |c|) by ( unfold Lgraph_node_in_dec; apply leb_correct; lia ).
      destruct (map_el H) as (nodepos & F1 & F2). rewrite <- F2. destruct nodepos as (clpos & litpos).
      apply labinv. now apply construct_literals_bound with (a:=a). 
    - intros u v F1 F2 F3. destruct (map_el F2) as ((ucl & ulit) & G1 & G2). destruct (map_el F3) as ((vcl & vlit) & D1 & D2). 
      specialize (H2 u v). change (n = 3 * (|c|)) in neq. 
      assert (u < n). { rewrite neq. rewrite <- G2. apply labinv. now apply construct_literals_bound with (a:=a). }
      assert (v < n). {rewrite neq. rewrite <- D2. apply labinv. now apply construct_literals_bound with (a:=a). }
      specialize (H2 (conj H H0)).  cbn. apply H2. assert ((ucl, ulit) <> (vcl, vlit)).
      {contradict F1. rewrite <- G2, <- D2. now rewrite F1. }
      assert (labF (labFInv (ucl, ulit)) = (ucl, ulit) /\ labF(labFInv(vcl, vlit)) = (vcl, vlit)) as (H4 & H5). 
      { split; symmetry; apply labinv; now apply construct_literals_bound with (a:=a). }
      split.
      -- rewrite <- G2, <- D2. rewrite H4, H5. now apply (construct_literals_different_clause G1 D1). 
      -- intros l1 l2 E1 E2. rewrite <- G2 in E1. rewrite <- D2 in E2.
         rewrite H4 in E1. rewrite H5 in E2. 
         destruct (construct_literals_no_conflict G1 D1 H3) as (l1' & l2' & H6 & H7 & H8).  rewrite <- H6 in E1. rewrite <- H7 in E2. 
         easy.
  + destruct cl as (g & k). intros (cl & Hclique).
        destruct g as (n, e). destruct H as (nc & kc &kcnf & (f & fInv & islab & red)).  
        split; [apply kcnf|]. exists (clique_to_assgn c f cl).
        now apply assgn_satisfies with (g:= (n, e)) (fInv := fInv). 
Qed. 

(*Layout of the constructed instance: To every clause with index i, we assign three nodes with indices 3i..3i+2 *)

(*Contruction principle: enumerate the literals from left to right; for each literal go through the literals *)
(*of the clauses to the right of it and make appropriate edges. *)
(* This suffices since we are dealing with an undirected graph.*)

(*make edges between the literal l and all qualifying literals in clause cl. numAcc is the index of the first literal in cl *)
Fixpoint makeEdgesLiteral' (l : literal) (numL : nat) (cl :clause) (numAcc : nat) :=
  match cl with [] => []
              | (l' :: cl) => if literalsConflictb l l' then makeEdgesLiteral' l numL cl (S numAcc) else (numL, numAcc) :: makeEdgesLiteral' l numL cl (S numAcc)
  end.

(*make edges where the first node (literal) is fixed. l is the first node and numL its index, while numAcc is the index of the first literal in cn *)
Fixpoint makeEdgesLiteral (l : literal) (numL : nat) (cn : cnf) (numAcc : nat) := match cn with [] => []
  | (cl::cn) => makeEdgesLiteral' l numL cl numAcc ++ makeEdgesLiteral l numL cn (3 + numAcc) end.

(*make all edges where the first node is from c. numL is the index of c's first literal *)
Fixpoint makeEdges' (c : clause) (numL : nat) (cn : cnf) (numCn : nat):= match c with [] => []
                                                           | (l :: c) => makeEdgesLiteral l numL cn numCn ++ makeEdges' c (S numL) cn numCn
                                                           end. 
(*make edges for a whole cnf. numL is the index of the first literal in c *)
(* this makes use of the fact that we are constructing an undirected graph and we don't want any edges within the same clause*)
Fixpoint makeEdges (c : cnf) (numL : nat) := match c with [] => []
             | (cl::c) => makeEdges' cl numL c (3 + numL) ++ makeEdges c (3 + numL) end.

(* using makeEdges, we can construct the whole clique instance*)
(* if the input CNF isn't a 3-CNF (this implies that the CNF isn't empty), we construct *)
(* an empty graph - this graph will not have a k-clique for any k > 0, *)
(* in particular not a (|c|)-clique *)
Definition redGraph (c : cnf) : Lgraph := if kCNF_decb 3 c then (3 * |c|, makeEdges c 0)
                                                            else (0, []). 

Definition reduction (c : cnf) : Lgraph * nat := (redGraph c, |c|). 

Definition labF (n : nat) := (n /3, n mod 3). 
Definition labFInv (n : nat * nat) := (fst n * 3 + snd n). 

Lemma labF_proj (a b : nat) : b < 3 -> labF(3 * a + b) = (a, b). 
Proof. 
  intros H. unfold labF. 
  rewrite Nat.mul_comm. rewrite Nat.div_add_l; [|lia]. rewrite Nat.add_comm with (n := a * 3). 
  rewrite Nat.mod_add; [| lia]. rewrite Nat.div_small; [|apply H]. rewrite Nat.mod_small; [|apply H]. now rewrite Nat.add_0_r. 
Qed. 

Lemma labF_inv (k a b : nat) : labF k = (a, b) -> k = 3 * a + b.
Proof. 
  unfold labF. intros H. inversion H. apply Nat.div_mod. lia.
Qed. 

Lemma labF_isLabelling (c : cnf) : isLabelling c labF labFInv. 
  split. 
  - split.
    + cbn [labF]. split.
      * enough (S(x/3) <= |c|) by lia. assert (S x <= 3 * |c|) by lia. clear H. 
        (* this is not entirely straightforward *)
        admit.
      * cbn. destruct (Nat.divmod); destruct n0; try destruct n0; cbn; lia. 
    + unfold labF, labFInv. cbn [fst snd]. replace ((x/3) * 3) with (3 * (x/3)) by lia. now apply Nat.div_mod. 
  - intros (a & b) H. split.
    + unfold labFInv; cbn [fst snd]. destruct H. lia. 
    + cbn. now rewrite <- labF_proj. 
Admitted. 



Section makeEdgesVerification.
  Lemma makeEdgesLiteral'_iff (numL numAcc : nat) (l : literal) (cl : clause) (a b : nat) :
    (a, b) el makeEdgesLiteral' l numL cl numAcc <-> (exists k, exists l', nth_error cl k = Some l' /\ a = numL /\ b = numAcc + k /\ not(literalsConflict l l')).
  Proof. 
    revert numAcc. induction cl.
    - intros numAcc. cbn. firstorder. destruct x; cbn in H; congruence. 
    - intros numAcc. split.
      + cbn. destruct (literalsConflictb l a0) eqn:Hel. 
        * intros (k & l' & H1 & H2 & H3 & H4)%IHcl. exists (S k), l'. split; try split; try split; try tauto; try lia.
        * intros [H | (k & l' & H1 & H2 & H3 & H4)%IHcl].
          -- exists 0, a0. assert (numL = a) by congruence. assert (numAcc = b) by congruence.
             split; try split; try split; try tauto; try lia.
             now intros H2%literalsConflictb_correct. 
          -- exists (S k), l'. split; try split; try split; try tauto; try lia.
     + intros (k & l' & H1 & H2 & H3 & H4). 
       destruct k. 
       * cbn. destruct (literalsConflictb l a0) eqn:H5. 
         -- exfalso. apply literalsConflictb_correct in H5. cbn in H1. congruence.  
         -- left. now rewrite H2, H3, Nat.add_0_r.
      * cbn in H1. cbn. destruct (literalsConflictb l a0);[ | right]. 
        all: apply IHcl. all: exists k, l'; firstorder. 
  Qed. 

  Lemma makeEdgesLiteral_iff (numL numAcc : nat) (l : literal) (cn : cnf) (a b : nat) : kCNF 3 cn -> 
    ((a, b) el makeEdgesLiteral l numL cn numAcc <-> (a = numL /\
     exists clpos lpos, lpos < 3 /\ clpos < (|cn|) /\ exists cl l', nth_error cn clpos = Some cl /\ nth_error cl lpos = Some l' /\
     b = numAcc + 3 * clpos + lpos /\ not (literalsConflict l l'))). 
  Proof.
    intros kc. revert numAcc. induction cn.
    - intros. cbn. firstorder. 
    - intros. split.
      + cbn. intros [H|H]%in_app_or. 
        * apply makeEdgesLiteral'_iff in H. destruct H as (k & l' & H1 & H2 & H3 & H4). 
          split; [assumption|]. exists 0, k. split; try split.
          -- inv kc. apply nth_error_Some_lt in H1; lia. 
          -- lia.
          -- exists a0, l'. cbn. split; [reflexivity | split; [apply H1 | split; [lia | apply H4]]].
       * inv kc. apply (IHcn H3) in H.
         destruct H as (F1 & (clpos & lpos & F2 & F3 & (cl & l' & F4 & F5 & F6 & F7))). 
         split; [apply F1 | exists (S(clpos)), lpos ].
         split; [apply F2 | split; [lia | exists cl, l']]. 
         cbn. firstorder.  
    + intros (F1 & (clpos & lpos & F2 & F3 & (cl & l' & F4 & F5 & F6 & F7))). 
      destruct clpos. 
      * rewrite F1, F6. cbn. apply in_or_app. left. 
        rewrite makeEdgesLiteral'_iff. exists lpos, l'. firstorder.
        cbn in F4. assert (a0 = cl) by congruence. now rewrite H. 
      * cbn. apply in_or_app. right. inv kc. apply (IHcn H2).
        split; [reflexivity | exists clpos, lpos]. cbn in F3. 
        firstorder. 
  Qed. 

  (*an indirect formulation via makeEdgesLiteral*)
  Lemma makeEdges'_iff (numCn numL : nat) (cn : cnf) (cl : clause) (a b : nat) :
    (|cl|) <= 3 -> kCNF 3 cn 
    -> ((a, b) el makeEdges' cl numL cn numCn <->
       (exists k, a = numL + k /\ exists l, nth_error cl k = Some l /\ (a, b) el makeEdgesLiteral l a cn numCn)).
  Proof. 
    intros H1 H2. revert numL. induction cl.
    - intros; cbn. firstorder. destruct x; cbn in H0; congruence. 
    - intros; split.
      + cbn. intros [H|H]%in_app_or. 
        * exists 0. apply makeEdgesLiteral_iff in H as H'. split.
          -- destruct H'; lia. 
          -- exists a0. cbn. firstorder. now rewrite H0. 
          -- apply H2. 
        * apply IHcl in H. 2: cbn in H1; lia. 
          destruct H. exists (S x). firstorder. 
      + intros (k & F1 & (l & F2 & F3)). cbn. apply in_or_app. destruct k.
        * left. cbn in F2. assert (a0 = l) as H by congruence. rewrite Nat.add_0_r in F1.
          now rewrite H, F1.
        * cbn in F2. right. apply IHcl; [cbn in H1 ;lia | ].
          exists k; split; [lia | exists l]. firstorder.
  Qed. 

  Lemma makeEdges_iff (cn : cnf) (numL : nat) (a b : nat): kCNF 3 cn ->
   ((a, b) el makeEdges cn numL <-> exists clpos lpos,
      clpos < |cn| /\ lpos < 3 /\ a = numL + 3 * clpos + lpos /\
        exists cl cn1 cn2, nth_error cn clpos = Some cl /\ cn = cn1 ++ (cl :: cn2) /\ (|cn1|) = clpos /\
          (a, b) el makeEdges' cl (numL + 3 * clpos) cn2 (numL + 3 * (S clpos))).
  Proof.
    intros kc. revert numL. induction cn.
    - intros; cbn. firstorder. 
    - intros; split.
      + cbn. intros [H | H]%in_app_or.
        * apply makeEdges'_iff in H as (lpos & H').
          destruct H' as (H1 & (l & H2 & H3)). 
          exists 0, lpos. split; [lia | split ].
          -- inv kc. apply nth_error_Some_lt in H2; now rewrite H4 in H2. 
          -- split; [cbn; now rewrite Nat.add_0_r | ]. exists a0, [], cn. cbn; split; try split; try split; try reflexivity.
             apply makeEdges'_iff; [inv kc; lia | now inv kc | ].
             exists lpos; split; [lia |]. exists l; split; [firstorder | ].
             replace (numL + 3) with (S (S (S numL))) by lia. now apply H3. 
          -- inv kc; lia. 
          -- now inv kc. 
       * apply IHcn in H as (clpos & lpos & F1 & F2 & F3 & (cl & cn1 & cn2 & F4 & F5 & F6 & F7)). 
         exists (S clpos), lpos. split; [lia | split; [lia |]]. split; [lia |].
         exists cl, (a0 :: cn1), (cn2). cbn. firstorder. 
         replace (numL + S(clpos + S(clpos + S(clpos + 0)))) with (S(S(S numL)) + 3 * clpos) by lia. 
         replace (numL + S(S(clpos + S(S(clpos + S(S(clpos + 0))))))) with (S(S(S numL)) + 3 * S(clpos)) by lia. 
         now apply F7. 
         now inv kc. 
    + intros (clpos & lpos & H1 & H2 & H3 & (cl & cn1 & cn2 & H4 & H5 & H6 & H7)). 
      cbn. apply in_or_app. destruct clpos. 
      * left. rewrite Nat.mul_0_r, Nat.add_0_r in H7. rewrite Nat.add_comm in H7. cbn in H7.
        rewrite length_zero_iff_nil in H6. rewrite H6 in H5; cbn in H5; clear H6. 
        cbn in H4. assert (a0 = cl) by congruence. enough (cn = cn2). {rewrite H, H0. apply H7. }
        congruence. 
      * right. apply IHcn; [now inv kc|]. cbn in H1, H4. 
        assert (exists cn1', cn1 = a0 :: cn1') as (cn1' & ->). 
        {
          destruct cn1. cbn in H6; congruence. cbn in H5. assert (a0 = l) by congruence. 
          exists cn1. now rewrite H. 
        }
        cbn in H5. exists clpos, lpos. split; [lia | split; [lia | split; [lia|]]]. 
        exists cl, cn1', cn2. split; [assumption | split; [congruence | ]]. 
        split; [now cbn in H6 |].
        replace (S(S(S numL)) + 3 * clpos) with (numL + 3 * S clpos) by lia. 
        replace (S(S(S numL)) + 3 * S clpos) with (numL + 3 * S (S clpos)) by lia.  
        now apply H7. 
  Qed. 

  (*now the final, less abstract correctness result*)
  (*TODO: split up and restructure*)
  Lemma makeEdges_correct (cn : cnf) (a b : nat) : kCNF 3 cn ->
   ((a, b) el makeEdges cn 0 <-> a < b /\ exists l l', Some l = enumerateLiteral cn (labF a) /\ Some l' = enumerateLiteral cn (labF b) /\ enumLiteral_different_clause (labF a) (labF b) /\ not (literalsConflict l l')). 
  Proof. 
    intros H. rewrite makeEdges_iff. split. 
    + intros (clpos & lpos & H1 & H2 & H3 & (cl & cn1 & cn2 & H4 & H5 & H6 & H7)). cbn -[Nat.mul] in H7. 
      rewrite makeEdges'_iff in H7. destruct H7 as (lpos2 & F1 & (l & F2 & F3)). assert (lpos = lpos2) by lia. rewrite <- H0 in F2; clear H0 F1 lpos2. 
      rewrite makeEdgesLiteral_iff in F3. destruct F3 as (_ & (clpos' & lpos' & G1 & G2 & (cl' & l' & G3 & G4 & G5 & G6))). 
      split.
      - rewrite H3, G5; cbn. lia. 
      - cbn -[Nat.mul] in H3. rewrite H3, G5. exists l, l'. rewrite <- G4, <- F2.
        split; try split; try split. 
        * rewrite labF_proj; [|apply H2]. cbn. rewrite H4. reflexivity. 
        * replace (3 * S clpos + 3 * clpos') with (3* (S clpos + clpos')) by lia. rewrite labF_proj; [|apply G1].  
          rewrite H5. unfold enumerateLiteral. rewrite nth_error_app2; rewrite H6. 2: lia. 
          replace (S clpos + clpos' - clpos ) with (S clpos') by lia. cbn. now rewrite G3. 
        * replace (3 * S clpos + 3 * clpos') with (3* (S clpos + clpos')) by lia. repeat rewrite labF_proj. 
          unfold enumLiteral_different_clause. cbn [fst]. lia.  
          all: assumption.
        * apply G6. 
     - apply kCNF_decb_iff, kCNF_decb_correct. rewrite H5 in H. rewrite <- kCNF_decb_iff, kCNF_decb_correct in H. firstorder. 
     - rewrite H5 in H. rewrite <- kCNF_decb_iff, kCNF_decb_correct in H. destruct H as (_ & H).
       specialize (H cl). enough (|cl| = 3) by lia; symmetry. firstorder.
     - apply kCNF_decb_iff, kCNF_decb_correct. rewrite H5 in H. rewrite <- kCNF_decb_iff, kCNF_decb_correct in H. firstorder.
   + intros (H1 & (l & l' & H2 & H3 & H4 & H5)). 
     destruct (labF a) as (clpos & lpos) eqn:H6. exists clpos, lpos.
     symmetry in H2.
     destruct (enumerateLiteral_Some_inv H (ex_intro (fun x => enumerateLiteral cn (clpos, lpos) = Some x) l H2)).
     split; try split; try assumption. split; [now apply labF_inv| ].
     destruct (labF b) as (clpos' & lpos') eqn:H8. unfold enumerateLiteral in H2. destruct (nth_error cn clpos) eqn:H9. 
     -- exists l0. specialize (nth_error_In cn clpos H9) as H10; apply in_split in H10. destruct H10 as (cn1 & cn2 & H10).  
        exists cn1, cn2. firstorder.
        ++ rewrite H10 in H9. admit.
        ++ apply makeEdges'_iff. 
           ** rewrite (kCNF_clause_length H); [lia | rewrite H10; firstorder ]. 
           ** eapply kCNF_inv_app with (l1 := [l0]). eapply kCNF_inv_app.
              now rewrite H10 in H.
           ** exists lpos. cbn [Nat.add]. split; [now apply labF_inv | ].
              exists l; split; [apply H2 | ]. apply makeEdgesLiteral_iff. 
              --- eapply kCNF_inv_app with (l1 := [l0]). eapply kCNF_inv_app.
                  now rewrite H10 in H.
              --- split; [reflexivity|]. exists (clpos' - S clpos), lpos'. 
  Admitted.

  (*or in terms of edges, thus encapsulating the asymmetry of a and b*)
  Lemma makeEdges_correct' (cn : cnf) (a b : nat) : kCNF 3 cn ->
    (Lgraph_edge_in_dec' (makeEdges cn 0) a b = true <-> exists l l', Some l = enumerateLiteral cn (labF a) /\ Some l' = enumerateLiteral cn (labF b) /\ enumLiteral_different_clause (labF a) (labF b) /\ not(literalsConflict l l')).  
    intros H. rewrite Lgraph_edge_in_dec'_correct. split.
    - intros [H1%makeEdges_correct|H1%makeEdges_correct]. 2, 4: assumption.
      + firstorder. 
      + destruct H1 as (_ & (l & l' & F1 & F2 & F3 & F4)). exists l', l. firstorder. destruct l, l'. firstorder.
    - intros (l & l' & H1 & H2 & H3 & H4). destruct (lt_eq_lt_dec a b) as [[H5 | ->] | H5]. 
      + left. apply makeEdges_correct; firstorder. 
      + assert (l = l') by congruence. rewrite H0 in H4. unfold literalsConflict in H4. destruct l, l'. congruence.  
      + right. apply makeEdges_correct; [assumption| split; [assumption|]]. exists l', l. firstorder. destruct l, l'; firstorder. 
  Qed. 

End makeEdgesVerification. 
                
Lemma reduction_sat_redRel (c : cnf) : kCNF 3 c -> redRel c (reduction c). 
Proof. 
  unfold redRel. destruct (reduction c) as (g, k) eqn:H. destruct g as (n, e). 
  unfold reduction in H. inversion H. unfold redGraph in H1. intros H0.
  apply kCNF_decb_iff in H0 as H0'. rewrite H0' in H1. 
  inv H1. split; [reflexivity | split; [reflexivity |]].
  unfold redGraph. rewrite H0'. 
  split; [apply H0|].
  exists labF, labFInv. split; [apply labF_isLabelling|]. intros u v [H1 H2]. 
  cbn [Lgraph_edge_in_dec]. rewrite makeEdges_correct'. split.
  + firstorder. assert (x = l1) by congruence. assert (x0 = l2) by congruence. now rewrite H9, H10 in H6. 
  + intros (F1 & F2). destruct (enumerateLiteral c (labF u)) eqn:E1, (enumerateLiteral c (labF v)) eqn:E2. 
    1: exists p, p0; firstorder.  
    all: destruct (labF_isLabelling c). 
    2: specialize (H3 u H1); destruct (labF u). 
    1,3: specialize (H3 v H2); destruct (labF v). 
    all: destruct H3 as ((bound_1 & bound_2) & _); specialize (enumerateLiteral_Some H0 bound_1 bound_2) as (l & E3); congruence. 
  + apply H0. 
Qed.

(*extraction of the reduction function*)
Definition literalsConflictb_time (l1 l2: literal) := let (_, v1) := l1 in let (_, v2) := l2 in 17 * min v1 v2 + 40.
Instance term_literalsConflictb : computableTime' literalsConflictb (fun l1 _ => (1, fun l2 _ => (literalsConflictb_time l1 l2, tt))). 
Proof. 
  extract.
  solverec. 
Defined.

Fixpoint makeEdgesLiteral'_time (l : literal) (cl : clause) := match cl with [] => 4 | l'::cl => literalsConflictb_time l l' + 22 + makeEdgesLiteral'_time l cl end.
Instance term_makeEdgesLiteral' : computableTime' makeEdgesLiteral' (fun l _ => (5, fun lpos _ => (1, fun cl _ => (1, fun numAcc _ => (makeEdgesLiteral'_time l cl , tt))))). 
Proof.
  extract. solverec.
Defined. 

Fixpoint makeEdgesLiteral_time (l : literal) (numL : nat) (cn : cnf) (numAcc : nat) :=
    match cn with [] => 4
             | (cl::cn) => makeEdgesLiteral'_time l cl + makeEdgesLiteral_time l numL cn (3 + numAcc) + 16 * (|makeEdgesLiteral' l numL cl numAcc|) + 74
    end.
Instance term_makeEdgesLiteral : computableTime' makeEdgesLiteral (fun l _ => (5, fun numL _ => (1, fun cn _ => (1, fun numAcc _ => (makeEdgesLiteral_time l numL cn numAcc, tt))))). 
Proof.
  extract. solverec. 
Qed.

Fixpoint makeEdges'_time (c : clause) (numL : nat) (cn : cnf) (numCn : nat) :=
    match c with [] => 4
            | (l::c) => makeEdgesLiteral_time l numL cn numCn + makeEdges'_time c (S numL) cn numCn + 16 * (|makeEdgesLiteral l numL cn numCn|) + 30
    end.
Instance term_makeEdges' : computableTime' makeEdges' (fun c _ => (5, fun numL _ => (1, fun cn _ => (1, fun numCn _ => (makeEdges'_time c numL cn numCn, tt))))). 
Proof.
  extract. solverec. 
Qed. 
                                                                                                                                            
Fixpoint makeEdges_time (c : cnf) (numL : nat) :=
    match c with [] => 4
            | (cl::c) => makeEdges'_time cl numL c (3 + numL) + makeEdges_time c (3+numL) + 16 * (|makeEdges' cl numL c (3+numL)|) + 117
    end. 
Instance term_makeEdges : computableTime' makeEdges (fun c _ => (5, fun numL _ => (makeEdges_time c numL , tt))).
Proof.
  extract. solverec. 
Qed. 

Definition redGraph_time (c : cnf) := kCNF_decb_time c + 44 * (| c |) + makeEdges_time c 0 + 92.
Instance term_redGraph : computableTime' redGraph (fun c _ => (redGraph_time c, tt)). 
Proof.
  extract. unfold redGraph_time. solverec. 
Qed. 

Definition reduction_time (c : cnf) := redGraph_time c + 11 * S (|c|).
Instance term_reduction : computableTime' reduction (fun c _ => (reduction_time c, tt)).
Proof.
  extract. unfold reduction_time. solverec. 
Qed. 

From Undecidability.L.Datatypes Require Import LProd LNat. 
From Undecidability.L.Complexity Require Import PolyBounds.

(*polynomial bounds in encoding size*)
Lemma literalsConflictb_time_bound : exists (f : nat -> nat), (forall (l1 l2 : literal), literalsConflictb_time l1 l2 <= f(size(enc l1) + size(enc l2))) /\ inOPoly f /\ monotonic f. 
Proof.
  evar (f : nat -> nat). exists f. 
  split.
  - intros (s1 & v1) (s2 & v2). cbn -[Nat.mul]. repeat rewrite size_prod; cbn [fst snd]. 
    rewrite Nat.le_min_r. rewrite size_nat_enc_r with (n:=v2) at 1. 
    instantiate (f:= fun n => 17 * n). subst f. solverec. 
  - split; subst f; smpl_inO. 
Qed. 
                                                                                                         
Lemma makeEdgesLiteral'_time_bound : exists (f : nat -> nat), (forall (l : literal) (cl : clause), makeEdgesLiteral'_time l cl <= f(size(enc l) + size(enc cl))) /\ inOPoly f /\ monotonic f. 
Proof.
  assert (exists (f': nat -> nat), (forall (l l' : literal) (cl : clause), l' el cl -> literalsConflictb_time l l' + 22 <= f' (size(enc l) + size(enc cl))) /\ inOPoly f' /\ monotonic f') as (f' & H1 & H2 & H3).
  {
    destruct (literalsConflictb_time_bound) as (f' & H1 & H2 & H3).
    evar (f : nat -> nat). exists f. split.
    - intros l l' cl Hel.  
      rewrite H1. unfold monotonic in H3. rewrite H3 with (x' := size(enc l) + size(enc cl)).
      generalize (size(enc l) + size(enc cl)); intros n. [f]: intros n. subst f. cbn. reflexivity. 
      rewrite (list_el_size_bound Hel); auto. 
    - split; subst f; smpl_inO. 
  }

  evar (f : nat -> nat). exists f. 
  split.
  - intros (l1 & l2) cl . rewrite size_prod; cbn [fst snd]. 
    unfold makeEdgesLiteral'_time. instantiate (f:= fun n => 4 + f' n * n). subst f.
    induction cl.
    + nia. 
    + rewrite H1. rewrite IHcl. 2: assert (a el a ::cl) as H by (now left); apply H. 
      repeat rewrite size_prod; cbn [fst snd]. rewrite list_size_cons at 3. 
      unfold monotonic in H3. rewrite H3 with (x:= size(enc l1) + size(enc l2) + 4 + size(enc(cl)))(x' := size(enc l1) + size(enc l2) + 4 + size(enc(a :: cl))). 
      solverec. 
      rewrite list_size_cons. nia. 
  - subst f; split; smpl_inO. 
Qed. 

Lemma makeEdgesLiteral'_size (l : literal) (numL : nat) (cl : clause) (numAcc : nat) : (|makeEdgesLiteral' l numL cl numAcc|) <= (|cl|). 
Proof. revert numAcc. induction cl; cbn. intros _; lia. intros numAcc; destruct literalsConflictb; cbn; rewrite IHcl; lia. Qed. 

Lemma makeEdgesLiteral_time_bound : exists (f : nat -> nat), (forall (l : literal) (numL : nat) (cn : cnf) (numAcc : nat), makeEdgesLiteral_time l numL cn numAcc <= f(size(enc l) + size(enc cn))) /\ inOPoly f /\ monotonic f. 
Proof.
  (*first bound the running time of each step *)
  assert (exists (f' : nat -> nat), (forall (l : literal) (cl : clause) (cn : cnf) (numAcc numL : nat), cl el cn -> makeEdgesLiteral'_time l cl + 16 * (|makeEdgesLiteral' l numL cl numAcc|) + 74 <= f'(size(enc l) + size(enc cn))) /\ inOPoly f' /\ monotonic f') as (f' & H1 & H2 & H3). 
  {
    destruct (makeEdgesLiteral'_time_bound) as (f' & H1 & H2 & H3).
    evar (f : nat -> nat). exists f. split.
    - intros l cl cn numAcc numL Hel. rewrite H1. rewrite makeEdgesLiteral'_size. 
      rewrite list_size_length.
      unfold monotonic in H3. rewrite H3 with (x' := size(enc l) + size(enc cn)).
      rewrite list_el_size_bound with (l0:= cn) (a:= cl). 2: apply Hel. 
      2: rewrite list_el_size_bound with (l0:=cn)(a:= cl). 2: lia. 2 : apply Hel. 
      instantiate (f := fun n => f' n + 16 * n + 74). subst f.
      solverec.
    - subst f; split; smpl_inO. 
  }
  evar (f : nat -> nat). exists f. split.
  - intros. unfold makeEdgesLiteral_time. 
    instantiate (f:= fun n => 4 + f' n * n). subst f.
    revert numAcc. 
    induction cn. 
    + intros ; lia.
    + intros numAcc; rewrite IHcn.
      setoid_rewrite <- Nat.add_assoc. setoid_rewrite Nat.add_comm at 2.
      rewrite <- Nat.add_assoc. setoid_rewrite Nat.add_assoc at 2. 
      rewrite H1.
      2: {assert (a el a :: cn) as H4 by now left. apply H4.  }
      rewrite list_size_cons at 3. unfold monotonic in H3. rewrite H3 with (x' := size(enc l) + size(enc (a :: cn))) at 1. 
      solverec. 
      rewrite list_size_cons. solverec.
  - split; subst f; smpl_inO. 
Qed. 

(* We assume a constant that bounds the length of each clause for this bound *)
Lemma makeEdgesLiteral_size (l : literal) (numL : nat) (cn : cnf) (numCn : nat) (k : nat) :
  (forall cl, cl el cn -> (|cl|) <= k) -> (|makeEdgesLiteral l numL cn numCn|) <= k * (|cn|). 
Proof.
  intros H. induction cn in numCn ,H |-*. 
  - cbn. lia.
  - cbn. rewrite app_length. rewrite IHcn. rewrite makeEdgesLiteral'_size.
    + specialize (H a (or_introl eq_refl)). lia. 
    + firstorder. 
Qed. 

(*We now derive a constant with which we can instantiate the previous lemma *)
Lemma cnf_clause_length_bound (c : cnf) : forall cl, cl el c -> (|cl|) <= size(enc c). 
Proof. 
  intros cl H. rewrite list_size_length. now rewrite list_el_size_bound.
Qed. 


Lemma makeEdges'_time_bound : exists (f : nat -> nat), (forall (c : clause) (numL : nat) (cn : cnf) (numCn : nat), makeEdges'_time c numL cn numCn <= f(size(enc c) + size(enc cn))) /\ inOPoly f /\ monotonic f. 
Proof.
  (*again, we first bound the running time of each recursion step*)
  assert (exists (f : nat -> nat), (forall (l : literal) (numL : nat) (cn : cnf) (numCn : nat), makeEdgesLiteral_time l numL cn numCn + 16 * (|makeEdgesLiteral l numL cn numCn|) + 30 <= f(size(enc l) + size(enc cn))) /\ inOPoly f /\ monotonic f) as (f' & H1 & H2 & H3). 
  {
    destruct (makeEdgesLiteral_time_bound) as (f' & H1 & H2 & H3). 
    evar (f : nat -> nat). exists f. split.
    - intros. rewrite H1.
      rewrite makeEdgesLiteral_size. 2: apply cnf_clause_length_bound.
      rewrite list_size_length.
      instantiate (f:= fun n => f' n + 16 * n * n + 30). subst f.
      solverec. 
    - subst f; split; smpl_inO. 
  }

  evar (f : nat -> nat). exists f. split.
  - intros. unfold makeEdges'_time.
    instantiate (f := fun n => (4 + f' n * n)). subst f.
    revert numL. 
    induction c. 
    + intros; lia.
    + intros; rewrite IHc.
      setoid_rewrite Nat.add_comm at 3.
      rewrite <- Nat.add_assoc.
      rewrite <- Nat.add_assoc. 
      setoid_rewrite Nat.add_assoc at 2. 
      rewrite H1.
      unfold monotonic in H3.
      repeat setoid_rewrite H3 with (x' := size(enc (a :: c)) + size(enc cn)).
      rewrite list_size_cons at 4. solverec. 
      all: rewrite list_size_cons; solverec. 
  - subst f; split; smpl_inO. 
Qed.  

(* We bound the output size of makeEdges' *)
Lemma makeEdges'_size (c : clause) (numL : nat) (cn : cnf) (numCn : nat) (k : nat) :
  (forall c', c' el cn -> (|c'|) <= k) -> (|makeEdges' c numL cn numCn|) <= k * (|c|) * (|cn|). 
Proof.
  intros H. revert numL.
  induction c. 
  - intros; cbn. lia. 
  - intros; cbn. rewrite app_length. rewrite IHc. rewrite (makeEdgesLiteral_size). 
    2: apply H.  lia. 
Qed.  
      
Lemma makeEdges_time_bound : exists (f : nat -> nat), (forall (c: cnf) (numL : nat), makeEdges_time c numL <= f(size(enc c))) /\ inOPoly f /\ monotonic f.
Proof.
  (*and again, we first bound the running time of each step*)
  assert (exists (f' : nat -> nat), (forall (cl : clause) (numL : nat) (cn : cnf), makeEdges'_time cl numL cn (3 + numL) + 16 * (|makeEdges' cl numL cn (3+numL)|) + 117 <= f'(size(enc cl) + size(enc cn))) /\ inOPoly f' /\ monotonic f') as (f' & H1 & H2 & H3).
  {
    destruct (makeEdges'_time_bound) as (f' & H1 & H2 & H3).
    evar (f : nat -> nat). exists f. split.
    - intros. rewrite makeEdges'_size. 2: apply cnf_clause_length_bound. 
      rewrite H1. 
      instantiate (f:= fun n => 121 + 16 * n * n * n + f' n). subst f.
      solverec.
      rewrite list_size_length.
      rewrite list_size_length.
      solverec.
    - subst f; split; smpl_inO. 
  }

  evar (f : nat -> nat). exists f. split.
  - intros c numL. unfold makeEdges_time. 
    instantiate (f:= fun n => 4 + f' n * n). subst f.
    revert numL. induction c.
    + intros; lia.  
    + intros; rewrite IHc. 
      setoid_rewrite Nat.add_comm at 3.
      rewrite <- Nat.add_assoc.
      rewrite <- Nat.add_assoc. 
      setoid_rewrite Nat.add_assoc at 2. 
      rewrite H1. 
      unfold monotonic in H3. repeat setoid_rewrite H3 with (x' := size(enc (a::c))). 
      rewrite list_size_cons at 4. solverec. 
      all: rewrite list_size_cons; lia. 
  - subst f; split; smpl_inO. 
Qed. 

(* one could obtain a tighter bound (constant 1/2 * k * k instead of k * k), but this is irrelevant *)
Lemma makeEdges_size (cn : cnf) (numL : nat) (k : nat):
  kCNF k cn -> (|makeEdges cn numL|) <=  k * k * (|cn|) * (|cn|). 
Proof. 
  intros H%kCNF_decb_iff%kCNF_decb_correct. revert numL. induction cn.
  - intros; cbn. lia.
  - intros; cbn. rewrite app_length. rewrite makeEdges'_size; destruct H as (F & H). 
    2: {
      intros cl H1. specialize (H cl (@or_intror (a = cl) (cl el cn) H1) ).
      enough (|cl| <= k) by apply H0. lia.  
    }
    rewrite IHcn. 2: firstorder. now rewrite H with (cl:=a).
Qed. 

(*now, finally, we come to the desired result: the reduction runs in polynomial time*)

Lemma reduction_time_bound : exists (f : nat -> nat), (forall (c : cnf), reduction_time c <= f(size(enc c))) /\ inOPoly f /\ monotonic f. 
Proof. 
  destruct (kCNF_decb_time_bound) as (g & H1 & H2 & H3).
  destruct (makeEdges_time_bound) as (h & F1 & F2 & F3). 
  evar (f : nat -> nat). exists f. split.
  - intros c. unfold reduction_time, redGraph_time. rewrite H1. rewrite F1. 
    rewrite list_size_length. 
    generalize (size (enc c)).  [f] : intros n. subst f. intros n.
    replace (S n) with (n+1) by lia. (*makes the proof below easier, since it doesn't know that S is in inOPoly *)
    cbn -[mul]. reflexivity.
  - subst f; split; smpl_inO. 
Qed. 

(* we also need to bound the size of the entries of the makeEdges output*)
(* the bound we go for is 3 * (|cn|) + numL for the components of the list's entries*)

Lemma makeEdges_entry_size (cn : cnf) (numL : nat) : kCNF 3 cn -> forall u v, (u, v) el makeEdges cn numL ->
                                                                      u < 3 * (|cn|) + numL /\ v < 3 * (|cn|) + numL.
Proof.
  intros H u v H1. 
  rewrite (makeEdges_iff numL u v H) in H1.
  rewrite <- kCNF_decb_iff, kCNF_decb_correct  in H. destruct H as (_ & H). 
  destruct H1 as (clpos & lpos & F1 & F2 & F3 & (cl & cn1& cn2 & F4 & F5 & F6 & F7)).
  rewrite makeEdges'_iff in F7. destruct F7 as (_ & _ & l' & _ & E2 ). 
  rewrite makeEdgesLiteral_iff in E2. destruct E2 as (_ & (clpos' & lpos' & G1 & G2 & (cl'' & l'' & G3 & G4 & G5 & _))). 
  rewrite F3, G5.
  split.
  - lia. 
  - enough (S clpos + clpos' < |cn|) by lia. 
    rewrite F5. rewrite app_length. cbn. lia. 
  - apply kCNF_decb_iff, kCNF_decb_correct. split; [lia|]. rewrite F5 in H. firstorder.
  -  rewrite F5 in H. rewrite <- H. lia. firstorder. 
  - apply kCNF_decb_iff, kCNF_decb_correct. split; [lia|]. rewrite F5 in H. firstorder. 
Qed. 

Lemma tsat_to_clique  : reducesPolyMO (kSAT 3) LClique. 
Proof. 
  exists reduction. split.
  - destruct (reduction_time_bound) as (f & H1 & H2 & H3). exists f. 
    + constructor. extract. solverec. unfold reduction_time in H1.  specialize (H1 x). lia.   
    + apply H2.
    + apply H3.
    + (*the output size is polynomial*)
      evar (f' : nat -> nat). exists f'. split.
      * intros c. unfold reduction. rewrite size_prod; cbn[fst snd].
        unfold redGraph. destruct (kCNF_decb) eqn:kcdec. 
        -- apply kCNF_decb_iff in kcdec. rewrite size_prod; cbn [fst snd].  rewrite list_size_of_el. 
           2: {
             intros ( u & v) H. rewrite size_prod; cbn [fst snd].  
             specialize (makeEdges_entry_size kcdec H) as (F1 & F2). 
             enough (size(enc u) + size(enc v) + 4 <= 2 * size(enc (3 * (|c|))) + 4) by apply H0. 
             repeat rewrite size_nat_enc. lia. 
           }
           repeat rewrite (makeEdges_size 0 kcdec). solverec. repeat rewrite size_nat_enc. solverec.
           repeat rewrite list_size_length.
           generalize (size(enc c)). [f']: intros n. subst f'. intros n. cbn -[Nat.mul]. reflexivity.  
        -- rewrite size_prod; cbn [fst snd]; rewrite size_list, size_nat_enc. cbn -[Nat.mul]. rewrite size_nat_enc.
           rewrite list_size_length.
           subst f'; solverec. 
      * subst f'; split; smpl_inO. 
  - intros cn. destruct (kCNF_decb 3 cn) eqn:H. 
    + apply kCNF_decb_iff in H. apply redRel_reduces. now apply reduction_sat_redRel. 
    + unfold reduction. unfold redGraph. rewrite H. unfold kSAT. rewrite <- kCNF_decb_iff. split.
      * intros (H' & _). congruence. 
      * intros H1. destruct H1 as (cl & H1). inv H1. 
        -- symmetry in H3. apply length_zero_iff_nil in H3. rewrite H3 in H; now cbn in H.
        -- destruct node; cbn in H4; congruence. 
Qed. 
