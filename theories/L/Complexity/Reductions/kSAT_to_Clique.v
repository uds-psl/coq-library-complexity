From Undecidability.L Require Import L.
From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Import LLists LLNat LProd.
From PslBase.FiniteTypes Require Import FinTypes Cardinality VectorFin.
From Undecidability.L.Complexity Require Import MorePrelim.
From Undecidability.L.Complexity.Problems Require Import Clique UGraph SAT kSAT.
From Undecidability.L.Complexity.Reductions Require Pigeonhole.

(** * Reduction from k-SAT to Clique *)

Implicit Types (a : assgn) (N : cnf) (C : clause) (l :literal).

Definition cnfGetClause N n := nth_error N n.
Definition clauseGetLiteral C n := nth_error C n.
Definition cnfGetLiteral N n1 n2 := 
  do C <- cnfGetClause N n1;
  clauseGetLiteral C n2.

Section fixSAT.
  Variable (k : nat). 
  Variable (Hkgt : k > 0).
  Variable (N : cnf).
  Variable (Hkcnf : kCNF k N).

  (** We start by defining the graph *)

  Definition Ncl := (|N|). 

  Definition literalsConflict l1 l2 := 
    let (b1, v1) := l1 in 
    let (b2, v2) := l2 in 
    v1 = v2 /\ b1 <> b2.

  Definition opt_literalsConflict o1 o2 := 
    match o1, o2 with 
    | Some l1, Some l2 => literalsConflict l1 l2
    | _, _ => False
    end. 

  (** The nodes are pairs (ci, li): the first component describes the clause, the second one the literal *)
  Definition Vcnf := finType_CS ((Fin.t Ncl * Fin.t k)%type).
  Implicit Type v : Vcnf. 

  Definition Ecnf (p : Vcnf * Vcnf) := 
    let (v1, v2) := p in 
    let (ci1, li1) := v1 in 
    let (ci2, li2) := v2 in
    let o1 := cnfGetLiteral N (index ci1) (index li1) in
    let o2 := cnfGetLiteral N (index ci2) (index li2) in 
    not (opt_literalsConflict o1 o2) /\ ci1 <> ci2. 

  Proposition literalsConflict_symm l1 l2 : literalsConflict l1 l2 <-> literalsConflict l2 l1. 
  Proof. 
    unfold literalsConflict. destruct l1, l2. split; intros [H1 H2]; split; congruence.
  Qed.

  Lemma Ecnf_symm v1 v2 : Ecnf (v1, v2) <-> Ecnf (v2, v1).
  Proof. 
    unfold Ecnf. destruct v1, v2. 
    unfold opt_literalsConflict. destruct cnfGetLiteral, cnfGetLiteral.
    2-4: firstorder. rewrite literalsConflict_symm. easy.
  Qed. 

  Lemma literalsConflict_dec l1 l2 : {literalsConflict l1 l2} + {~ literalsConflict l1 l2}.
  Proof. 
    unfold literalsConflict. 
    destruct l1, l2. 
    destruct (nat_eq_dec n n0).
    - destruct (bool_eq_dec b b0); tauto.
    - now right.
  Defined. 

  Lemma Ecnf_dec v1 v2 : {Ecnf (v1, v2) } + {not (Ecnf (v1, v2))}. 
  Proof. 
    unfold Ecnf. destruct v1 as (ci1 & li1), v2 as (ci2 & li2). 
    unfold opt_literalsConflict.
    destruct (eqType_dec ci1 ci2) as [He | He].
    - destruct cnfGetLiteral; [ | now right].
      destruct cnfGetLiteral; [ | now right].
      destruct (literalsConflict_dec p p0); tauto. 
    - destruct cnfGetLiteral; [ | now left].
      destruct cnfGetLiteral; [ | now left].
      destruct (literalsConflict_dec p p0); tauto.
  Defined.

  Definition Gcnf := Build_UGraph Ecnf_dec Ecnf_symm.

  (** we show the correctness of the encoding *) 

  Section SAT_implies_Clique.
    (** ** SAT implies Clique *)
    (** Assume that there is a satisfying assignment for the CNF. *)
    Variable (a__sat : assgn).
    Context (H_sat : evalCnf a__sat N = true). 

    Lemma evalLiteral_true_no_conflict a l1 l2 : evalLiteral a l1 = true -> evalLiteral a l2 = true -> not (literalsConflict l1 l2).
    Proof using. 
      clear k N a__sat Hkgt Hkcnf H_sat. 
      intros H1 H2 H. unfold literalsConflict in H. 
      destruct l1, l2. destruct H as [<- H]. 
      unfold evalLiteral in *. 
      rewrite Bool.eqb_true_iff in H1, H2. 
      congruence.
    Qed. 

    Definition verticesClauseGe (L : list (V Gcnf)) (i : nat) := forall ci li, (ci, li) el L -> index ci >= i.

    Proposition Vcnf_inhabitated : |N| > 0 -> exists (v : Vcnf), True.
    Proof. 
      clear H_sat.
      unfold Vcnf, Ncl.
      intros H1. destruct k, N; cbn in *; try lia.
      exists (@Fin.F1 (|l0|), @Fin.F1 n). easy.
    Qed.

    Lemma nth_index (t : finType) (def : t) i: i < (Cardinality t) -> index (nth i (elem t) def) = i.
    Proof. 
      intros H. 
      unfold index. apply getPosition_nth. 
      - apply Cardinality.dupfree_elements.
      - apply H.
    Qed.
  
    (*we fix the index of the clause: the same clause might appear twice, but for the proof, we really need to work on a particular clause given by an index *)
    Lemma literalInClause_exists_vertex l C i: 
      l el C -> cnfGetClause N i = Some C -> exists (v : V Gcnf), 
      let (ci, li) := v in index ci = i /\ clauseGetLiteral C (index li) = Some l.
    Proof.
      clear H_sat.
      intros H1 H2. 
      destruct Vcnf_inhabitated as ((cdef & ldef) & _).
      1: { unfold cnfGetClause in H2. apply nth_error_In in H2. destruct N; cbn in *; [destruct H2 | lia]. }
      specialize (In_nth_error _ _ H1) as (j & H1').
      unfold Gcnf, Vcnf. cbn [V]. 
      exists (nth i (elem (finType_CS (Fin.t Ncl))) cdef, nth j (elem (finType_CS (Fin.t k))) ldef).
      split. 
      - apply nth_index. rewrite Card_Fint. unfold Ncl. eapply nth_error_Some_lt, H2. 
      - unfold clauseGetLiteral. rewrite nth_index; [apply H1' | ]. 
        rewrite Card_Fint. apply nth_error_Some_lt in H1'. 
        rewrite kCNF_clause_length in Hkcnf.
        unfold cnfGetClause in H2. apply nth_error_In in H2. 
        apply Hkcnf in H2. lia.
    Qed.
      
    Definition vertexSatisfied a (v : V (Gcnf)) := let (ci, li) := v in 
      match cnfGetLiteral N (index ci) (index li) with 
      | Some l => evalLiteral a__sat l = true
      | None => False
      end.  

    Lemma vertexSatisfied_edge a ci ci' li li' : ci <> ci' -> vertexSatisfied a (ci, li) -> vertexSatisfied a (ci', li') -> E (((ci, li), (ci', li')) : (V Gcnf * V Gcnf)).
    Proof. 
      intros H. unfold vertexSatisfied.
      unfold E. cbn. 
      destruct cnfGetLiteral, cnfGetLiteral; try tauto.
      intros H1 H2. unfold opt_literalsConflict. split; [now eapply evalLiteral_true_no_conflict | apply H].
    Qed. 

    Hint Constructors dupfree.
    Lemma exists_clique' N' i : (exists N'', N = N'' ++ N') -> |N'| + i = |N| -> 
        exists L, isKClique (|N'|) L /\ verticesClauseGe L i /\ (forall v, v el L -> vertexSatisfied a__sat v).
    Proof. 
      revert i. induction N'; cbn; intros. 
      - exists []. unfold isKClique, verticesClauseGe. cbn. split; [split; [lia | ] | split; [intros ? _ [] | tauto]].
        unfold isClique. split; [ intros ? ? [] | eauto].
      - rename a into C. destruct H as (N'' & H). 
        edestruct (IHN' (S i)) as (L & IH1 & IH2 & IH3).
        2: lia.
        1: { exists (N'' ++ [C]). rewrite H. rewrite <- app_assoc. now cbn. }
        clear IHN'. 
        rewrite H in H_sat. apply evalCnf_app_iff in H_sat as (_ & H_sat).
        apply evalCnf_step_inv in H_sat as (b1 & b2 & H1 & H2 & H3).
        symmetry in H3; apply andb_true_iff in H3 as [-> ->].
        apply evalClause_literal_iff in H2 as (l & Hel & H2). 
        edestruct (@literalInClause_exists_vertex l C (|N''|)) as (v & Hv). 
        + apply Hel.
        + rewrite H. unfold cnfGetClause. rewrite nth_error_app2; [ | lia]. 
          rewrite Nat.sub_diag. cbn. easy. 
        + exists (v :: L). destruct v as (ci & li). destruct Hv as [Hv1 Hv2].
          assert (vertexSatisfied a__sat (ci, li)) as H_sat.
          { unfold vertexSatisfied. unfold cnfGetLiteral. 
            rewrite Hv1, H. unfold cnfGetClause. rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. 
            cbn -[clauseGetLiteral index]. rewrite Hv2. apply H2.
          } 
          split; [ | split].
          * apply indKClique_iff. constructor. 
            -- apply indKClique_iff, IH1.  
            -- unfold verticesClauseGe in IH2. intros H3%IH2. rewrite H, app_length in H0. cbn in H0. lia. 
            -- intros (ci' & li') Hv'. specialize (IH3 _ Hv'). apply IH2 in Hv'. 
               eapply vertexSatisfied_edge; [ rewrite H, app_length in H0; cbn in H0; intros ->; lia | apply H_sat | apply IH3]. 
          * unfold verticesClauseGe. intros ci' li' [[=] | HL]; [ | specialize (IH2 _ _ HL); lia].
            subst ci'. subst li'. rewrite Hv1. rewrite H, app_length in H0. cbn in H0. lia.
          * intros v [<- | Hsat]; [ apply H_sat | now apply IH3].
    Qed.

    Lemma exists_clique: exists (L : list (V Gcnf)), isKClique Ncl L.
    Proof. 
      specialize (@exists_clique' N 0 ltac:(exists []; firstorder) ltac:(lia)) as (L & H & _). 
      unfold Ncl. exists L; apply H.
    Qed.
  End SAT_implies_Clique. 

  Section Clique_implies_SAT.
    (** ** Clique implies SAT *)
    (** Assume that the graph has a clique *)
    Variable (L : list (V Gcnf)). 
    Context (Hclique : isKClique Ncl L). 
    
    (** The proof proceeds in four steps:
        - We show that there exists a vertex of the clique for every clause of the CNF, using the pigeonhole principle.
        - Thus, there exists a list of (clause, literal) indices such that there is contained exactly one position per clause and the referenced literals are non-conflicting.
        - Resolving this list of indices, there exists a list of literals (one for every clause) which is non-conflicting. Every assignment satisfying this list of literals also satisfies the whole CNF.
        - From this list of literals, a satisfying assignment can be derived. 
      *)

    (** *** Step 1*)

    (** proof by contradiction for decidable predicates *)
    Fact contradiction_dec_bipredicate (X Y : Type) (p : X -> Y -> Prop) : (forall x y, dec (p x y)) -> forall x y, (~ (~ p x y)) -> p x y. 
    Proof. 
      intros Hdec x y Hdn. destruct (Hdec x y); tauto.
    Qed.

    Definition clausesOf (L : list (V Gcnf)) := map (fun '(ci, li) => ci) L. 
    Lemma isClique_clausesOf_dupfree cl : isClique cl -> dupfree (clausesOf cl).
    Proof. 
      intros [H1 H2]. induction cl; cbn; [constructor | ].
      destruct a as (ci & li). constructor.
      - rewrite in_map_iff. intros ((ci' & li') & -> & H3).
        destruct (eqType_dec li li') as [He | He]. 
        + subst. inv H2. auto.
        + specialize (H1 (ci, li) (ci, li') ltac:(now left) ltac:(now right) ltac:(congruence)). 
          unfold E in H1. cbn in H1. destruct H1 as (_ & H1). congruence.
      - apply IHcl; [ | now inv H2]. intros; now apply H1. 
    Qed. 

    Fact lt_le_rew (a b c : nat) : a < b -> b <= c -> a < c. 
    Proof. lia. Qed.

    Definition ofClause (v : V Gcnf) i := match v with (ci, li) => index ci = i end.  
    Lemma clique_vertex_for_all_clauses : forall i, i < Ncl -> exists v, v el L /\ ofClause v i.
    Proof. 
      intros i Hi. eapply contradiction_dec_bipredicate with (p := fun i L => exists v : Vcnf, v el L /\ ofClause v i).
      1: { clear i L Hclique Hi. intros i L. 
           induction L. 
           - right. intros (v & [] & _).
           - destruct IHl as [IH | IH].
             + left. destruct IH as (v & H1 & H2). now exists v.  
             + destruct a as (ci & li). unfold ofClause. 
               destruct (nat_eq_dec (index ci) i) as [H1 | H1]. 
               * left. exists (ci, li). eauto.
               * right. intros (v & [<- | H2] & H3); [congruence | apply IH; eauto].
      } 
      intros H. assert (forall v, v el L -> not (ofClause v i)) as H0.
      { intros v Hel Hc. apply H; eauto. } 
      clear H. 
      enough (not (dupfree (clausesOf L))) as H. 
      { destruct Hclique as (_ & H1). now apply isClique_clausesOf_dupfree in H1. }
      eapply Pigeonhole.pigeonhole'; [easy | | ].
      - instantiate (1 := remove (@eqType_dec (EqType (Fin.t Ncl))) (nth i (elem (finType_CS (Fin.t Ncl))) (Fin.of_nat_lt Hi)) (elem (finType_CS (Fin.t Ncl)))). 
        intros ci Hel. apply in_remove_iff.
        split; [apply elem_spec | ].
        unfold clausesOf in Hel. apply in_map_iff in Hel as ((ci' & li) & -> & Hel).
        apply H0 in Hel. unfold ofClause in Hel.
        specialize (H0 (ci, Fin.of_nat_lt Hkgt)). intros Heq; apply Hel.
        rewrite Heq. rewrite nth_index; [easy | rewrite Card_Fint; apply Hi].  
      - unfold clausesOf. eapply lt_le_rew. 
        + apply remove_length_el. apply elem_spec. 
        + rewrite map_length. destruct Hclique as (H1 & _).
          setoid_rewrite H1.
          specialize (Card_Fint Ncl). unfold Cardinality. intros Heq. setoid_rewrite Heq. lia.
    Qed.


    (** *** Step 2 *)
    (** We map to a list of (clause, literal) positions *)
    Definition toPos (L : list (V Gcnf)) := map (fun '(ci, li) => (index ci, index li)) L. 
    
    Definition satPositions := toPos L.

    Lemma satPositions_dupfree : dupfree satPositions. 
    Proof. 
      unfold satPositions, toPos. 
      apply dupfree_map. 2: apply Hclique.
      intros (ci1 & li1) (ci2 & li2) _ _ [=]. 
      apply injective_index in H0. apply injective_index in H1. congruence. 
    Qed. 

    Lemma satPositions_for_all_clauses : forall i, i < Ncl -> exists li, (i, li) el satPositions. 
    Proof. 
      intros i (v & H1 & H2)%clique_vertex_for_all_clauses. 
      destruct v as (ci & li).
      exists (index li). unfold toPos. apply in_map_iff.  
      exists (ci, li). unfold ofClause in H2. rewrite <- H2.  easy.
    Qed. 

    Fact Card_Fint' n : |elem (finType_CS (Fin.t n))| = n.
    Proof. specialize (Card_Fint n). now unfold Cardinality. Qed. 
      
    Lemma satPositions_non_conflicting ci1 ci2 li1 li2 : 
      (ci1, li1) el satPositions 
      -> (ci2, li2) el satPositions 
      -> (ci1, li1) <> (ci2, li2) 
      -> exists l1 l2, cnfGetLiteral N ci1 li1 = Some l1 
          /\ cnfGetLiteral N ci2 li2 = Some l2 /\ not (literalsConflict l1 l2). 
    Proof. 
      intros H1 H2 Hneq. unfold satPositions, toPos in *. 
      apply in_map_iff in H1 as ((Ci1 & Li1) & H1' & H1). inv H1'.
      apply in_map_iff in H2 as ((Ci2 & Li2) & H2' & H2). inv H2'. 
      unfold cnfGetLiteral, cnfGetClause, clauseGetLiteral. 

      specialize (index_le Ci1) as H3. rewrite Card_Fint' in H3. 
      apply (proj2 (nth_error_Some N (index Ci1))) in H3.
      destruct (nth_error N (index Ci1)) as [ C1 | ] eqn:H3'; [clear H3 | congruence].
      specialize (nth_error_In _ _ H3') as H5'.

      specialize (index_le Ci2) as H4. rewrite Card_Fint' in H4. 
      apply (proj2 (nth_error_Some N (index Ci2))) in H4. 
      destruct (nth_error N (index Ci2)) as [ C2 | ] eqn:H4'; [clear H4 | congruence].
      specialize (nth_error_In _ _ H4') as H6'.

      cbn -[index]. rewrite kCNF_clause_length in Hkcnf. 
      apply Hkcnf in H5'. apply Hkcnf in H6'. 

      specialize (index_le Li1) as H5. rewrite Card_Fint', <- H5' in H5. clear H5'.
      apply (proj2 (nth_error_Some C1 (index Li1))) in H5. 
      destruct (nth_error C1 (index Li1)) as [l1 | ] eqn:H5'; [clear H5 | congruence].

      specialize (index_le Li2) as H6. rewrite Card_Fint', <- H6' in H6. clear H6'.
      apply (proj2 (nth_error_Some C2 (index Li2))) in H6. 
      destruct (nth_error C2 (index Li2)) as [l2 | ] eqn:H6'; [clear H6 | congruence].
      
      exists l1, l2; split; [easy | split; [easy | ]]. 
      unfold isKClique in Hclique. destruct Hclique as (_ & (H & _)). 
      specialize (H _ _ H1 H2 ltac:(congruence)).

      unfold E in H. cbn -[index] in H. 
      unfold cnfGetLiteral, cnfGetClause, clauseGetLiteral in H. 
      rewrite H3', H4' in H. cbn -[index] in H. rewrite H5', H6' in H. 
      cbn in H. apply H. 
    Qed. 

    Proposition satPositions_valid ci li : (ci, li) el satPositions -> exists l, cnfGetLiteral N ci li = Some l. 
    Proof. 
      unfold satPositions, toPos. intros ((Ci & Li) & H1' & H1)%in_map_iff. inv H1'.
      unfold cnfGetLiteral, cnfGetClause, clauseGetLiteral. 

      specialize (index_le Ci) as H2. rewrite Card_Fint' in H2. 
      apply (proj2 (nth_error_Some N (index Ci))) in H2.
      destruct (nth_error N (index Ci)) as [ C | ] eqn:H2'; [clear H2 | congruence].
      apply nth_error_In in H2'.

      cbn -[index]. rewrite kCNF_clause_length in Hkcnf. 
      apply Hkcnf in H2'.
      specialize (index_le Li) as H3. rewrite Card_Fint', <- H2' in H3. clear H2'.
      apply (proj2 (nth_error_Some C (index Li))) in H3. 
      destruct (nth_error C (index Li)) as [l | ]; [clear H3 | congruence].
      eauto.
    Qed.

    (** ** Step 3: map to literals *)
    Definition toLiterals (L : list (nat * nat)) := filterSome (map (fun '(ci, li) => cnfGetLiteral N ci li) L). 

    Definition satLiterals := toLiterals satPositions. 

    Lemma satLiterals_for_all_clauses : forall C, C el N -> exists l, l el C /\ l el satLiterals.
    Proof. 
      intros C Hel. apply In_nth_error in Hel as (i & Hel). 
      specialize (nth_error_Some_lt Hel) as Hel'.
      specialize (satPositions_for_all_clauses Hel') as (li & H1). 
      specialize (satPositions_valid H1) as (l & H2).   
      exists l. split.
      - unfold cnfGetLiteral, cnfGetClause, clauseGetLiteral in H2. 
        rewrite Hel in H2. cbn in H2. now eapply nth_error_In. 
      - unfold satLiterals, toLiterals. apply in_filterSome_iff, in_map_iff.
        exists (i, li). easy.
    Qed. 

    Lemma satLiterals_sat a : (forall l, l el satLiterals -> evalLiteral a l = true) -> evalCnf a N = true. 
    Proof. 
      intros H. apply evalCnf_clause_iff. setoid_rewrite evalClause_literal_iff. 
      intros C (l & Hl & Hsat)%satLiterals_for_all_clauses.  
      exists l. split; [apply Hl | ]. 
      now apply H. 
    Qed. 

    Lemma satLiterals_not_conflicting : forall l1 l2, l1 el satLiterals -> l2 el satLiterals -> not(literalsConflict l1 l2).
    Proof. 
      intros l1 l2 Hel1 Hel2. 
      unfold satLiterals, toLiterals in *. 
      apply in_filterSome_iff, in_map_iff in Hel1 as ((ci1 & li1) & Hel1' & Hel1). 
      apply in_filterSome_iff, in_map_iff in Hel2 as ((ci2 & li2) & Hel2' & Hel2). 
      destruct (eqType_dec (ci1, li1) (ci2, li2)) as [ | Hneq]. 
      - inv e. rewrite Hel1' in Hel2'. inv Hel2'. unfold literalsConflict. 
        destruct l2. easy.
      - specialize (satPositions_non_conflicting Hel1 Hel2 Hneq) as (l1' & l2' & H1 & H2 & H3). 
        rewrite H1 in Hel1'. inv Hel1'. rewrite H2 in Hel2'. inv Hel2'. 
        apply H3. 
    Qed. 

    (** *** Step 4: map to a satisfying assignment *)
    Fixpoint toAssignment (L : list literal) := 
      match L with 
      | [] => []
      | (true, v) :: L => v :: toAssignment L
      | (false, v) :: L => toAssignment L
      end. 

    Lemma in_toAssignment_iff (v : var) lits : v el toAssignment lits <-> (true, v) el lits. 
    Proof. 
      induction lits; cbn; [tauto | ]. 
      destruct a as (b & v'). destruct b. 
      - split; [intros [-> | H1]; [now left | right; now apply IHlits] 
              | intros [[=->] | H1]; [now left | right; now apply IHlits]]. 
      - rewrite IHlits. split; [intros H; now right | intros [[=] | H]; apply H]. 
    Qed. 

    Definition satAssgn := toAssignment satLiterals.

    Lemma satAssgn_sat_literals : forall l, l el satLiterals -> evalLiteral satAssgn l = true. 
    Proof. 
      intros l Hel. destruct l as (b & v). apply evalLiteral_var_iff. 
      destruct b. 
      - apply evalVar_in_iff. apply in_toAssignment_iff, Hel. 
      - destruct evalVar eqn:H1; [ | easy]. 
        apply evalVar_in_iff, in_toAssignment_iff in H1. 
        exfalso; eapply satLiterals_not_conflicting; [apply Hel | apply H1 | ].
        unfold literalsConflict. split; congruence. 
    Qed. 

    Lemma satAssgn_sat_cnf : satisfies satAssgn N. 
    Proof. 
      unfold satisfies. 
      apply satLiterals_sat, satAssgn_sat_literals.  
    Qed. 

    Corollary exists_assignment : exists a, satisfies a N. 
    Proof. 
      exists satAssgn; apply satAssgn_sat_cnf. 
    Qed. 

  End Clique_implies_SAT. 

  Corollary reduction_to_Clique : kSAT k N <-> Clique (Gcnf, Ncl).
  Proof. 
    split.
    - intros (_ & _ & (a & H)). eapply exists_clique, H. 
    - intros (L & H). split; [ | split]. 
      + apply Hkgt. 
      + apply Hkcnf. 
      + eapply exists_assignment, H.
  Qed. 
End fixSAT. 

Lemma trivialNoInstance : {p : UGraph * nat & not (Clique p)}.
Proof. 
  exists (@Build_UGraph (finType_CS (Fin.t 0)) (fun _ => False) ltac:(intros; now right) ltac:(intros; tauto), 1). 
  intros (L & H). cbn in L. destruct H. destruct L as [ | e]; cbn in *; [congruence | ].
  inv e.
Qed. 

Definition reduction (k : nat) (N : cnf) := 
  if kCNF_decb k N && Nat.ltb 0 k then (Gcnf k N, Ncl N) else projT1 trivialNoInstance. 

Theorem kSAT_reduces_to_Clique k: forall N, kSAT k N <-> Clique (reduction k N). 
Proof. 
  intros N. unfold reduction. destruct kCNF_decb eqn:H1.
  - destruct k; cbn. 
    + unfold kSAT. specialize (projT2 trivialNoInstance) as H2. cbn in H2. split; [lia | tauto].
    + rewrite reduction_to_Clique; [easy | lia | apply kCNF_decb_iff, H1]. 
  - cbn. unfold kSAT. 
    assert (not (kCNF_decb k N = true)) as H1'. { destruct kCNF_decb; firstorder. }
    rewrite kCNF_decb_iff in H1'.
    specialize (projT2 trivialNoInstance) as H2. cbn in H2. 
    split; tauto.
Qed. 
