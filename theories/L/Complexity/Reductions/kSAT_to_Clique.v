From Undecidability.L Require Import L.
From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Import LLists LLNat LProd.
From PslBase.FiniteTypes Require Import FinTypes Cardinality VectorFin.
From Undecidability.L.Complexity.Problems Require Import newClique UGraph.
From Undecidability.L.Complexity.Cook Require Import SAT kSAT Prelim.
From Undecidability.L.Complexity.Reductions Require Pigeonhole.

(** More preliminaries *)
Section remove.
  Variable (X : Type).
  Context (eqdec : (forall x y: X, dec (x = y))).
  Lemma in_remove_iff (l : list X) (a b : X) : a el remove eqdec b l <-> a el l /\ a <> b.
  Proof.
    revert a. induction l; intros; cbn.
    - tauto. 
    - destruct (eqdec b a).
      + split; [firstorder | ].
        intros [[-> | H1] H2]; [congruence|]. now apply IHl. 
      + split; [firstorder; congruence | firstorder].
  Qed. 

  Lemma remove_length (l : list X) (a : X) : |remove eqdec a l| <= |l|.
  Proof.
    induction l; cbn.
    - lia.
    - destruct eqdec; cbn; lia. 
  Qed. 

  Lemma remove_length_el (l : list X) (a : X) : a el l -> |remove eqdec a l| < |l|.
  Proof.
    induction l.
    - intros [].
    - intros [-> | H1].
      + cbn. destruct (eqdec a a); [specialize (remove_length l a); lia | congruence].
      + cbn. destruct (eqdec a a0); [specialize (remove_length l a); lia | cbn; firstorder ].  
  Qed. 
End remove.


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

  (* the first component describes the literal, the second one the clause *)
  Definition Vcnf := (Fin.t Ncl * Fin.t k)%type.
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

    Definition literalInClause l C := l el C.
    Definition literalInCnf l N := exists C, C el N /\ literalInClause l C. 

    Proposition Vcnf_inhabitated : |N| > 0 -> exists (v : Vcnf), True.
    Proof. 
      clear H_sat.
      Print Fin.t.
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
      literalInClause l C -> cnfGetClause N i = Some C -> exists (v : V Gcnf), 
      let (ci, li) := v in index ci = i /\ clauseGetLiteral C (index li) = Some l.
    Proof.
      clear H_sat.
      intros H1 H2. 
      destruct Vcnf_inhabitated as ((cdef & ldef) & _).
      1: { unfold cnfGetClause in H2. apply nth_error_In in H2. destruct N; cbn in *; [destruct H2 | lia]. }
      unfold literalInClause in H1. 
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
        + unfold literalInClause. apply Hel.
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
    (** Assume that the graph has a clique *)
    Variable (L : list (V Gcnf)). 
    Context (Hclique : isKClique Ncl L). 
    
    (** The proof proceeds in three parts:
        - We show that there exists a vertex of the clique for every clause of the CNF, using the pigeonhole principle.
        - Thus, there exists a list of literals (one for every clause) which is non-contradictory.
        - From this list of literals, a satisfying assignment can be derived. 
      *)

    (** * Step 1*)

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
      enough (Pigeonhole.rep (clausesOf L)) as H. 
      { apply Pigeonhole.not_dupfree_rep in H; [ | easy]. 
        destruct Hclique as (_ & H1). now apply isClique_clausesOf_dupfree in H1. 
      }
      eapply Pigeonhole.pigeonhole; [easy | | ].
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


    (** Step 2 *)

