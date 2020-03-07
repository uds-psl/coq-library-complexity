From Undecidability.L Require Import L.
From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Import LLists LLNat LProd.
From PslBase.FiniteTypes Require Import FinTypes Cardinality VectorFin.
From Undecidability.L.Complexity.Problems Require Import FlatUGraph kSAT FlatClique.
From Undecidability.L.Complexity.Reductions Require Import kSAT_to_Clique.
From Undecidability.L.Complexity.Cook Require Import FlatFinTypes Prelim.
From Undecidability.L.Complexity Require Import MorePrelim. 

Section fixSAT. 
  Variable (k : nat).
  Context (Hkgt : k > 0).
  Variable (N : cnf).
  Context (Hkcnf : kCNF k N). 

  Definition Ncl := |N|. 

  (** All (clause, literal) positions *)
  Definition allPositions := list_prod (seq 0 Ncl) (seq 0 k). 

  Proposition allPositions_sound : forall ci li, (ci, li) el allPositions -> exists l, cnfGetLiteral N ci li = Some l.
  Proof. 
    intros ci li Hel. apply in_prod_iff in Hel as (Hel1 & Hel2).
    apply in_seq in Hel1 as (_ & Hel1). apply in_seq in Hel2 as (_ & Hel2). cbn in Hel1, Hel2. 
    unfold cnfGetLiteral, cnfGetClause, clauseGetLiteral.
    specialize (proj2 (nth_error_Some _ _) Hel1) as H1.
    destruct nth_error as [C | ] eqn:H2; [ | congruence].
    cbn. 
    apply nth_error_In in H2. 
    rewrite kCNF_clause_length in Hkcnf. apply Hkcnf in H2. rewrite <- H2 in Hel2. 
    specialize (proj2 (nth_error_Some _ _) Hel2) as H3. 
    destruct nth_error; [ eauto | congruence]. 
  Qed. 

  Proposition in_allPositions_iff : forall ci li, (ci < Ncl /\ li < k) <-> (ci, li) el allPositions. 
  Proof. 
    intros ci li. unfold allPositions. rewrite in_prod_iff. rewrite !in_seq. split; lia.
  Qed. 

  Definition Vf := flatProd Ncl k. 
  Definition toVertex '(ci, li) := flatPair Ncl k ci li. 

  Definition literalsConflict_decb (l1 l2 : literal) :=  
    let (b1, v1) := l1 in
    let (b2, v2) := l2 in 
    Nat.eqb v1 v2 && negb (Bool.eqb b1 b2). 

  Fact negb_not b : negb b = true <-> not (b = true). 
  Proof. 
    rewrite negb_true_iff. destruct b; split; congruence. 
  Qed. 

  Proposition literalsConflict_decb_iff l1 l2 : literalsConflict_decb l1 l2 = true <-> literalsConflict l1 l2. 
  Proof. 
    unfold literalsConflict_decb, literalsConflict. 
    destruct l1 as (b1 & v1), l2 as (b2 & v2). 
    rewrite andb_true_iff. rewrite negb_not. rewrite Nat.eqb_eq, Bool.eqb_true_iff. tauto. 
  Qed. 
  
  Definition opt_literalsConflict_decb (o1 o2 : option literal) := 
    match o1, o2 with 
    | Some l1, Some l2 => literalsConflict_decb l1 l2
    | _,_ => false 
    end. 

  Proposition opt_literalsConflict_decb_iff o1 o2 : opt_literalsConflict_decb o1 o2 = true <-> opt_literalsConflict o1 o2. 
  Proof. 
    unfold opt_literalsConflict, opt_literalsConflict_decb. 
    destruct o1 as [l1 | ], o2 as [l2 | ]. 2-4: firstorder. 
    apply literalsConflict_decb_iff. 
  Qed. 

  Definition makeEdge '((ci1, li1), (ci2, li2)) := 
    if Nat.eqb ci1 ci2 || opt_literalsConflict_decb (cnfGetLiteral N ci1 li1) (cnfGetLiteral N ci2 li2)
        then []
        else [(toVertex (ci1, li1), toVertex (ci2, li2))]. 
  Definition makeEdges := concat (map makeEdge (list_prod allPositions allPositions)). 

  Lemma in_makeEdges_iff v1 v2: (v1, v2) el makeEdges <-> (exists ci1 li1 ci2 li2, (ci1 < Ncl /\ li1 < k) /\ (ci2 < Ncl /\ li2 < k) /\ v1 = toVertex (ci1, li1) /\ v2 = toVertex (ci2, li2) /\ ci1 <> ci2 /\ not (opt_literalsConflict (cnfGetLiteral N ci1 li1) (cnfGetLiteral N ci2 li2))). 
  Proof. 
    unfold makeEdges. rewrite in_concat_map_iff. 
    split. 
    - intros (((ci1 & li1) & (ci2 & li2)) & (H1 & H2)%in_prod_iff & H3). 
      specialize (allPositions_sound H1) as (l1 & H1').
      specialize (allPositions_sound H2) as (l2 & H2'). 
      apply in_allPositions_iff in H1. apply in_allPositions_iff in H2. 
      exists ci1, li1, ci2, li2. 
      unfold makeEdge in H3. 
      destruct Nat.eqb eqn:H4; [cbn in H3; tauto | ].
      destruct opt_literalsConflict_decb eqn:H5; [ cbn in H3; tauto | ].
      cbn in H3. destruct H3 as [H3 | []]. inv H3. 
      split; [ apply H1 | split; [ apply H2 | split; [easy | split; [easy | ]]]]. 
      rewrite <- Nat.eqb_eq, H4. rewrite <- opt_literalsConflict_decb_iff, H5. split; congruence. 
  - intros (ci1 & li1 & ci2 & li2 & H1 & H2 & -> & -> & H3 & H4). 
    exists ((ci1, li1), (ci2, li2)). split.
    + rewrite in_prod_iff, <- !in_allPositions_iff. tauto.
    + unfold makeEdge. 
      rewrite <- Nat.eqb_eq in H3. rewrite <- opt_literalsConflict_decb_iff in H4. 
      destruct Nat.eqb; [ congruence | clear H3].
      destruct opt_literalsConflict_decb; [congruence | clear H4].
      now cbn. 
  Qed. 

  Definition Gflat := (Vf, makeEdges). 

  Proposition vertices_repr : finRepr (Vcnf k N) Vf. 
  Proof. 
    finRepr_simpl. 
    - unfold finRepr. rewrite Card_Fint'. easy.
    - unfold finRepr. rewrite Card_Fint'. easy.
  Qed.

  Proposition unflattenVertex ci li: ci < Ncl -> li < k -> { Va : Fin.t Ncl & { Vb : Fin.t k & finReprEl' ci Va /\ finReprEl' li Vb /\ finReprEl' (toVertex (ci, li)) (Va, Vb)}}. 
  Proof. 
    intros H1 H2. 
    fold (ofFlatType Ncl ci) in H1. fold (ofFlatType k li) in H2. 
    rewrite <- Card_Fint in H1 at 1.
    rewrite <- Card_Fint in H2 at 1.
    apply finReprEl'_exists in H1 as (Va & H1). 
    apply finReprEl'_exists in H2 as (Vb & H2). 
    exists Va, Vb. split; [apply H1 | split; [apply H2 | ]].
    finRepr_simpl.
    - split; [now rewrite <- Card_Fint | apply H1].
    - split; [now rewrite <- Card_Fint | apply H2].
  Defined. 

  Proposition index_pair (f1 f2 : finType) n1 n2 (v1 : f1) (v2 : f2) : finRepr f1 n1 -> finRepr f2 n2 -> index (v1, v2) = flatPair n1 n2 (index v1) (index v2).
  Proof. 
    intros H1 H2. 
    assert (finReprEl (flatProd n1 n2) (flatPair n1 n2 (index v1) (index v2)) (v1, v2)) as H'.
    { finRepr_simpl.
      - split; [apply H1 | reflexivity].
      - split; [apply H2 | reflexivity].
    } 
    destruct H' as (_ & H'). apply H'.
  Qed. 

  Lemma flat_edges : @isFlatEdgesOf makeEdges Vf (@Vcnf k N) (@Ecnf k N).
  Proof. 
    split. 
    - intros v1 v2 H%in_makeEdges_iff. 
      destruct H as (ci1 & li1 & ci2 & li2 & H1 & H2 & -> & -> & H3 & H4).
      split. 
      + cbn. unfold flatPair, Vf, flatProd. nia.
      + destruct (unflattenVertex (proj1 H1) (proj2 H1)) as (Va1 & Va2 & H51 & H52 & H53). 
        destruct (unflattenVertex (proj1 H2) (proj2 H2)) as (Vb1 & Vb2 & H61 & H62 & H63).
        exists (Va1, Va2), (Vb1, Vb2).
        split; [ | split; unfold isFlatVertexOf; easy].
        unfold Ecnf. rewrite H51, H52, H61, H62. 
        split; [apply H4 | ].
        rewrite <- H51 in H3. rewrite <- H61 in H3. congruence. 
    - intros (Va1 & Va2) (Vb1 & Vb2) [H1 H2].
      apply in_makeEdges_iff. 
      exists (index Va1), (index Va2), (index Vb1), (index Vb2). 
      repeat split. 
      + specialize (index_le Va1). now rewrite Card_Fint'. 
      + specialize (index_le Va2). now rewrite Card_Fint'.
      + specialize (index_le Vb1). now rewrite Card_Fint'. 
      + specialize (index_le Vb2). now rewrite Card_Fint'.
      + unfold toVertex. apply index_pair; now rewrite <- Card_Fint'. 
      + setoid_rewrite index_pair; [reflexivity | rewrite <- Card_Fint'; reflexivity | rewrite <- Card_Fint'; reflexivity].
      + contradict H2. now apply injective_index in H2. 
      + apply H1. 
  Qed. 

  Lemma flat_graph : isFlatGraphOf Gflat (Gcnf k N).
  Proof. 
    split. 
    - apply vertices_repr.
    - apply flat_edges.
  Qed.

  Lemma SAT_implies_FlatClique : SAT N -> FlatClique (Gflat, Ncl). 
  Proof. 
    intros (a & H).
    specialize (exists_clique Hkgt Hkcnf H) as (L & [H1 H2]). 
    destruct (clique_flatten flat_graph H2) as (l & H3 & H4). 
    exists l. split. 
    - apply H3. 
    - rewrite H4, H1. easy.
  Qed. 

  Lemma FlatClique_implies_SAT : FlatClique (Gflat, Ncl) -> SAT N. 
  Proof. 
    intros (l & [H1 H2]). 
    specialize (clique_unflatten flat_graph H1) as (L & H3 & H4). 
    eapply (exists_assignment Hkgt Hkcnf). 
    split.
    2: apply H3. 
    rewrite H4, H2. easy.
  Qed. 

  Theorem SAT_equiv_FlatClique : SAT N <-> FlatClique (Gflat, Ncl). 
  Proof. 
    split; [apply SAT_implies_FlatClique | apply FlatClique_implies_SAT].
  Qed. 
End fixSAT.

Definition trivialNoInstance := ((0, []):fgraph, 1).
Proposition trivialNoInstance_isNoInstance : not (FlatClique trivialNoInstance). 
Proof. 
  intros [l [H1 H2]]. destruct H1 as (H1 & _).
  destruct l; cbn in *; [congruence | ]. unfold list_ofFlatType in H1. 
  specialize (H1 n ltac:(now left)). unfold ofFlatType in H1. lia.
Qed. 

Definition reduction (k : nat) (N : cnf) := 
  if kCNF_decb k N && Nat.ltb 0 k then (Gflat k N, Ncl N) else trivialNoInstance. 

Lemma kSAT_reduces_to_FlatClique k : forall N, kSAT k N <-> FlatClique (reduction k N). 
Proof. 
  intros N. 
  unfold reduction. destruct kCNF_decb eqn:H1. 
  - destruct k. 
    + cbn -[trivialNoInstance]. unfold kSAT. 
      split; [lia | specialize trivialNoInstance_isNoInstance; tauto].
    + cbn. split; intros. 
      * apply SAT_implies_FlatClique; [lia | apply H | apply H].
      * apply kCNF_decb_iff in H1. apply FlatClique_implies_SAT in H; [ | lia | apply H1].
        split; [lia | split; auto]. 
  - cbn -[trivialNoInstance]. split.
    + intros (_ & H3 & _). apply kCNF_decb_iff in H3. congruence. 
    + intros []%trivialNoInstance_isNoInstance. 
Qed. 

