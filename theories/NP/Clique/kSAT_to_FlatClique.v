From Undecidability.L Require Import L.
From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Import Lists LNat LProd.
From Undecidability.Shared.Libs.PSL.FiniteTypes Require Import FinTypes Cardinality VectorFin.
From Complexity.NP.Clique Require Import FlatUGraph FlatClique kSAT_to_Clique.
From Complexity.NP.SAT Require Import kSAT SAT_inNP.
From Complexity.Libs.CookPrelim Require Import FlatFinTypes MorePrelim.

(** * k-SAT to FlatClique *)
(** We compute a flat graph corresponding to the graph of the k-SAT to Clique reduction and then use the correctness of that reduction to derive the correctness of the flat reduction. *)

(** ** correctness *)
Section fixSAT. 
  Variable (k : nat).
  Variable (N : cnf).
  Context (Hkcnf : kCNF k N). 

  Definition Ncl := |N|. 

  (** All (clause, literal) positions *)
  Definition allPositions := list_prod (seq 0 Ncl) (seq 0 k). 

  Proposition allPositions_sound : forall ci li, (ci, li) el allPositions -> exists l, cnfGetLiteral N ci li = Some l.
  Proof using Hkcnf. 
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
  Proof using Hkcnf. 
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
    - unfold finRepr. rewrite Fin_cardinality'. easy.
    - unfold finRepr. rewrite Fin_cardinality'. easy.
  Qed.

  Proposition unflattenVertex ci li: ci < Ncl -> li < k -> { Va : Fin.t Ncl & { Vb : Fin.t k & finReprEl' ci Va /\ finReprEl' li Vb /\ finReprEl' (toVertex (ci, li)) (Va, Vb)}}. 
  Proof. 
    intros H1 H2. 
    fold (ofFlatType Ncl ci) in H1. fold (ofFlatType k li) in H2. 
    rewrite <- Fin_cardinality in H1 at 1.
    rewrite <- Fin_cardinality in H2 at 1.
    apply finReprElP_exists in H1 as (Va & H1). 
    apply finReprElP_exists in H2 as (Vb & H2). 
    exists Va, Vb. split; [apply H1 | split; [apply H2 | ]].
    finRepr_simpl.
    - split; [now rewrite <- Fin_cardinality | apply H1].
    - split; [now rewrite <- Fin_cardinality | apply H2].
  Defined (* because informative*).

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
  Proof using Hkcnf. 
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
      + specialize (index_le Va1). now rewrite Fin_cardinality'. 
      + specialize (index_le Va2). now rewrite Fin_cardinality'.
      + specialize (index_le Vb1). now rewrite Fin_cardinality'. 
      + specialize (index_le Vb2). now rewrite Fin_cardinality'.
      + unfold toVertex. apply index_pair; now rewrite <- Fin_cardinality'. 
      + setoid_rewrite index_pair; [reflexivity | rewrite <- Fin_cardinality'; reflexivity | rewrite <- Fin_cardinality'; reflexivity].
      + contradict H2. now apply injective_index in H2. 
      + apply H1. 
  Qed. 

  Lemma flat_graph : isFlatGraphOf Gflat (Gcnf k N).
  Proof using Hkcnf. 
    split. 
    - apply vertices_repr.
    - apply flat_edges.
  Qed.


  Context (Hkgt : k > 0).
  Lemma SAT_implies_FlatClique : SAT N -> FlatClique (Gflat, Ncl). 
  Proof using Hkgt Hkcnf. 
    intros (a & H).
    specialize (exists_clique Hkgt Hkcnf H) as (L & [H1 H2]). 
    destruct (clique_flatten flat_graph H2) as (l & H3 & H4). 
    exists l. split; [ | split]. 
    - eapply isFlatGraphOf_wf, flat_graph. 
    - apply H3. 
    - rewrite H4, H1. easy.
  Qed. 

  Lemma FlatClique_implies_SAT : FlatClique (Gflat, Ncl) -> SAT N. 
  Proof using Hkgt Hkcnf. 
    intros (l & [_ [H1 H2]]). 
    specialize (clique_unflatten flat_graph H1) as (L & H3 & H4). 
    eapply (exists_assignment Hkgt Hkcnf). 
    split.
    2: apply H3. 
    rewrite H4, H2. easy.
  Qed. 

  Theorem SAT_equiv_FlatClique : SAT N <-> FlatClique (Gflat, Ncl). 
  Proof using Hkgt Hkcnf. 
    split; [apply SAT_implies_FlatClique | apply FlatClique_implies_SAT].
  Qed. 
End fixSAT.

Definition trivialNoInstance := ((0, []):fgraph, 1).
Proposition trivialNoInstance_isNoInstance : not (FlatClique trivialNoInstance). 
Proof. 
  intros [l [_ [H1 H2]]]. destruct H1 as (H1 & _).
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
      * apply SAT_implies_FlatClique; [apply H | lia | apply H].
      * apply kCNF_decb_iff in H1. apply FlatClique_implies_SAT in H; [ | apply H1| lia ].
        split; [lia | split; auto]. 
  - cbn -[trivialNoInstance]. split.
    + intros (_ & H3 & _). apply kCNF_decb_iff in H3. congruence. 
    + intros []%trivialNoInstance_isNoInstance. 
Qed. 

(** ** extraction *)
From Complexity Require Import NP Complexity.Definitions.
From Undecidability.L Require Import Tactics.LTactics Complexity.UpToCNary.
From Complexity Require Import kSAT CookPrelim.PolyBounds. 
From Undecidability.L.Datatypes Require Import LBool Lists LNat LProd LOptions. 

(** allPositions *)
Definition c__allPositions := c__length + 16.
Definition allPositions_time (k : nat) (N : cnf) := c__length * (|N|) + seq_time (|N|) + seq_time k + prodLists_time (seq 0 (|N|)) (seq 0 k) + c__allPositions. 
Instance term_allPositions : computableTime' allPositions (fun k _ => (1, fun N _ => (allPositions_time k N, tt))). 
Proof. 
  extract. solverec. 
  all: unfold allPositions_time, c__allPositions; solverec. 
Qed.

Definition poly__allPositions n := c__length * n + (n + 2) * c__seq + poly__prodLists (n^2 + c__listsizeCons * n + 2 * c__listsizeNil) + c__allPositions. 
Lemma allPositions_time_bound k N : allPositions_time k N <= poly__allPositions (size (enc N) + size (enc k)). 
Proof. 
  unfold allPositions_time. unfold seq_time. 
  rewrite list_size_length at 1 2. rewrite size_nat_enc_r with (n := k) at 1.  
  rewrite prodLists_time_bound. 
  poly_mono prodLists_poly. 
  2: { rewrite list_size_of_el.  2: { intros a (_ & H)%in_seq. rewrite nat_size_le. 
        2: instantiate (1 := (|N|)); lia. reflexivity. 
       } 
       rewrite list_size_of_el. 2: { intros a (_ & H)%in_seq. rewrite nat_size_le. 
        2: instantiate (1 := k); lia. reflexivity. 
       } 
       rewrite !seq_length. rewrite list_size_enc_length, !list_size_length. 
       rewrite size_nat_enc_r with (n := k) at 2 3.
       instantiate (1 := ((size (enc N) + size (enc k))^2 + c__listsizeCons * (size (enc N) + size (enc k)) + 2* c__listsizeNil)). cbn -[Nat.mul c__listsizeCons]. leq_crossout. 
  } 
  unfold poly__allPositions. leq_crossout.
Qed. 
Lemma allPositions_poly : monotonic poly__allPositions /\ inOPoly poly__allPositions.
Proof. 
  unfold poly__allPositions; split; smpl_inO; try apply inOPoly_comp; smpl_inO; apply prodLists_poly. 
Qed. 

(** literalsConflict_decb *)
Definition c__literalsConflictDecb := c__eqbBool + 24. 
Definition literalsConflict_decb_time (l1 l2 : literal) := 
  let (_, v1) := l1 in let (_, v2) := l2 in EqBool.eqbTime (X := nat) (size (enc v1)) (size (enc v2)) + c__literalsConflictDecb. 
Instance term_literalsConflict_decb : computableTime' literalsConflict_decb (fun l1 _ => (1, fun l2 _ => (literalsConflict_decb_time l1 l2, tt))). 
Proof. 
  extract. solverec. 
  unfold c__literalsConflictDecb. solverec. 
Qed.

(** opt_literalsConflict_decb *)
Definition c__optLiteralsConflictDecb := 10. 
Definition opt_literalsConflict_decb_time (o1 o2 : option literal) := 
  match o1, o2 with 
  | Some l1, Some l2 => literalsConflict_decb_time l1 l2 
  | _, _ => 0
  end + c__optLiteralsConflictDecb. 
Instance term_opt_literalsConflict_decb : computableTime' opt_literalsConflict_decb (fun o1 _ => (1, fun o2 _ => (opt_literalsConflict_decb_time o1 o2, tt))). 
Proof. 
  extract. solverec. 
  all: unfold opt_literalsConflict_decb_time, c__optLiteralsConflictDecb; nia. 
Qed.

Definition poly__optLiteralsConflictDecb n := n * EqBool.c__eqbComp nat + 31 + c__optLiteralsConflictDecb.
Lemma opt_literalsConflict_decb_time_bound o1 o2 : opt_literalsConflict_decb_time o1 o2 <= poly__optLiteralsConflictDecb (size (enc o1)). 
Proof. 
  unfold opt_literalsConflict_decb_time, literalsConflict_decb_time. 
  destruct o1 as [ (b1 & v1) | ], o2 as [(b2 & v2) | ]; cbn. 
  2-4: unfold poly__optLiteralsConflictDecb; solverec. 
  unfold EqBool.eqbTime. rewrite Nat.le_min_l. 
  unfold poly__optLiteralsConflictDecb. rewrite size_option, size_prod; cbn. nia.
Qed.
Lemma opt_literalsConflict_decb_poly : monotonic poly__optLiteralsConflictDecb /\ inOPoly poly__optLiteralsConflictDecb. 
Proof. 
  unfold poly__optLiteralsConflictDecb; split; smpl_inO. 
Qed.

(** toVertex *)
Definition c__toVertex := c__length + 8.
Definition toVertex_time (k : nat) (N : cnf) (p : nat *nat) := let (ci, li) := p in c__length * (|N|) + flatPair_time ci k + c__toVertex.
Instance term_toVertex : computableTime' toVertex (fun k _ => (1, fun N _ => (1, fun p _ => (toVertex_time k N p, tt)))). 
Proof. 
  unfold toVertex, Ncl. extract. solverec. 
  unfold c__toVertex; nia. 
Qed.

Definition poly__toVertex n := c__length * n + (n * n * c__mult + c__mult * (n + 1) + (n * n + 1) * c__add + c__flatPair) + c__toVertex.
Lemma toVertex_time_bound k N p : toVertex_time k N p <= poly__toVertex (size (enc N) + size (enc k) + size (enc p)). 
Proof. 
  unfold toVertex_time. destruct p as (ci & li). unfold flatPair_time, mult_time, add_time. 
  rewrite list_size_length. rewrite size_nat_enc_r with (n := ci) at 1 2 3. 
  rewrite size_nat_enc_r with (n := k) at 1 2. 
  pose (g := size (enc N) + size (enc k) + size (enc (ci, li))). 
  replace_le (size (enc N)) with g by (subst g; lia) at 1. 
  replace_le (size (enc k)) with g by (subst g; lia) at 1 2. 
  replace_le (size (enc ci)) with g by (subst g; rewrite size_prod; cbn; lia) at 1 2 3.
  fold g.  unfold poly__toVertex. nia. 
Qed. 
Lemma toVertex_poly : monotonic poly__toVertex /\ inOPoly poly__toVertex. 
Proof. 
  unfold poly__toVertex; split; smpl_inO. 
Qed.

(** cnfGetLiteral *)
Definition c__cnfGetLiteral := 15. 
Definition cnfGetLiteral_time (N : cnf) (ci li : nat) := 
  nth_error_time N ci + 
  match nth_error N ci with 
  | Some C => nth_error_time C li 
  | None => 0
  end + c__cnfGetLiteral. 
Instance term_cnfGetLiteral : computableTime' cnfGetLiteral (fun N _ => (1, fun ci _ => (1, fun li _ => (cnfGetLiteral_time N ci li, tt)))). 
Proof. 
  unfold cnfGetLiteral, optBind, cnfGetClause, clauseGetLiteral. 
  extract.
  unfold cnfGetLiteral_time, c__cnfGetLiteral; recRel_prettify2. all: nia. 
Qed.

Definition poly__cnfGetLiteral n := (n + 1) * c__ntherror * 2 + c__cnfGetLiteral.
Lemma cnfGetLiteral_time_bound N ci li : cnfGetLiteral_time N ci li <= poly__cnfGetLiteral (size (enc N)). 
Proof. 
  unfold cnfGetLiteral_time. destruct nth_error eqn:H1. 
  - rewrite !nth_error_time_bound. rewrite !Nat.le_min_l. 
    apply nth_error_In in H1. erewrite (list_el_size_bound H1).
    unfold poly__cnfGetLiteral; nia.  
  - rewrite nth_error_time_bound. rewrite Nat.le_min_l. 
    unfold poly__cnfGetLiteral; nia.  
Qed.
Lemma cnfGetLiteral_poly : monotonic poly__cnfGetLiteral /\ inOPoly poly__cnfGetLiteral. 
Proof. 
  unfold poly__cnfGetLiteral; split; smpl_inO. 
Qed. 

Lemma cnfGetLiteral_size N ci li: size (enc (cnfGetLiteral N ci li)) <= size (enc N) + 5. 
Proof. 
  unfold cnfGetLiteral. destruct cnfGetClause eqn:H1. 
  - cbn. unfold clauseGetLiteral. destruct nth_error eqn:H2. 
    + apply nth_error_In in H2. apply nth_error_In in H1. 
      rewrite size_option.
      rewrite (list_el_size_bound H2), (list_el_size_bound H1).
      solverec. 
    + rewrite size_option. lia. 
  - cbn. now rewrite size_option.
Qed.

(** makeEdge *)
Definition c__makeEdge := 43.
Definition makeEdge_time (k : nat) (N : cnf) (p : (nat * nat) * (nat * nat)) := 
  let '((ci1, li1), (ci2, li2)) := p in EqBool.eqbTime (X := nat) (size (enc ci1)) (size (enc ci2)) + cnfGetLiteral_time N ci1 li1 + cnfGetLiteral_time N ci2 li2 + opt_literalsConflict_decb_time (cnfGetLiteral N ci1 li1) (cnfGetLiteral N ci2 li2) + toVertex_time k N (ci1, li1) + toVertex_time k N (ci2, li2) + c__makeEdge.
Instance term_makeEdge : computableTime' makeEdge (fun k _ => (1, fun N _ => (1, fun p _ => (makeEdge_time k N p, tt)))). 
Proof. 
  extract. recRel_prettify2. 1-2: nia. 
  all: unfold makeEdge_time, c__makeEdge; nia. 
Qed.

Definition poly__makeEdge n :=n * EqBool.c__eqbComp nat + 2 * poly__cnfGetLiteral n + poly__optLiteralsConflictDecb (n + 5) + 2 * poly__toVertex n + c__makeEdge.
Lemma makeEdge_time_bound k N p: makeEdge_time k N p <= poly__makeEdge (size (enc k) + size (enc N) + size (enc p)). 
Proof. 
  unfold makeEdge_time. destruct p as ((ci1 & li1) & (ci2 & li2)). 
  rewrite !cnfGetLiteral_time_bound. 
  rewrite opt_literalsConflict_decb_time_bound. 
  rewrite !toVertex_time_bound. 
  pose (g := size (enc k) + size (enc N) + size (enc ((ci1, li1), (ci2, li2)))). 
  poly_mono cnfGetLiteral_poly. 2: { instantiate (1 := g). unfold g; nia. }
  poly_mono toVertex_poly. 2: { instantiate (1 := g). unfold g. rewrite !size_prod; cbn; nia. }
  poly_mono toVertex_poly at 2. 2: { instantiate (1 := g). unfold g. rewrite !size_prod; cbn; nia. }
  poly_mono opt_literalsConflict_decb_poly. 2: { rewrite cnfGetLiteral_size. instantiate (1 := g + 5). unfold g. lia. } 
  unfold EqBool.eqbTime. rewrite Nat.le_min_l. 
  fold g. replace_le (size (enc ci1)) with g by (unfold g; rewrite !size_prod; cbn; lia).  
  unfold poly__makeEdge; nia. 
Qed.
Lemma makeEdge_poly : monotonic poly__makeEdge /\ inOPoly poly__makeEdge. 
Proof. 
  unfold poly__makeEdge; split; smpl_inO; try apply inOPoly_comp; smpl_inO. 
  all: first [apply cnfGetLiteral_poly | apply opt_literalsConflict_decb_poly | apply toVertex_poly]. 
Qed. 

(** makeEdges *)
Definition c__makeEdges := 11. 
Definition makeEdges_time (k : nat) (N : cnf) := 2 * allPositions_time k N + prodLists_time (allPositions k N) (allPositions k N) + map_time (makeEdge_time k N) (list_prod (allPositions k N) (allPositions k N))+ concat_time (map (makeEdge k N) (list_prod (allPositions k N) (allPositions k N))) + c__makeEdges.
Instance term_makeEdges : computableTime' makeEdges (fun k _ => (1, fun N _ => (makeEdges_time k N, tt))). 
Proof. 
  extract. solverec. 
  unfold makeEdges_time, c__makeEdges. simp_comp_arith. nia. 
Qed. 

Definition poly__makeEdges n := 
  2 * poly__allPositions n +
  poly__prodLists (((n + 4) * (n * n) + c__listsizeCons * n * n + c__listsizeNil) * 2) +
  (n^4 * (poly__makeEdge ((n + 4) * 3) + c__map) + c__map) + (n^4 * c__concat + (n^4 + 1) * c__concat) + c__makeEdges.

Lemma makeEdges_time_bound k N: makeEdges_time k N <= poly__makeEdges (size (enc N) + size (enc k)). 
Proof. 
  unfold makeEdges_time. rewrite allPositions_time_bound. 
  rewrite prodLists_time_bound. 
  pose (g := size (enc N) + size (enc k)).
  poly_mono prodLists_poly.
  2: { unfold allPositions. rewrite list_size_of_el. 
    2: { intros (a & b) (H1 & H2)%in_prod_iff. 
      apply in_seq in H1 as (_ &H1). apply in_seq in H2 as (_&H2). rewrite size_prod. cbn in *.
      rewrite nat_size_lt; [ | unfold Ncl in H1; apply H1].
      rewrite nat_size_lt with (a := b); [ | apply H2]. rewrite list_size_enc_length. 
      reflexivity.
    }
    rewrite prod_length, !seq_length. unfold Ncl. rewrite size_nat_enc_r with (n := k) at 2 3 5 6. 
    rewrite list_size_length. 
    instantiate (1 := ((g + 4) * (g * g) + c__listsizeCons * g * g + c__listsizeNil) * 2). 
    fold g. replace_le (size (enc N)) with g by (subst g; lia). replace_le (size (enc k)) with g by (subst g; lia). nia. 
  } 
  rewrite map_time_mono. 2: { 
    intros ((ci1 & li1) & (ci2 & li2)) Hel. instantiate (1 := fun _ => _). cbn -[makeEdge_time Nat.add Nat.mul]. 
    rewrite makeEdge_time_bound.  
    poly_mono makeEdge_poly. 
    2: { apply in_prod_iff in Hel as (H1 & H2). apply in_allPositions_iff in H1 as (H1 & H1'). 
      apply in_allPositions_iff in H2 as (H2 & H2').
      rewrite !size_prod. cbn. unfold Ncl in *. 
      rewrite nat_size_lt with (a := ci1); [ | apply H1]. 
      rewrite nat_size_lt with (a := li1); [ | apply H1'].
      rewrite nat_size_lt with (a := ci2); [ | apply H2]. 
      rewrite nat_size_lt with (a := li2); [ | apply H2'].
      rewrite list_size_enc_length. instantiate (1 := (g + 4) * 3). subst g. nia.
    } 
    reflexivity. 
  } 
  rewrite map_time_const. rewrite prod_length; unfold allPositions. rewrite !prod_length, !seq_length. 
  rewrite concat_time_exp. rewrite sumn_map_mono. 
  2: { intros l (((ci1 & li1) & (ci2 &li2)) & <- & Hel)%in_map_iff. instantiate (1 := fun _ => c__concat). 
    cbn -[Nat.mul]. unfold makeEdge. destruct Nat.eqb, opt_literalsConflict_decb; cbn -[Nat.mul]; lia. 
  } 
  rewrite sumn_map_const. rewrite !map_length, !prod_length, !seq_length. 
  unfold Ncl. rewrite size_nat_enc_r with (n := k) at 2 3 4 5 6 7. 
  rewrite list_size_length at 1 2 3 4 5 6.
  fold g. 
  replace_le (size (enc N)) with g by (subst g; nia). replace_le (size (enc k)) with g by (subst g; nia).
  unfold poly__makeEdges; cbn [Nat.pow]; nia. 
Qed.
Lemma makeEdges_poly : monotonic poly__makeEdges /\ inOPoly poly__makeEdges. 
Proof. 
  unfold poly__makeEdges; split; smpl_inO; try apply inOPoly_comp; smpl_inO.
  all: first [apply allPositions_poly | apply prodLists_poly | apply makeEdge_poly].
Qed.

Lemma makeEdges_length k N : |makeEdges k N| <= k * k * (|N|) * (|N|).
Proof. 
  unfold makeEdges. rewrite length_concat, map_map. 
  rewrite sumn_map_mono. 2: { intros ((ci1 & li1) & (ci2& li2)) _ . unfold makeEdge.
    instantiate (1 := fun _ => 1). destruct Nat.eqb, opt_literalsConflict_decb; cbn; lia.  
  } 
  rewrite sumn_map_const. rewrite prod_length; unfold allPositions. rewrite !prod_length, !seq_length. 
  unfold Ncl. nia. 
Qed.

Lemma makeEdges_fedges_wf k N : kCNF k N -> fedges_wf (Vf k N) (makeEdges k N). 
Proof. 
  intros H. eapply isFlatEdgesOf_fedges_wf, flat_edges, H. 
Qed.

Lemma makeEdges_size_bound k N : kCNF k N -> size (enc (makeEdges k N)) <= (size (enc (Vf k N)) * 2 + 4) * k^2 * (|N|)^2 + c__listsizeCons * k^2 * (|N|)^2 + c__listsizeNil.
Proof. 
  intros H. rewrite list_size_of_el. 
  2: { intros (v1 & v2) Hel. eapply makeEdges_fedges_wf in Hel; [ | apply H]. 
    rewrite size_prod; cbn. destruct Hel as (H1 & H2). 
    rewrite nat_size_lt ; [ | apply H1]. rewrite nat_size_lt with (a := v2); [ | apply H2]. 
    reflexivity. 
  } 
  rewrite makeEdges_length. 
  cbn[Nat.pow]. nia. 
Qed.

(** Gflat *)
Definition c__Gflat := 4. 
Definition Gflat_time (k : nat) (N : cnf) :=c__length * (|N|) + c__length + c__mult1 + mult_time (|N|) k + makeEdges_time k N + c__Gflat. 
Instance term_Gflat : computableTime' Gflat (fun k _ => (1, fun N _ => (Gflat_time k N, tt))). 
Proof. 
  unfold Gflat, Vf.
  extract. solverec. 
  unfold Gflat_time, c__Gflat; solverec. 
Qed.

Definition poly__Gflat n := c__length * n + c__length + c__mult1 + (n * n * c__mult + c__mult * (n + 1)) + poly__makeEdges n + c__Gflat. 
Lemma Gflat_time_bound (k : nat) (N : cnf) : Gflat_time k N <= poly__Gflat (size (enc N) + size (enc k)). 
Proof. 
  unfold Gflat_time. unfold mult_time. 
  rewrite list_size_length. rewrite size_nat_enc_r with (n := k) at 1. 
  rewrite makeEdges_time_bound. 
  unfold poly__Gflat. nia. 
Qed.
Lemma Gflat_poly : monotonic poly__Gflat /\ inOPoly poly__Gflat. 
Proof. 
  unfold poly__Gflat; split; smpl_inO; apply makeEdges_poly. 
Qed. 

Fact nat_size_mul a b: size (enc (a * b)) <= size (enc a) * size (enc b). 
Proof. 
  rewrite !size_nat_enc. unfold c__natsizeS; nia. 
Qed.

Definition poly__GflatSize n := n * n + (n * n * 2 + 4) * n^4 + c__listsizeCons * n^4 + c__listsizeNil + 4.
Lemma Gflat_size_bound k N: kCNF k N -> size (enc (Gflat k N)) <= poly__GflatSize (size (enc N) + size (enc k)). 
Proof. 
  intros H. unfold Gflat. rewrite size_prod; cbn.
  rewrite makeEdges_size_bound by apply H. 
  unfold Vf. rewrite nat_size_mul. unfold Ncl. 
  rewrite list_size_length at 3 4. rewrite list_size_enc_length.  
  rewrite size_nat_enc_r with (n := k) at 3 4. 
  pose (g := size (enc N) + size (enc k)). fold g. 
  replace_le (size (enc N)) with g by (unfold g;nia). 
  replace_le (size (enc k)) with g by (unfold g;nia). 
  unfold poly__GflatSize. cbn [Nat.pow]. nia. 
Qed. 
Lemma Gflat_size_poly : monotonic poly__GflatSize /\ inOPoly poly__GflatSize. 
Proof. 
  unfold poly__GflatSize; split; smpl_inO. 
Qed.

(** reduction *)
Definition c__reduction := 14. 
Definition reduction_time (k : nat) (N : cnf) := kCNF_decb_time k N + Gflat_time k N + c__length * (|N|) + c__length + (c__leb * 2 + c__ltb) + c__reduction.
Instance term_reduction (k : nat): computableTime' (reduction k) (fun N _ => (reduction_time k N, tt)). 
Proof. 
  extract. solverec. 
  all: unfold ltb_time, leb_time; rewrite Nat.le_min_l. 
  all: unfold reduction_time, c__reduction; nia.  
Qed.

(** full reduction statement *)
(** This is the flat version of the statement, including the polynomial running time. 
The correctness statement is Lemma [kSAT_reduces_to_Clique] *) 
Lemma kSAT_to_FlatClique_poly k: kSAT k ⪯p FlatClique. 
Proof. 
  eapply reducesPolyMO_intro with (f := (reduction k)). 
  - evar (f : nat -> nat). exists f. 
    + eexists (extT (reduction k)). eapply computesTime_timeLeq; [ | apply term_reduction].
      cbn. intros N _. split; [ | easy]. unfold reduction_time. 
      rewrite kCNF_decb_time_bound, Gflat_time_bound.
      rewrite list_size_length. instantiate (f := fun n => poly__kCNFDecb (n + size (enc k)) + poly__Gflat (n + size (enc k)) + c__length * n + c__length + (c__leb * 2 + c__ltb) + c__reduction). 
      subst f; simp_comp_arith; nia.
    + subst f; smpl_inO; apply inOPoly_comp; smpl_inO; first [apply kCNF_decb_poly  | apply Gflat_poly]. 
    + subst f; smpl_inO; first [apply kCNF_decb_poly  | apply Gflat_poly]. 
    + eexists (fun n => size (enc (trivialNoInstance)) + poly__GflatSize (n + size (enc k)) + n + 4). 
      * intros N. unfold reduction. destruct kCNF_decb eqn:H1, Nat.ltb; cbn. 
        2-4: lia. 
        apply kCNF_decb_iff in H1. rewrite size_prod; cbn. 
        rewrite Gflat_size_bound by apply H1. unfold Ncl. rewrite list_size_enc_length.
        nia. 
      * smpl_inO. apply inOPoly_comp; smpl_inO; apply Gflat_size_poly.  
      * smpl_inO. apply Gflat_size_poly. 
  - apply kSAT_reduces_to_FlatClique. 
Qed.
