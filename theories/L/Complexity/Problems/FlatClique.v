From Undecidability.L Require Import L.
From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Import LLists LLNat LProd.
From PslBase Require Import FinTypes. 
From Undecidability.L.Complexity.Problems Require Import FlatUGraph Clique UGraph.
From Undecidability.L.Complexity.Cook Require Import FlatFinTypes.

Definition isfClique (G : fgraph) (l : list fvertex) := 
  let (V, E) := G in
  (forall v, v el l -> isfVertex V v) /\ dupfree l /\ (forall v1 v2, v1 el l -> v2 el l -> v1 <> v2 -> (v1, v2) el E). 

Definition isfKClique (k : nat) (G : fgraph) (l : list fvertex) := isfClique G l /\ |l| = k. 

Fixpoint allPairsOfEdges_decb l E := 
  match l with 
  | [] => true
  | v1 :: l => forallb (fun v2 => fedges_edge_in_decb E (v1, v2)) l && allPairsOfEdges_decb l E
  end. 

Definition isfClique_decb (G : fgraph) l := 
  let (V, E) := G in forallb (isfVertex_decb V) l && dupfreeb Nat.eqb l && allPairsOfEdges_decb l E. 

Lemma allPairsOfEdges_decb_iff V E l: 
  fgraph_wf (V, E) -> (forall v, v el l -> isfVertex V v) -> dupfree l 
  -> allPairsOfEdges_decb l E = true <-> (forall v1 v2, v1 el l -> v2 el l -> v1 <> v2 -> (v1, v2) el E).
Proof. 
  intros H0 H Hdup. 
  induction l; cbn; [easy | ].
  split.
  - rewrite andb_true_iff. intros [H1 H2].
    rewrite forallb_forall in H1. 
    intros v1 v2 [-> | Hel1] [-> | Hel2]. 
    + easy.
    + intros _. eapply fedges_edge_in_decb_iff, H1, Hel2. 
    + intros _. destruct H0 as (H0 & _). apply H0. apply fedges_edge_in_decb_iff, H1, Hel1.  
    + intros Hneq. apply IHl; try easy. now inv Hdup.
  - intros H1. apply andb_true_iff. split. 
    + apply forallb_forall. intros v Hel. apply fedges_edge_in_decb_iff. 
      destruct (nat_eq_dec a v); [now inv Hdup | ].
      now apply H1. 
    + apply IHl. 
      * intros; now apply H. 
      * now inv Hdup.
      * intros; now apply H1. 
Qed. 

Lemma isfClique_decb_iff G l : fgraph_wf G -> isfClique_decb G l = true <-> isfClique G l. 
Proof. 
  intros H. destruct G as (V & E). unfold isfClique_decb, isfClique. 
  rewrite !andb_true_iff, forallb_forall, dupfreeb_iff. 2: symmetry; apply Nat.eqb_eq.  
  setoid_rewrite isfVertex_decb_iff.
  split. 
  - intros [[H1 H2] H3]. split; [apply H1 | split; [apply H2 | ]].
    eapply allPairsOfEdges_decb_iff; easy.
  - intros [H1 [H2 H3]]. split; [split; [apply H1 | apply H2] | ].
    now eapply allPairsOfEdges_decb_iff. 
Qed. 

Definition isfKClique_decb k G l := isfClique_decb G l && Nat.eqb (length l) k. 

Lemma isfKClique_decb_iff k G l : fgraph_wf G -> isfKClique_decb k G l = true <-> isfKClique k G l.  
Proof. 
  intros H. unfold isfKClique_decb, isfKClique. 
  rewrite andb_true_iff, (isfClique_decb_iff _ H),  Nat.eqb_eq. easy.
Qed. 

(** agreement with the non-flat definition *)
Section fixGraph. 
  Variable (UG : UGraph).
  Variable (G : fgraph).
  Context (H : isFlatGraphOf G UG). 
 
  (** We require dupfreeness as list_finReprEl' does not enforce any order or how often an element appears *)
  Lemma clique_flat_agree l (L: list (V UG)): dupfree l -> dupfree L -> list_finReprEl' l L -> isfClique G l <-> isClique L. 
  Proof. 
    destruct G as (fV & fE). destruct H as (Hv & He). inv He.
    intros Hdup1 Hdup2 [H1 H2]. unfold isfClique, isClique. split. 
    - intros (F1 & F2 & F3). split; [ | easy]. 
      intros v1 v2 Hel1 Hel2 Hneq. apply H2 in Hel1. apply H2 in Hel2. 
      assert (index v1 <> index v2) as Hneq'. 
      { intros Heq. apply Hneq. now apply injective_index in Heq. }
      specialize (F3 _ _ Hel1 Hel2 Hneq').
      apply R__edgesSound in F3 as (_ & (V1 & V2 & F3 & ->%injective_index & ->%injective_index)). 
      apply F3. 
    - intros (F1 & _ ). split; [ | split; [easy | ]]. 
      + intros v Hel. apply H1 in Hel as (v' & _ & ->).
        rewrite Hv. unfold isfVertex. apply index_le. 
      + intros v1 v2 Hel1 Hel2 Hneq. 
        apply H1 in Hel1 as (V1 & Hel1 & ->).
        apply H1 in Hel2 as (V2 & Hel2 & ->).
        apply R__edgesComplete. 
        apply F1; easy. 
  Qed. 
End fixGraph.
        
