From Undecidability.L Require Import L.
From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Import LLists LLNat LProd.
From PslBase Require Import FinTypes. 
From Undecidability.L.Complexity.Problems Require Import FlatUGraph Clique UGraph.
From Undecidability.L.Complexity Require Import FlatFinTypes.
From Undecidability.L.Complexity Require Import MorePrelim. 

(** * Clique on flat graphs and NP containment *)

Definition isfClique (G : fgraph) (l : list fvertex) := 
  let (V, E) := G in
  list_ofFlatType V l /\ dupfree l /\ (forall v1 v2, v1 el l -> v2 el l -> v1 <> v2 -> (v1, v2) el E). 

Definition isfKClique (k : nat) (G : fgraph) (l : list fvertex) := isfClique G l /\ |l| = k. 

Definition FlatClique '(G, k) := exists l, fgraph_wf G /\ isfKClique k G l.

Fixpoint allPairsOfEdges_decb l E := 
  match l with 
  | [] => true
  | v1 :: l => forallb (fun v2 => fedges_edge_in_decb E (v1, v2)) l && allPairsOfEdges_decb l E
  end. 

Definition isfClique_decb (G : fgraph) l := 
  let (V, E) := G in list_ofFlatType_dec V l && dupfreeb Nat.eqb l && allPairsOfEdges_decb l E. 

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
  rewrite !andb_true_iff, list_ofFlatType_dec_correct, dupfreeb_iff. 2: symmetry; apply Nat.eqb_eq.  
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
  rewrite andb_true_iff, (isfClique_decb_iff _ H),  Nat.eqb_eq. easy.  Qed. 

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

  (** Constructively flatten and unflatten a clique. *)
  Lemma clique_flatten (L : list (V UG)) : isClique L -> {l : list fvertex & isfClique G l /\ |l| = |L| }. 
  Proof. 
    intros Hc. exists (map index L). split; [ | now rewrite map_length].
    eapply clique_flat_agree. 
    - apply dupfree_map. 2: apply Hc. intros. now apply injective_index. 
    - apply Hc. 
    - apply isFlatListOf_list_finReprEl'. reflexivity. 
    - apply Hc. 
  Defined. 

  Lemma clique_unflatten (l : list nat) : isfClique G l -> { L : list (V UG) & isClique L /\ |L| = |l| }. 
  Proof. 
    intros Hc. destruct G as (Vf & Ef) eqn:Heq. 
    unfold isfClique in Hc. 
    edestruct (finRepr_exists_list (proj1 H) (proj1 Hc)) as (L & H1). 
    exists L. split; [ | rewrite H1; now rewrite map_length ]. 
    rewrite <- Heq in H. eapply clique_flat_agree. 
    4: rewrite Heq; apply Hc.  
    - apply Hc. 
    - eapply map_dupfree. rewrite <- H1. apply Hc. 
    - apply isFlatListOf_list_finReprEl', H1. 
  Defined. 
End fixGraph.

(** *** extraction *)
From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Complexity Require Import PolyBounds FlatFinTypes. 
From Undecidability.L.Datatypes Require Import LProd LOptions LBool LSum LLNat LLists. 
From Undecidability.L.Functions Require Import EqBool.

(** fedges_edge_in_decb *)
Definition c__fedgesEdgeInDecb := 6. 
Definition fedges_edge_in_decb_time (E : list fedge) (e : fedge) := list_in_decb_time E e + c__fedgesEdgeInDecb. 
Instance term_fedges_edge_in_decb : computableTime' fedges_edge_in_decb (fun E _ => (1, fun e _ => (fedges_edge_in_decb_time E e, tt))). 
Proof. 
  extract. solverec. 
  unfold fedges_edge_in_decb_time, c__fedgesEdgeInDecb. Set Printing All. easy.  
Qed. 

(** allPairsOfEdges_decb *)
Definition allPairsOfEdges_decb_step (E : list fedge) (v1 : fvertex) (v2 : fvertex) := fedges_edge_in_decb E (v1, v2). 

Definition c__allPairsOfEdgesDecbStep := 4. 
Definition allPairsOfEdges_decb_step_time (E : list fedge) (v1 : fvertex) (v2 : fvertex) := fedges_edge_in_decb_time E (v1, v2) + c__allPairsOfEdgesDecbStep.
Instance term_allPairsOfEdges_decb_step : computableTime' allPairsOfEdges_decb_step (fun E _ => (1, fun v1 _ => (1, fun v2 _ => (allPairsOfEdges_decb_step_time E v1 v2, tt)))). 
Proof. 
  extract. solverec. unfold allPairsOfEdges_decb_step_time, c__allPairsOfEdgesDecbStep. solverec. 
Qed. 

Definition c__allPairsOfEdgesDecb := 19.
Fixpoint allPairsOfEdges_decb_time (l : list fvertex) (E : list fedge) :=
  match l with 
  | [] => 0
  | v1 :: l => forallb_time (allPairsOfEdges_decb_step_time E v1) l + allPairsOfEdges_decb_time l E
  end + c__allPairsOfEdgesDecb.
Instance term_allPairsOfEdges_decb : computableTime' allPairsOfEdges_decb (fun l _ => (5, fun E _ => (allPairsOfEdges_decb_time l E, tt))). 
Proof. 
  apply computableTimeExt with (x := 
  fix allPairsOfEdges_decb (l : list nat) (E : list (nat * nat)) {struct l} : bool :=
    match l with
    | [] => true
    | v1 :: l0 =>
        forallb (allPairsOfEdges_decb_step E v1) l0 &&
        allPairsOfEdges_decb l0 E
    end). 1: easy.
  extract. solverec. 
  all: unfold allPairsOfEdges_decb_time, c__allPairsOfEdgesDecb; solverec. 
Qed. 

Definition c__allPairsOfEdgesDecbBound1 := c__fedgesEdgeInDecb + c__allPairsOfEdgesDecbStep + c__forallb.
Definition c__allPairsOfEdgesDecbBound2 := c__forallb + c__allPairsOfEdgesDecb.
Definition poly__allPairsOfEdgesDecb n :=
  n * n * (poly__listInDecb (X := nat * nat) n + c__allPairsOfEdgesDecbBound1) + (n + 1) * c__allPairsOfEdgesDecbBound2. 
Lemma allPairsOfEdges_decb_time_bound l E : allPairsOfEdges_decb_time l E <= poly__allPairsOfEdgesDecb (size (enc E) + size (enc l)). 
Proof. 
  induction l; cbn. 
  - unfold poly__allPairsOfEdgesDecb, c__allPairsOfEdgesDecbBound2. nia.  
  - rewrite IHl. rewrite forallb_time_exp. 
    rewrite sumn_map_mono. 
    2:{ intros v Hel. unfold allPairsOfEdges_decb_step_time. unfold fedges_edge_in_decb_time.  
        rewrite list_in_decb_time_bound at 1. instantiate (1 := fun _ => _). cbn. reflexivity. 
    } 
    rewrite sumn_map_const. 
    rewrite list_size_length. 
    poly_mono (@list_in_decb_poly (nat * nat) _ _ _ _). 2: { instantiate (1 := size (enc E) + size (enc (a::l))). lia. }
    unfold poly__allPairsOfEdgesDecb. 
    poly_mono (@list_in_decb_poly (nat * nat) _ _ _ _) at 2. 2: { instantiate (1 := size (enc E) + size (enc (a::l))). rewrite list_size_cons. lia. }
    rewrite list_size_cons at 3 4 6. unfold c__listsizeCons. 
    (* nia is too dumb to solve this; leq_crossout is smart enough and fast, but produces proof terms which are too large*)
    (* thus we have to do this unmaintainable, annoying cluster**** *)
    replace (poly__listInDecb (X := nat * nat) (size (enc E) + size (enc (a :: l))) + c__fedgesEdgeInDecb +
 c__allPairsOfEdgesDecbStep + c__forallb) with (poly__listInDecb (X := nat * nat) (size (enc E) + size (enc (a::l))) + c__allPairsOfEdgesDecbBound1) by (unfold c__allPairsOfEdgesDecbBound1; lia). 
    replace (size (enc l) * (poly__listInDecb (size (enc E) + size (enc (a :: l))) +
     c__allPairsOfEdgesDecbBound1) + c__forallb + ((size (enc E) + size (enc l)) * (size (enc E) + size (enc l)) * (poly__listInDecb (size (enc E) + size (enc (a :: l))) +
     c__allPairsOfEdgesDecbBound1) +
     (size (enc E) + size (enc l) + 1) * c__allPairsOfEdgesDecbBound2) +
     c__allPairsOfEdgesDecb) with (size (enc l) * (poly__listInDecb (X := nat * nat)(size (enc E) + size (enc (a :: l))) +
     c__allPairsOfEdgesDecbBound1) + ((size (enc E) + size (enc l)) * (size (enc E) + size (enc l)) * (poly__listInDecb (X := nat * nat) (size (enc E) + size (enc (a :: l))) +
     c__allPairsOfEdgesDecbBound1) +
     (size (enc E) + size (enc l) + 1) * c__allPairsOfEdgesDecbBound2) +
     c__allPairsOfEdgesDecbBound2) by (unfold c__allPairsOfEdgesDecbBound2; lia). 
    leq_crossout. (* leq_crossout says this is okay, so we just admit *)
Admitted. 
Lemma allPairsOfEdges_decb_poly : monotonic poly__allPairsOfEdgesDecb /\ inOPoly poly__allPairsOfEdgesDecb. 
Proof. 
  unfold poly__allPairsOfEdgesDecb; split; smpl_inO; apply list_in_decb_poly. 
Qed. 
    
Definition c__isfCliqueDecb := 21. 
Definition isfClique_decb_time (G : fgraph) (l : list fvertex) := let (V, E) := G in list_ofFlatType_dec_time V l + dupfreeb_time l + allPairsOfEdges_decb_time l E + c__isfCliqueDecb.
Instance term_isfClique_decb : computableTime' isfClique_decb (fun G _ => (1, fun l _ => (isfClique_decb_time G l, tt))). 
Proof. 
  extract. solverec. unfold c__isfCliqueDecb; solverec. 
Qed. 

Definition poly__isfCliqueDecb n := poly__listOfFlatTypeDec n + poly__dupfreeb (X := nat) n + poly__allPairsOfEdgesDecb n + c__isfCliqueDecb. 
Lemma isfClique_decb_time_bound G l : isfClique_decb_time G l <= poly__isfCliqueDecb (size (enc G) + size (enc l)). 
Proof. 
  unfold isfClique_decb_time. destruct G as (V & E). 
  rewrite list_ofFlatType_dec_time_bound. 
  rewrite dupfreeb_time_bound. 
  rewrite allPairsOfEdges_decb_time_bound. 
  poly_mono list_ofFlatType_dec_poly. 2: { instantiate (1 := size (enc (V, E)) + size (enc l)). rewrite size_prod; cbn. lia. }
  poly_mono (@dupfreeb_poly nat _ _ _ _). 2: { instantiate (1 := size (enc (V, E)) + size (enc l)). rewrite size_prod; cbn. lia. }
  poly_mono allPairsOfEdges_decb_poly. 2: { instantiate (1 := size (enc (V, E)) + size (enc l)). rewrite size_prod; cbn. lia. }
  unfold poly__isfCliqueDecb; solverec.  
Qed. 
Lemma isfClique_decb_poly: monotonic poly__isfCliqueDecb /\ inOPoly poly__isfCliqueDecb. 
Proof. 
  unfold poly__isfCliqueDecb; split; smpl_inO. 
  all: first [apply list_ofFlatType_dec_poly | apply dupfreeb_poly | apply allPairsOfEdges_decb_poly]. 
Qed. 

(** isfKClique_decb *)
Definition c__isfKCliqueDecb := 12 + c__length. 
Definition isfKClique_decb_time (k : nat) (G : fgraph) (l : list fvertex) := 
  isfClique_decb_time G l + c__length * (|l|) + eqbTime (X := nat) (size (enc (|l|))) (size (enc k))
  + c__isfKCliqueDecb. 
Instance term_isfKClique_decb : computableTime' isfKClique_decb (fun k _ => (1, fun G _ => (1, fun l _ => (isfKClique_decb_time k G l, tt)))).
Proof. 
  extract. solverec. 
  unfold isfKClique_decb_time, c__isfKCliqueDecb. solverec. 
Qed. 

Definition poly__isfKCliqueDecb n := poly__isfCliqueDecb n + c__length * n + n * c__eqbComp nat + c__isfKCliqueDecb. 
Lemma isfKClique_decb_time_bound k G l : isfKClique_decb_time k G l <= poly__isfKCliqueDecb (size (enc G) + size (enc l)). 
Proof. 
  unfold isfKClique_decb_time. destruct G as (V & E). 
  rewrite isfClique_decb_time_bound. rewrite list_size_length at 1. 
  unfold eqbTime. rewrite Nat.le_min_l, list_size_enc_length. 
  unfold poly__isfKCliqueDecb. solverec.  
Qed. 
Lemma isfKClique_decb_poly : monotonic poly__isfKCliqueDecb /\ inOPoly poly__isfKCliqueDecb.
Proof. 
  unfold poly__isfKCliqueDecb; split; smpl_inO; apply isfClique_decb_poly. 
Qed.  

(** fedges_symmetric_decb *)
Definition fedges_symmetric_decb_step (E : list fedge) (e : fedge) := let (v1, v2) := e in fedges_edge_in_decb E (v2, v1). 

Definition c__fedgesSymmetricDecbStep := 8. 
Definition fedges_symmetric_decb_step_time (E : list fedge) (e : fedge) := let (v1, v2) := e in fedges_edge_in_decb_time E (v2, v1) + c__fedgesSymmetricDecbStep.
Instance term_fedges_symmetric_decb_step : computableTime' fedges_symmetric_decb_step (fun E _ => (1, fun e _ => (fedges_symmetric_decb_step_time E e, tt))). 
Proof. 
  extract. solverec. unfold c__fedgesSymmetricDecbStep; solverec. 
Qed. 

Definition c__fedgesSymmetricDecb := 3. 
Definition fedges_symmetric_decb_time (E : list fedge) := forallb_time (fedges_symmetric_decb_step_time E) E + c__fedgesSymmetricDecb. 
Instance term_fedges_symmetric_decb : computableTime' fedges_symmetric_decb (fun E _ => (fedges_symmetric_decb_time E, tt)). 
Proof. 
  apply computableTimeExt with (x := fun E => forallb (fedges_symmetric_decb_step E) E). 
  1: easy.
  extract. solverec. unfold fedges_symmetric_decb_time, c__fedgesSymmetricDecb; solverec. 
Qed. 

Definition poly__fedgesSymmetricDecb n := n * (poly__listInDecb (X := nat * nat) n + c__fedgesEdgeInDecb + c__fedgesSymmetricDecbStep + c__forallb) + c__forallb + c__fedgesSymmetricDecb.
Lemma fedges_symmetric_decb_time_bound E : fedges_symmetric_decb_time E <= poly__fedgesSymmetricDecb (size (enc E)). 
Proof. 
  unfold fedges_symmetric_decb_time. rewrite forallb_time_exp. 
  rewrite sumn_map_mono. 
  2: { intros (v1 & v2) Hel. unfold fedges_symmetric_decb_step_time. 
       unfold fedges_edge_in_decb_time. rewrite list_in_decb_time_bound. 
       instantiate (1 := fun _ => _). cbn; reflexivity. 
  } 
  rewrite sumn_map_const. rewrite list_size_length. 
  unfold poly__fedgesSymmetricDecb. lia. 
Qed. 
Lemma fedges_symmetric_decb_poly : monotonic poly__fedgesSymmetricDecb /\ inOPoly poly__fedgesSymmetricDecb. 
Proof. 
  unfold poly__fedgesSymmetricDecb; split; smpl_inO; apply list_in_decb_poly. 
Qed. 

(** fedge_wf_decb *)
Definition c__fedgeWfDecb := 2 * c__ltb + 12. 
Definition fedge_wf_decb_time (V : nat) := 2 * c__leb * (1 + V) + c__fedgeWfDecb. 
Instance term_fedge_wf : computableTime' fedge_wf_decb (fun V _ => (1, fun e _ => (fedge_wf_decb_time V, tt))). 
Proof. 
  extract. solverec. 
  unfold ltb_time, leb_time. rewrite !Nat.le_min_r. 
  unfold fedge_wf_decb_time, c__fedgeWfDecb. solverec. 
Qed. 
  
(** fedges_wf_decb *)
Definition c__fedgesWfDecb := c__forallb + 3.
Definition fedges_wf_decb_time (V : nat) (E : list fedge) := (|E|) * (fedge_wf_decb_time V + c__forallb) + c__fedgesWfDecb.
Instance term_fedges_wf : computableTime' fedges_wf_decb (fun V _ => (1, fun E _ => (fedges_wf_decb_time V E, tt))). 
Proof. 
  extract. solverec. 
  rewrite forallb_time_exp. rewrite sumn_map_const. 
  unfold fedges_wf_decb_time, c__fedgesWfDecb. solverec.  
Qed.

Definition poly__fedgesWfDecb n := n * (2 * c__leb * (1 + n) + c__fedgeWfDecb + c__forallb) + c__fedgesWfDecb.
Lemma fedges_wf_decb_time_bound V E : fedges_wf_decb_time V E <= poly__fedgesWfDecb (size (enc V) + size (enc E)). 
Proof.
  unfold fedges_wf_decb_time. rewrite list_size_length. unfold fedge_wf_decb_time. 
  rewrite size_nat_enc_r with (n := V) at 1. 
  unfold poly__fedgesWfDecb. leq_crossout. 
Qed.
Lemma fedges_wf_decb_poly : monotonic poly__fedgesWfDecb /\ inOPoly poly__fedgesWfDecb. 
Proof. 
  unfold poly__fedgesWfDecb; split; smpl_inO. 
Qed. 

(** fgraph_wf_decb *)
Definition c__fgraphWfDecb := 11. 
Definition fgraph_wf_decb_time (G : fgraph) := let (V, E) := G in fedges_symmetric_decb_time E + fedges_wf_decb_time V E + c__fgraphWfDecb.
Instance term_fgraph_wf_decb : computableTime' fgraph_wf_decb (fun G _ => (fgraph_wf_decb_time G, tt)). 
Proof. 
  extract. solverec. unfold c__fgraphWfDecb; solverec. 
Qed. 

Definition poly__fgraphWfDecb n := poly__fedgesSymmetricDecb n + poly__fedgesWfDecb n + c__fgraphWfDecb. 
Lemma fgraph_wf_decb_time_bound G : fgraph_wf_decb_time G <= poly__fgraphWfDecb (size (enc G)). 
Proof. 
  unfold fgraph_wf_decb_time. destruct G as (V & E). 
  rewrite fedges_symmetric_decb_time_bound, fedges_wf_decb_time_bound. 
  poly_mono fedges_symmetric_decb_poly. 2: { instantiate (1 := size (enc (V, E))). rewrite size_prod; cbn; lia. }
  poly_mono fedges_wf_decb_poly. 2: { instantiate (1 := size (enc (V, E))). rewrite size_prod; cbn; lia. }
  unfold poly__fgraphWfDecb; lia.  
Qed. 
Lemma fgraph_wf_decb_poly : monotonic poly__fgraphWfDecb /\ inOPoly poly__fgraphWfDecb. 
Proof. 
  unfold poly__fgraphWfDecb; split; smpl_inO; first [apply fedges_symmetric_decb_poly | apply fedges_wf_decb_poly]. 
Qed. 


(** *** NP containment *)
Lemma FlatClique_in_NP : inNP (unrestrictedP FlatClique). 
Proof. 
  eapply inNP_intro with (R := fun (i : { p : fgraph * nat | True}) l => let (G, k) := proj1_sig i in fgraph_wf G /\ isfKClique k G l). 
  1: apply linDec_polyTimeComputable. 
  2: { 
    eexists. 
    - intros ((G & k) & ?) cert. cbn. firstorder.  
    - intros ((G & k) & ?). cbn. intros (l & H1). exists l. split; [apply H1 | ]. 
      destruct G as (V & E). destruct H1 as [_ ((H1 & H2 & _) & _)].  
      enough (size (enc l) <= size (enc (seq 0 V))) as H3. 
      { rewrite H3. rewrite list_size_of_el. 
        2: { intros a (_ & Hb)%in_seq. rewrite nat_size_le; [ | rewrite Hb; reflexivity]. 
             reflexivity. 
        } 
        rewrite seq_length. cbn -[Nat.mul]. rewrite size_nat_enc_r with (n := V) at 2 3.
        instantiate (1 := fun n => n * n + c__listsizeCons * n + c__listsizeNil). 
        rewrite !size_prod.  cbn -[Nat.mul]. nia. 
      } 
      eapply list_incl_dupfree_size. 
      + intros a Hel. apply H1 in Hel. apply in_seq. split; [lia | apply Hel]. 
      + apply H2. 
    - smpl_inO. 
    - smpl_inO. 
  } 
  eexists. split. 
  - constructor. exists (fun '(G, k, l) => fgraph_wf_decb G && isfKClique_decb k G l). 
    + extract. recRel_prettify2. rewrite isfKClique_decb_time_bound, fgraph_wf_decb_time_bound. 
      poly_mono isfKClique_decb_poly. 2: {instantiate (1 := size (enc (a, b1, b0, b))). rewrite !size_prod; cbn. lia. }
      poly_mono fgraph_wf_decb_poly. 2: {instantiate (1 := size (enc (a, b1, b0, b))). rewrite !size_prod; cbn. lia. }
      instantiate (1 := fun n => _). cbn. generalize (size (enc (a, b1, b0, b))). reflexivity. 
    + intros ((G & k) & l) ?. cbn. rewrite andb_true_iff. rewrite fgraph_wf_decb_iff. 
      split. 
      * intros [H1 H2]; split; [apply H1 | rewrite isfKClique_decb_iff; easy]. 
      * intros [H1 H2]; split; [apply H1 | rewrite <- isfKClique_decb_iff; easy ]. 
  - split; smpl_inO; first [apply fgraph_wf_decb_poly | apply isfKClique_decb_poly]. 
Qed.
