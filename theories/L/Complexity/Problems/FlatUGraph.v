From Undecidability.L Require Import L.
From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Import LLists LLNat LProd.
From PslBase Require Import FinTypes. 
From Undecidability.L.Complexity.Problems Require Import UGraph.
From Undecidability.L.Complexity.Cook Require Import FlatFinTypes.

(** *Flat representation of an undirected graph. *)

(** We represent graphs using a number, denoting the number of nodes, and a list of edges. *)
Notation fvertex := (nat) (only parsing).
Notation fedge := ((fvertex * fvertex)%type) (only parsing).
Notation fgraph := ((nat * list fedge)%type) (only parsing).

Implicit Types (e : fedge) (E : list fedge) (G : fgraph) (V v: fvertex). 

(** We require the list of edges to be symmetric and to only mention nodes which actually exist. *)
Definition fedges_symmetric (E : list fedge) := forall V1 V2, (V1, V2) el E -> (V2, V1) el E.
Definition fedge_wf n e := match e with (V1, V2) => V1 < n /\ V2 < n end. 
Definition fedges_wf n (E : list fedge) := forall e, e el E -> fedge_wf n e. 

Definition fgraph_wf G := match G with (V, E) => fedges_symmetric E /\ fedges_wf V E end. 

Definition fedge_eqb := prod_eqb Nat.eqb Nat.eqb.
Definition fedges_edge_in_decb E e := list_in_decb fedge_eqb E e. 
Definition fgraph_edge_in_decb G e := match G with (V, E) => fedges_edge_in_decb E e end. 

Definition isfVertex (V : fvertex) (v : fvertex) := ofFlatType V v.

(** Boolean deciders for some of the above definitions*)
Definition fedges_symmetric_decb (E : list fedge) := 
  forallb (fun e => let (v1, v2) := e in fedges_edge_in_decb E (v2, v1)) E. 

Definition fedge_wf_decb n e := let (v1, v2) := e in Nat.ltb v1 n && Nat.ltb v2 n. 
Definition fedges_wf_decb n E := forallb (fedge_wf_decb n) E.

Definition fgraph_wf_decb G := let (V, E) := G in fedges_symmetric_decb E && fedges_wf_decb V E. 

Definition isfVertex_decb V v := ofFlatType_dec V v. 

Proposition fedge_eqb_spec e1 e2 : reflect (e1 = e2) (fedge_eqb e1 e2).
Proof. 
  unfold fedge_eqb. apply prod_eqb_spec; apply Nat.eqb_spec.  
Qed.

Corollary fedge_eqb_iff e1 e2 : e1 = e2 <-> fedge_eqb e1 e2 = true.
Proof.
  apply reflect_iff, fedge_eqb_spec. 
Qed. 

Proposition fedges_edge_in_decb_iff E e: fedges_edge_in_decb E e = true <-> e el E. 
Proof. 
  apply list_in_decb_iff, fedge_eqb_iff.
Qed. 

Proposition fedge_wf_decb_iff n e : fedge_wf_decb n e = true <-> fedge_wf n e. 
Proof. 
  unfold fedge_wf_decb, fedge_wf. destruct e. 
  rewrite andb_true_iff, !Nat.ltb_lt. easy.
Qed. 

Proposition fedges_symmetric_decb_iff E : fedges_symmetric_decb E = true <-> fedges_symmetric E. 
Proof. 
  unfold fedges_symmetric_decb, fedges_symmetric. 
  rewrite forallb_forall. split; intros H. 
  - intros v1 v2 H1. apply fedges_edge_in_decb_iff, (H (v1, v2)), H1. 
  - intros [v1 v2] H1. apply fedges_edge_in_decb_iff, H, H1. 
Qed. 

Proposition fedges_wf_decb_iff n E : fedges_wf_decb n E = true <-> fedges_wf n E. 
Proof. 
  unfold fedges_wf_decb, fedges_wf. rewrite forallb_forall. setoid_rewrite fedge_wf_decb_iff. easy.
Qed.

Proposition fgraph_wf_decb_iff G : fgraph_wf_decb G = true <-> fgraph_wf G. 
Proof. 
  unfold fgraph_wf_decb, fgraph_wf. 
  destruct G. rewrite andb_true_iff, fedges_symmetric_decb_iff, fedges_wf_decb_iff. 
  easy.
Qed. 

Proposition isfVertex_decb_iff V v : isfVertex_decb V v = true <-> isfVertex V v. 
Proof. 
  unfold isfVertex_decb, isfVertex. apply Nat.ltb_lt.
Qed.

(** We relate UGraph and fgraph instances in the following way *)
Definition isFlatVerticesOf V (finV : finType) := finRepr finV V.
Definition isFlatVertexOf (finV : finType) V (v : finV):= finReprEl' V v. 

Inductive isFlatEdgesOf E V (finV : finType) (finE : finV * finV -> Prop) : Prop := 
  mkIsFlatEdgesOf 
    (R__edgesSound : forall v1 v2, (v1, v2) el E -> fedge_wf V (v1, v2) /\ 
                                                    exists (V1 V2 : finV), finE (V1, V2) /\ isFlatVertexOf v1 V1 /\ isFlatVertexOf v2 V2)
    (R__edgesComplete : forall (v1 v2 : finV), finE (v1, v2) -> (index v1, index v2) el E)
    : isFlatEdgesOf E V finE.
                                                  
Definition isFlatGraphOf (g : fgraph) (UG : UGraph) := 
  let (fV, fE) := g in isFlatVerticesOf fV (V UG) /\ isFlatEdgesOf fE fV (@E UG). 
