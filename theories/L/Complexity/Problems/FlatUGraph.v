From Undecidability.L Require Import L.
From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Import LLists LLNat LProd.
From PslBase Require Import FinTypes. 
From Undecidability.L.Complexity.Problems Require Import UGraph.

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
Definition ledges_edge_in_decb E e := list_in_decb fedge_eqb E e. 
Definition lgraph_edge_in_decb G e := match G with (V, E) => ledges_edge_in_decb E e end. 


(** Boolean deciders for some of the above definitions*)
Definition fedges_symmetric_decb (E : list fedge) := 
  forallb (fun e => let (v1, v2) := e in ledges_edge_in_decb E (v2, v1)) E. 

Definition fedge_wf_decb n e := let (v1, v2) := e in Nat.ltb v1 n && Nat.ltb v2 n. 
Definition fedges_wf_decb n E := forallb (fedge_wf_decb n) E.

Definition fraph_wf_decb G := let (V, E) := G in fedges_symmetric_decb E && fedges_wf_decb V E. 

Lemma fedge_eqb_iff e1 e2 : fedge_eqb e1 e2 = true <-> e1 = e2. 


(** We relate UGraph and fgraph instances in the following way *)
Definition isFlatVerticesOf V (finV : finType) := V = |elem finV|.

Definition isFlatVertexOf (finV : finType) V (v : finV):= V = index v. 

Inductive isFlatEdgesOf E V (finV : finType) (finE : finV -> finV -> Prop) : Prop := 
  mkIsFlatEdgesOf 
    (R__flatVertices : isFlatVerticesOf V finV)
    (R__edgesSound : forall v1 v2, (v1, v2) el E -> fedge_wf V (v1, v2) /\ 
                                                    exists (V1 V2 : finV), finE V1 V2 /\ isFlatVertexOf v1 V1 /\ isFlatVertexOf v2 V2)
    (R__edgesComplete : forall (v1 v2 : finV), finE v1 v2 -> (index v1, index v2) el E)
    : isFlatEdgesOf E V finE.
                                                  
