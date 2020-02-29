From Undecidability.L Require Import L.
From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Import LLists LLNat LProd.
From PslBase Require Import FinTypes. 

(** *Flat representation of an undirected graph. *)

(** We represent graphs using a number, denoting the number of nodes, and a list of edges. *)
Notation fvertex := (nat) (only parsing).
Notation fedge := ((fvertex * fvertex)%type) (only parsing).
Notation fgraph := ((nat * list fedge)%type) (only parsing).

Implicit Types (e : fedge) (E : list fedge) (G : fgraph) (V : fvertex). 

(** We require the list of edges to be symmetric and to only mention nodes which actually exist. *)
Definition fedges_symmetric (E : list fedge) := forall V1 V2, (V1, V2) el E -> (V2, V1) el E.
Definition fedge_wf n e := match e with (V1, V2) => V1 < n /\ V2 < n end. 
Definition fedges_wf n (E : list fedge) := forall e, e el E -> fedge_wf n e. 

Definition fgraph_wf G := match G with (V, E) => fedges_symmetric E /\ fedges_wf V E end. 

Definition fedge_eqb := prod_eqb Nat.eqb Nat.eqb.
Definition lgraph_edge_in_decb G e := match G with (V, E) => list_in_decb fedge_eqb E e end. 


(** We relate UGraph and fgraph instances in the following way *)
Section fixUGraph. 

Inductive isFlatEdgesOf (finV : finType) : list fedge -> 

