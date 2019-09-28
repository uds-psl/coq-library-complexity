From Undecidability.L Require Import L.
From Undecidability.L.Tactics Require Import LTactics ComputableTactics.
From Undecidability.L.Datatypes Require Import LProd LTerm LNat Lists LOptions.
From Undecidability.L.Complexity Require Import NP Synthetic Monotonic.
From Undecidability.L.Functions Require Import Size.

From Undecidability.L.Datatypes Require Import LGraph. 


(* k-Clique: duplicate-free list of k nodes such that all pairwise-distinct nodes are connected *)
Inductive isClique (g : UndirectedGraph) : list (Fin.t (V g)) -> nat -> Prop :=
| isCliqueB : isClique [] 0
| isCliqueS (cl : list (Fin.t (V g))) (node : Fin.t (V g)) (k : nat):
    isClique cl k -> (not (node el cl)) -> (forall (node' : Fin.t (V g)), node' el cl -> E node node') -> isClique (node :: cl) (S k).

Definition Clique (input : UndirectedGraph * nat) :=
  let (g, k) := input in exists cl, @isClique g cl k. 
