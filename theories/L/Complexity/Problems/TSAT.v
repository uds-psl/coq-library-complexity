From Undecidability.L Require Import L.
From Undecidability.L.Tactics Require Import LTactics ComputableTactics.
From Undecidability.L.Datatypes Require Import LProd LTerm LNat Lists LOptions.
From Undecidability.L.Complexity Require Import NP Synthetic Monotonic.
From Undecidability.L.Functions Require Import Size.

From Undecidability.L.Complexity Require Export Problems.SAT.

Inductive TCNF : cnf -> Prop :=
| TCNFB : TCNF []
| TCNFS (c : cnf) (cl : clause) : (|cl|) = 3 -> TCNF c -> TCNF (cl :: c).               

Definition TSAT (c : cnf) : Prop := TCNF c /\ exists (a : assgn), evalCnf a c = Some true. 


