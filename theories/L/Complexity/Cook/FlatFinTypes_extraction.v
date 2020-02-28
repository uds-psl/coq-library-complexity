From Undecidability.L.Complexity.Cook Require Export FlatFinTypes.
From Undecidability.L.Complexity.Cook Require Import Prelim.
From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Import LProd LOptions LBool LLNat LLists LSum.
From Undecidability.L.Complexity Require Import PolyBounds. 

Instance term_flatOption : computableTime' flatOption (fun n _ => (2, tt)). 
Proof. 
  extract. solverec. 
Defined.

Definition flatProd_time (a b : nat) := 1. 
Instance term_flatProd : computableTime' flatProd (fun a _ => (1, fun b _ => (flatProd_time a b, tt))). 
Proof. 
  extract. solverec.

Definition flatOption (n : nat) := S n.
Definition flatProd (a b : nat) := a * b.
Definition flatSum (a b : nat) := a + b.

(*flat value constructors *)
Definition flatNone := 0.
Definition flatSome k := S k. 
Definition flatInl (k : nat) := k.
Definition flatInr (a: nat) k := a + k. 
Definition flatPair (a b : nat) x y := x * b + y. 


