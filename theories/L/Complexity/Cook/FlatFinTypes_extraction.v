From Undecidability.L.Complexity.Cook Require Export FlatFinTypes.
From Undecidability.L.Complexity.Cook Require Import Prelim.
From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Import LProd LOptions LBool LLNat LLists LSum.
From Undecidability.L.Complexity Require Import PolyBounds. 

Instance term_flatOption : computableTime' flatOption (fun n _ => (2, tt)). 
Proof. 
  extract. solverec. 
Defined.

(*Definition flatProd_time (a b : nat) := c__mult1 + mult_time a b + 1.*)
(*Instance term_flatProd : computableTime' flatProd (fun a _ => (1, fun b _ => (flatProd_time a b, tt))). *)
(*Proof. *)
  (*extract. solverec. unfold flatProd_time. solverec. *)
(*Defined. *)

(*Definition flatSum_time a := c__add1 + add_time a + 1.  *)
(*Instance term_flatSum : computableTime' flatSum (fun a _ => (1, fun b _ => (flatSum_time a, tt))). *)
(*Proof. *)
  (*extract. solverec. unfold flatSum_time. solverec. *)
(*Defined. *)

Instance term_flatSome : computableTime' flatSome (fun a _ => (3, tt)). 
Proof. 
  extract. solverec. 
Defined. 

Instance term_flatInl : computableTime' flatInl (fun a _ => (1, tt)).
Proof. 
  extract. solverec. 
Defined. 

(*Definition c__flatInr := 13. *)
(*Definition flatInr_time a := c__add1 + add_time a + 3. *)
(*Instance term_flatInr : computableTime' flatInr (fun a _ => (1, fun k _ => (flatInr_time a, tt))). *)
(*Proof. *)
  (*extract. solverec. unfold flatInr_time; solverec. *)
(*Defined. *)

Definition c__flatPair := c__add1 + 2 + c__mult1. 
Definition flatPair_time x b := mult_time x b + add_time (x * b) + c__flatPair.
Instance term_flatPair : computableTime' flatPair (fun a _ => (1, fun b _ => (1, fun x _ => (1, fun y _ => (flatPair_time x b, tt))))). 
Proof. 
  extract. solverec. unfold flatPair_time, c__flatPair; solverec. 
Defined. 
