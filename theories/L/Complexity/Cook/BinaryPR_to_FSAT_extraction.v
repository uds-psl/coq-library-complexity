From Undecidability.L.Complexity.Cook Require Import FlatPR BinaryPR FSAT BinaryPR_to_FSAT.

From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Import LProd LOptions LBool LLNat LLists LSum.
From Undecidability.L.Complexity Require Import PolyBounds. 


(** encodeLiteral *)
Definition c__encodeLiteral := 1.
Instance term_encodeLiteral : computableTime' encodeLiteral (fun v _ => (1, fun s _ => (c__encodeLiteral, tt))). 
Proof. 
  (*TODO: simplification fails. why!? *)
  extract. 
Admitted. 

