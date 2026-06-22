From Complexity.L Require Import ComputableTime.
From Undecidability.L Require Export Functions.EqBool.

Class eqbCompT X {R: encodable X} eqb {H:eqbClass (X:=X) eqb} :=
  { c__eqbComp :nat;
    eqbTime x y:= min x y* c__eqbComp;
    compT_eqb : computableTime' eqb (fun x _ =>(5,fun y _ => (eqbTime (size (enc x)) (size (enc y)),tt)))
  }.
Arguments eqbCompT _ {_ _ _}.
Arguments c__eqbComp _ {_ _ _ _}.

#[export] Hint Mode eqbCompT + - - -: typeclass_instances.

#[global]
Existing Instance compT_eqb.
