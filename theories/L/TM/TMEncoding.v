From Undecidability.L.TM Require Export TMEncoding.
From Undecidability.TM.Util Require Import TM_facts.
From Complexity.L Require Import ComputableTime Functions.EqBool.

Section reg_tapes.
  Variable sig : Type.
  Context `{reg_sig : encodable sig}.
  
  Implicit Type (t : TM.tape sig).

  (*Internalize constructors **)

  Global Instance term_leftof : computableTime' (@leftof sig) (fun _ _ => (1, fun _ _ => (1,tt))).
  Proof.
    extract constructor.
    solverec.
  Qed.

  Global Instance term_rightof : computableTime' (@rightof sig) (fun _ _ => (1, fun _ _ => (1,tt))).
  Proof.
    extract constructor. solverec.
  Qed.

  Global Instance term_midtape : computableTime' (@midtape sig) (fun _ _ => (1, fun _ _ => (1,fun _ _ => (1,tt)))).
  Proof.
    extract constructor. solverec.
  Qed.
End reg_tapes.

#[global]
Instance eqbCompT_move : eqbCompT move.
Proof.
  evar (c:nat). exists c. unfold move_eqb.
  unfold enc;cbn.
  extract.
  solverec.
  [c]:exact 3.
  all:unfold c;try lia.
Qed.
