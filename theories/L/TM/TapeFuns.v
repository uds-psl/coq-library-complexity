From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Import LNat Lists LProd LFinType LVector.
From Undecidability.L Require Import TM.TMEncoding.


From Undecidability Require Import TM.TM.
Require Import PslBase.FiniteTypes.FinTypes.


Section fix_sig.
  Variable sig : Type.
  Context `{reg_sig : registered sig}.

  Section reg_tapes.

    Global Instance term_tape_move_left' : computableTime' (@tape_move_left' sig) (fun _ _ => (1, fun _ _ => (1,fun _ _ => (12,tt)))).
    Proof.
      extract. solverec.
    Qed.

    Global Instance term_tape_move_left : computableTime' (@tape_move_left sig) (fun _ _ => (23,tt)).
    Proof.
      extract. solverec.
    Qed.

    Global Instance term_tape_move_right' : computableTime' (@tape_move_right' sig) (fun _ _ => (1, fun _ _ => (1,fun _ _ => (12,tt)))).
    Proof.
      extract. solverec.
    Qed.

    Global Instance term_tape_move_right : computableTime' (@tape_move_right sig) (fun _ _ => (23,tt)).
    Proof.
      extract. solverec.
    Qed.

    Global Instance term_tape_move : computableTime' (@tape_move sig) (fun _ _ => (1,fun _ _ => (48,tt))).
    Proof.
      extract. solverec.
    Qed.

    Global Instance term_left : computableTime' (@left sig) (fun _ _ => (10,tt)).
    Proof.
      extract. solverec.
    Qed.

    Global Instance term_right : computableTime' (@right sig) (fun _ _ => (10,tt)).
    Proof.
      extract. solverec.
    Qed.

    Global Instance term_tape_write : computableTime' (@tape_write sig) ((fun _ _ => (1,fun _ _ => (28,tt)))).
    Proof.
      extract. solverec.
    Qed.

    
    Global Instance term_tapeToList:  computableTime' (@tapeToList sig) (fun t _ => (sizeOfTape t*29 + 26,tt)).  
    extract. recRel_prettify2. all:repeat (simpl_list;cbn -[plus mult]). all:nia.
    Proof.
    Qed.


    Global Instance term_sizeOfTape: computableTime' (@sizeOfTape sig) (fun t _ => (sizeOfTape t*40 + 35,tt)).
    Proof.
      extract. unfold sizeOfTape. solverec.
    Qed.

    Global Instance term_current: computableTime' ((current (sig:=sig))) (fun _ _ => (10,tt)).
    Proof.
      extract.
      solverec.
    Qed.

    Global Instance term_current_chars n: computableTime' (current_chars (sig:=sig) (n:=n))  (fun _ _ => (n * 22 +12,tt)).
    Proof.
      extract.
      solverec.
      rewrite map_time_const,to_list_length.  omega.
    Qed.

    Global Instance term_doAct: computableTime' (doAct (sig:=sig)) (fun _ _ => (1,fun _ _ => (89,tt))).
    Proof.
      extract.
      solverec.
    Qed.


  End reg_tapes.
End fix_sig.

Fixpoint loopTime {X} `{registered X} f (fT: timeComplexity (X -> X)) (p: X -> bool) (pT : timeComplexity (X -> bool)) (a:X) k :=
  fst (pT a tt) +
  match k with
    0 => 7
  |  S k =>
     fst (fT a tt) + 13 + loopTime f fT p pT (f a) k
  end.

Instance term_loop A `{registered A} :
  computableTime' (@loop A)
                 (fun f fT => (1,fun p pT => (1,fun a _ => (5,fun k _ =>(loopTime f fT p pT a k,tt))))).
Proof.
  extract.
  solverec.
Qed.



