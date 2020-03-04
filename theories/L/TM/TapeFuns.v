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
    (*
    Global Instance term_sizeOfmTapes n:
      computableTime' (@sizeOfmTapes sig n) (fun t _ => ((sizeOfmTapes t) * n*cnst 1 + cnst 0,tt)).
    Proof.
      set (f:= (fix sizeOfmTapes acc (ts : list (tape sig)) : nat :=
                        match ts with
                        | [] => acc
                        | t :: ts0 => sizeOfmTapes (Init.Nat.max acc (sizeOfTape t)) ts0
                        end)).
      
      assert (H' : extEq (fun v => f 0 (Vector.to_list v)) (@sizeOfmTapes sig n)).
      { intros x. hnf. unfold sizeOfmTapes. generalize 0.
        induction x using Vector.t_ind;intros acc. cbn. nia.        
        cbn in *. rewrite <- IHx. unfold Vector.to_list. nia.
      }
      (*TODO: express runtime nicely, e.g. better computational behaviour for sizeOfmTapse. *)
      assert (computableTime' f (fun acc _ => (5, fun t _ => ((max acc (Vector.fold_right Init.Nat.max (Vector.map (sizeOfTape (sig:=sig))(Vector.of_list t)) 0)*65 + 61) * (length t) + 9,tt)))).
      { unfold f. extract. solverec. set (Vector.fold_right _ _ _). nia. }

      eapply computableTimeExt. exact H'.
      extract. solverec. unfold sizeOfmTapes. rewrite Vector.fold_left_right_assoc_eq. 2:intros;nia.
      Check (Vector.of_list (Vector.to_list x)).
      rewrite Vector.of_list.
      set (Vector.fold_right _ _ _). 
      cbn eta. rewrite 
      extract. unfold sizeOfmTapesFlat_time. solverec. 
    Qed.
*)
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



