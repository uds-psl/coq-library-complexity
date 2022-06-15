From Undecidability.L Require Import L Tactics.LTactics.
From Undecidability.L.Datatypes Require Import LSum LBool LNat Lists.

From Undecidability.L.AbstractMachines  Require Import FlatPro.Programs FlatPro.LM_heap_def Computable.LPro.

Local Fixpoint jumpTarget' (k:nat) (Q:Pro) (P:Pro) : option (Pro*Pro) :=
  match P with
  | retT :: P' => match k with
                | 0 => Some (rev Q,P')
                | S k' => jumpTarget' k' (retT::Q) P'
                end
  | lamT :: P' => jumpTarget' (S k) (lamT::Q) P'
  | t :: P' => jumpTarget' k (t::Q) P' (* either [varT n] or [appT] *)
  | [] => None
  end.

Local Lemma jumpTarget'_eq k Q P :
  jumpTarget k Q P = jumpTarget' k (rev Q) P.
Proof.
  induction P in k,Q|-*;cbn;repeat destruct _.
  all:try rewrite IHP.
  all:autorewrite with list;cbn. all:try easy.
Qed.

Definition time_jumpTarget' :=
  fix f (k : nat) q (P : list Tok) {struct P} : nat :=
  match P with
  | [] => 0
  | varT _ as t :: P' | appT as t :: P' => f k (S q) P'
  | lamT :: P' => f (S k) (S q) P'
  | retT :: P' => match k with
                  | 0 => q * 13
                  | S k' => f k' (S q) P'
                  end
  end + 27.

(*
Definition time_decompile_nice n := (n +1) * 31.

Lemma time_decompile_nice_leq l P A:
  time_decompile l P A <= time_decompile_nice (length P).
Proof.
  unfold time_decompile_nice.
  induction P in l,A |-*;cbn.
  all:repeat destruct _.
  all:cbn.
  all:try rewrite IHP;nia.
Qed. *)


#[export]
Instance term_jumpTarget' : computableTime' jumpTarget' (fun k _ => (5,fun Q _ => (1,fun P _ => (time_jumpTarget' k (length Q) P,tt)))).
Proof.
  extract. solverec.
Qed.

#[export]
Instance term_jumpTarget : computableTime' (jumpTarget 0 []) (fun P _ =>  (time_jumpTarget' 0 0 P,tt)).
Proof.
  apply computableTimeExt with (x:=fun x => jumpTarget' 0 [] x). now cbn;intros;rewrite jumpTarget'_eq.
  eexists. eapply computesTime_timeLeq. 2:now eapply extTCorrect.
  repeat intro;cbn.  easy.
Qed.
