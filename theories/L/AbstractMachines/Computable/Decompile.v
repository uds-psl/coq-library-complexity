From Undecidability.L Require Import L Tactics.LTactics.
From Undecidability.L.Datatypes Require Import LSum LBool LNat Lists.

From Undecidability.L.AbstractMachines Require Import Programs.

Require Import Undecidability.L.AbstractMachines.LargestVar.

From Undecidability.L.AbstractMachines.Computable Require Import Shared.

Definition time_decompile :=
  fix f (l:nat) (P:list Tok) A :=
    match P with
    | [] => 0
    | varT n :: P0 => f l P0 (var n::A)
    | ProgramsDef.appT :: P0 =>
      match A with
      | [] => 0
      | [t] => 0
      | t :: s :: A0 => f l P0 (app s t :: A0)
      end
    | ProgramsDef.lamT :: P0 => f (S l) P0 A
    | retT :: P0 =>
      match l with
      | 0 => 0
      | S l0 => match A with
               | [] => 0
               | s :: A0 => f l0 P0 (lam s :: A0)
               end
      end
    end + 31.

Definition time_decompile_nice n := (n +1) * 31.

Lemma time_decompile_nice_leq l P A:
  time_decompile l P A <= time_decompile_nice (length P).
Proof.
  unfold time_decompile_nice.
  induction P in l,A |-*;cbn.
  all:repeat destruct _.
  all:cbn.
  all:try rewrite IHP;nia.
Qed.

Instance term_decompile : computableTime' decompile (fun l _ => (5,fun P _ => (1, fun A _ =>  (time_decompile l P A,tt)))).
Proof.
  extract. solverec.
Qed.
