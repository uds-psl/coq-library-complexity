From Undecidability.L Require Import L Tactics.LTactics.
From Undecidability.L.AbstractMachines.FlatPro Require Import ProgramsDef.
From Undecidability.L Require Import Tactics.GenEncode.

From Undecidability.L.Datatypes Require Import LNat.


Run TemplateProgram (tmGenEncode "token_enc" Tok).
Hint Resolve token_enc_correct : Lrewrite.

Instance term_varT : computableTime' varT (fun _ _ => (1,tt)).
extract constructor. solverec.
Qed.
(* Instance term_tok_eqb : computableTime' Tok_eqb (fun t _ => (1,fun t' _ => (min (sizeT t) (sizeT t') * 17 + 10,tt))). *)
(* extract. solverec. *)
(* Qed. *)
