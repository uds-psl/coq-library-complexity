From Undecidability.L Require Import L Tactics.LTactics.
From Undecidability.L.AbstractMachines Require Import FlatPro.Programs.
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


Lemma size_Tok_enc_r t: sizeT t <= size (enc t).
Proof.
  destruct t;cbn. 2-4:now cbv.
  unfold enc;cbn. now rewrite <- LNat.size_nat_enc_r.
Qed.
