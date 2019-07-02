
From Undecidability.L.Complexity.Problems  Require Import GenericNPcompleteProblem TMGenericNPcompleteProblem.

From Undecidability.L.Complexity  Require Import Synthetic NP.
From Undecidability.L Require Import Tactics.LTactics.

From Undecidability.TM Require Import TM.

From Undecidability.L Require Import TM.TMEncoding Datatypes.LFinType.
From Undecidability.LAM  Require Import TM.HaltingProblem.



(* Instance regSigT X P `{registered X} `{forall x, registered (P x)} : registered {x : X & P x}. *)
(* Proof. *)
(*   exists (fun x => ((λ f, f !!(enc (projT1 x)) !!(enc (projT2 x))))). *)
(*   all:cbn [convert TH minus].  *)
(*   -intros[]. split;Lproc. *)
(*   -intros x y. intros [=]. destruct x;destruct y. cbn in *. *)
(*    eapply inj_enc in H2. subst x. *)
(*    eapply inj_enc in H3. subst p. reflexivity. *)
(* Qed. *)

Local Existing Instance registered_finType.

Lemma polyRed_L_to_mTM : genericNPcompleteProblem ⪯p TMgenericNPcompleteProblem.
(*** TODO:*)
Abort.
