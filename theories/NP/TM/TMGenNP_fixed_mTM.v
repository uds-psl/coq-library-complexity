From Undecidability.TM Require Import TM_facts.
From Undecidability.L.TM Require Import TMEncoding.
From Complexity.Complexity Require Import NP Subtypes.
From Undecidability.L Require Import Tactics.LTactics.

(** For each Machine M (with n+1 tapes), we define this problem:
Given n tapes and a sizeBound and a step bound, does there exist a (small enough) first tape such that the machine halts on the resulting n+1 tapes in fewer steps than the step bound? *)

(** We contain this on haltsOrDiverges as our MutiTape2SingleTape-translation probably only knows upper bounds of the step count.  *)
Section mTM.
  Context {sig : finType} {n} (M : TM sig (S n)).

  Definition HaltsOrDiverges_mTM_fixed : Vector.t (tape sig) n * nat * nat -> Prop :=
    fun '(ts, maxSize, steps) =>
      forall t__cert' k res', loopM (initc M (t__cert':::ts)) k = Some res'
                      -> exists t__cert res, sizeOfTape t__cert <= maxSize
                                      /\ loopM (initc M (t__cert:::ts)) steps = Some res.

  Definition mTMGenNP_fixed' := (fun '(ts, maxSize, steps) =>
          exists t1, sizeOfTape t1 <= maxSize /\ exists f, loopM (initc M (t1:::ts)) steps = Some f).

  Definition mTMGenNP_fixed : {x | HaltsOrDiverges_mTM_fixed x} -> Prop :=
    restrictBy HaltsOrDiverges_mTM_fixed mTMGenNP_fixed'.

End mTM.

Arguments mTMGenNP_fixed {_ _} _.


Definition initTape_singleTapeTM (sig : Type) (s : list sig) :=
  match s with
    | [] => niltape sig
    | x::s => @leftof sig x s
  end. 

Definition TMGenNP_fixed {sig : finType} (M : TM sig 1)
  := (fun '(ts, maxSize, steps) =>
        exists (cert : list sig), length cert <= maxSize
                            /\ exists res, execTM M [|initTape_singleTapeTM (ts++cert)|] steps = Some res).

