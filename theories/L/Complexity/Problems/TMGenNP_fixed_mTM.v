From Undecidability.TM Require Import TM.
From Undecidability.L.TM Require Import TMflat TMflatEnc TMflatFun TMEncoding TapeDecode TMunflatten TMflatFun.
From Undecidability.L.Datatypes Require Import LNat LProd Lists.
From Undecidability.L.Complexity Require Import NP LinTimeDecodable ONotation.
From Undecidability.L Require Import Tactics.LTactics Functions.Decoding TMflatFun.
From Undecidability Require Import L.Functions.EqBool.
From Undecidability Require Import L.Datatypes.LNat.

(** For each Machine M (with n+1 tapes), we define this problem:
Given n tapes and a sizeBound and a step bound, does there exist a (small enough) first tape such that the machine halts on the resulting n+1 tapes in fewer? *)

Definition TMGenNP_fixed_mTM' (sig : finType) `{registered sig} n (M : mTM sig (S n)) : Vector.t (tape sig) n * nat * nat -> Prop :=
  fun '(ts, maxSize, steps) =>
    exists t1, sizeOfTape t1 <= maxSize /\ exists f, loopM (initc M (t1:::ts)) steps = Some f.

Definition HaltsOrDiverges_fixed_mTM (sig : finType) `{registered sig} n (M : mTM sig (S n)) : Vector.t (tape sig) n * nat * nat -> Prop :=
  fun '(ts, maxSize, steps) =>
    forall t1, sizeOfTape t1 <= maxSize -> forall k f, loopM (initc M (t1:::ts)) steps = Some f -> k <= steps.

Definition TMGenNP_fixed_mTM (sig : finType) `{registered sig} n (M : mTM sig (S n))
  := restrictBy (HaltsOrDiverges_fixed_mTM M) (TMGenNP_fixed_mTM' M).

Arguments TMGenNP_fixed_mTM : clear implicits.
Arguments TMGenNP_fixed_mTM {_ _ _}.

