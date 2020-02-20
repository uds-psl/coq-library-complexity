From Undecidability.TM Require Import TM.
From Undecidability.L.TM Require Import TMflat TMflatEnc TMflatFun TMEncoding TapeDecode TMunflatten TMflatFun.
From Undecidability.L.Datatypes Require Import LNat LProd Lists.
From Undecidability.L.Complexity Require Import NP LinTimeDecodable ONotation.
From Undecidability.L Require Import Tactics.LTactics Functions.Decoding TMflatFun.
From Undecidability Require Import L.Functions.EqBool.
From Undecidability Require Import L.Datatypes.LNat.


Definition TMGenNP_fixed_mTM' (sig : finType) `{registered sig} n (M : mTM sig (S n)) : Vector.t (tape sig) n * nat * nat -> Prop :=
  fun '(ts, maxSize, steps) =>
    exists t1, sizeOfTape t1 <= maxSize /\ exists f, loopM (initc M (t1:::ts)) steps = Some f.

Definition HaltsOrDiverges_fixed_mTM (sig : finType) `{registered sig} n (M : mTM sig (S n)) : Vector.t (tape sig) n * nat * nat -> Prop :=
  fun '(ts, maxSize, steps) =>
    forall t1, sizeOfTape t1 <= maxSize -> forall k f, loopM (initc M (t1:::ts)) steps = Some f -> k <= steps.

Definition GenNPHalt_fixed_mTM (sig : finType) `{registered sig} n (M : mTM sig (S n))
  := restrictBy (HaltsOrDiverges_fixed_mTM M) (TMGenNP_fixed_mTM' M).

