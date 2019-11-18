From Undecidability.TM Require Import TM.
From Undecidability.L.TM Require Import TMflat TMflatEnc TMflatFun TMEncoding TapeDecode TMunflatten.

Definition mkinitTape (sig : finType) (i : list sig) : tape sig := match i with nil => niltape sig | (x::xr) => @leftof sig x xr end. 

(*single-tape machine whose head will always start at the leftmost position (i.e. initial tapes are niltape or leftof) *)
Definition GenNP : TM*nat*nat -> Prop:=
  fun '(M,maxSize, steps (*in unary*)) =>
    exists sig (M':mTM sig 1), isFlatteningTMOf M M' /\ (exists i, (exists f, loopM (initc M' ([|mkinitTape i|])) steps = Some f)
         /\ length i <= maxSize).
