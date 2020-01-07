From Undecidability.TM Require Import TM.
From Undecidability.L.TM Require Import TMflat TMflatEnc TMflatFun TMEncoding TapeDecode TMunflatten.


Definition isValidInput (sig : finType) k (s : list sig) := |s| <= k. 

Definition initialTapeForString (sig : finType) (s : list sig) :=
  match s with
    | [] => niltape sig
    | x::s => @leftof sig x s
  end. 

(*single-tape machine whose head will always start at the leftmost position (i.e. initial tapes are niltape or leftof) *)
Definition GenNPflat : TM*nat*nat -> Prop:=
  fun '(M,maxSize, steps (*in unary*)) =>
    exists sig (M':mTM sig 1), isFlatteningTMOf M M' /\ (exists i, (exists f, loopM (initc M' ([|initialTapeForString i|])) steps = Some f)
         /\ length i <= maxSize).

Definition GenNP (i : { sig : finType & (mTM sig 1 * nat * nat)%type } ) : Prop := 
  match i with existT _ sig (tm, k, t) => exists inp, |inp| <= k /\ exists f, loopM (initc tm ([|initialTapeForString inp|])) t = Some f end. 
