From Undecidability.TM Require Import TM.
From Undecidability.L.TM Require Import TMflat TMflatEnc TMflatFun TMEncoding TapeDecode TMunflatten.
From Undecidability.L.Complexity.Cook Require Import FlatFinTypes.

(** *Definition of a generic NP-hard problem *)
(*(at least it is NP-hard if one accepts Turing machines)*)

Definition isValidCert (sig : finType) k' (c : list sig) := |c| <= k'.
Definition isValidInput (sig : finType) s k' (inp : list sig) := exists c, isValidCert k' c /\ inp = s ++ c. 

Definition initialTapeForString (sig : finType) (s : list sig) :=
  match s with
    | [] => niltape sig
    | x::s => @leftof sig x s
  end. 

(*single-tape machine whose head will always start at the leftmost position (i.e. initial tapes are niltape or leftof) *)
Definition GenNP (i : { sig : finType & (mTM sig 1 * list sig * nat * nat)%type } ) : Prop := 
  match i with existT _ sig (tm, s, k', t) => exists cert, |cert| <= k'
                                                      /\ exists f, loopM (initc tm ([|initialTapeForString (s ++ cert)|])) t = Some f
  end.

Definition FlatGenNP : TM*list nat *nat*nat -> Prop:=
  fun '(M,s,maxSize, steps (*in unary*)) =>
    exists sig (M':mTM sig 1) sfin, isFlatteningTMOf M M' /\ isFlatListOf s sfin /\ GenNP (existT _ _ (M', sfin, maxSize, steps)). 
