From Complexity.Libs Require Import MoreList.
From Complexity.TM Require Import Code.
From Undecidability.TM Require Export Single.EncodeTapes.

Definition isNilBlank {sig : Type} (s : sigTape sig) : bool :=
  match s with
    NilBlank => true
  | _ => false
  end.

Definition isLeftBlank {sig : Type} (s : sigTape sig) : bool :=
  match s with
  | LeftBlank _  => true
  | _ => false
  end.

Definition isVoidBlank {sig : Type} (s : sigTape sig) : bool :=
  match s with
  | RightBlank _ => true
  | _ => false
  end.

Definition isSymbol {sig : Type} (s : sigTape sig) : bool :=
  match s with
  | UnmarkedSymbol _ | MarkedSymbol _ => true
  | _ => false
  end.

#[global]
Instance Encode_tape (sig : Type) : codable (sigTape sig) (tape sig) :=
  {|
    encode := @encode_tape sig;
  |}.

#[global]
Instance Encode_tapes (sig : Type) (n : nat) : codable (sigList (sigTape sig)) (tapes sig n) :=
  {|
    encode := @encode_tapes sig n;
  |}.

Lemma sizeOfTape_encodeTape sig' (t : tape sig') :
  | encode_tape t | = let l := sizeOfTape t in if 0 =? l then 1 else 2 + sizeOfTape t.
Proof.
  destruct t;cbn - [Nat.eqb].
  all:repeat (autorewrite with list;cbn [length]).
  1:easy.
  2,3:rewrite !Nat.add_succ_r. all:cbn [Nat.eqb]. all:Lia.nia.
Qed.


Lemma sizeOfTape_encodeTape_le sig' (t : tape sig') :
  | encode_tape t | <= 2 + sizeOfTape t.
Proof.
  rewrite sizeOfTape_encodeTape. cbn;destruct _;Lia.nia.
Qed.
