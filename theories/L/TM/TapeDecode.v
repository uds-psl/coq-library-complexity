From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Import LNat Lists LProd LFinType.
From Undecidability.L Require Import TM.TMEncoding.


From Undecidability Require Import TM.TM.

From Undecidability.L Require Import Functions.Decoding Complexity.Synthetic Complexity.LinTimeDecodable.

Instance linDec_tape X `{_:linTimeDecodable X}: linTimeDecodable (tape X).
Proof.
  evar (c:nat). exists c.
  unfold decode, decode_tape,tape_decode.
  extract.
  recRel_prettify2;cbn[size];ring_simplify. idtac. 
  [c]:exact (max (c__linDec (list X)) (max (c__linDec (X)) 11)).
  all:unfold c;try nia.
Qed.
