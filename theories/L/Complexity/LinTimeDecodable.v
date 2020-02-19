From Undecidability.L.Tactics Require Import LTactics.
From Undecidability.L.Datatypes Require Import LNat Lists LTerm LOptions.

From Undecidability.L Require Import Functions.Decoding.

Class linTimeDecodable `(X:Type) `{decodable X}: Type :=
  {
    c__linDec : nat;
    comp_enc_lin : computableTime' (decode X) (fun x _ => (size x *c__linDec + c__linDec,tt));
  }.

Arguments linTimeDecodable : clear implicits.
Arguments linTimeDecodable _ {_ _}.

Arguments c__linDec : clear implicits.
Arguments c__linDec _ {_ _ _}.

Existing Instance comp_enc_lin.

Instance linDec_nat : linTimeDecodable nat.
Proof.
  evar (c:nat). exists c.
  unfold decode,decode_nat;cbn. extract.
  recRel_prettify2;cbn[size];ring_simplify.
  [c]:exact 9.
  all:unfold c;try lia.
Qed.

Instance linDec_term : linTimeDecodable term.
Proof.
  evar (c:nat). exists c.
  unfold decode,decode_term;cbn. extract.
  recRel_prettify2;cbn[size];ring_simplify.
  [c]:exact (max (c__linDec nat) 10).
  all:unfold c;try nia.
Qed.

Instance linDec_list X `{_:linTimeDecodable X}: linTimeDecodable (list X).
Proof.
  evar (c:nat). exists c.
  unfold decode,decode_list,list_decode;cbn.
  extract.
  recRel_prettify2;cbn[size];ring_simplify.
  [c]:exact (max (c__linDec X) 12).
  all:unfold c;try nia.
Qed.

