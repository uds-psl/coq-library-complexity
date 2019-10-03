From Undecidability.L.Tactics Require Import LTactics.
From Undecidability.L.Datatypes Require Import LNat Lists LTerm LOptions.

From Undecidability.L Require Import Functions.Decoding Complexity.Synthetic.

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

Lemma linDec_polyTimeComputable  X `{_:linTimeDecodable X}: polyTimeComputable (decode X).
Proof.
  evar (f:nat -> nat).
  exists f.
  -split. eexists _. 
   eapply computesTime_timeLeq.
   2:now eapply comp_enc_lin.
   intros x _;cbn [fst snd]. split.
   2:easy.
   rewrite size_term_enc_r. generalize (size (enc x)) as n;intros.
   [f]:intro. unfold f. reflexivity.
  -unfold f. smpl_inO.
  -unfold f. smpl_inO.
  -evar (f':nat -> nat).
   exists f'. 
   repeat eapply conj.
   +intros t.
    specialize (decode_correct2 (X:=X) (t:=t)) as H'.
    destruct decode.
    setoid_rewrite <- H'. 2:reflexivity.
    *rewrite size_option,LTerm.size_term_enc_r.
    generalize (size (enc (enc x))). [f']:intro. unfold f'. reflexivity.
    *unfold enc at 1. cbn. unfold f'. easy.
   +unfold f'. smpl_inO.
   +unfold f'. smpl_inO.
Qed.

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

Instance linDec_bool : linTimeDecodable bool.
Proof.
  evar (c : nat). exists c. unfold decode, decode_bool. extract. 
  solverec. [c]: exact 5. all: subst c; lia.
Qed. 

