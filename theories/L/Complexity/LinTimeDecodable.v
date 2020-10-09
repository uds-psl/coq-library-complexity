From Undecidability.L.Tactics Require Import LTactics.
From Undecidability.L.Datatypes Require Import LNat Lists LTerm LOptions LUnit.

From Complexity.L Require Import Functions.Decoding.

From Complexity.L Require Export LinTimeDecodable_def.


Instance linDec_unit : linTimeDecodable unit.
Proof. 
  evar (c : nat). exists c. 
  unfold decode, decode_unit. cbn. extract. 
  solverec. [c]: exact 5. all: unfold c; lia. 
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

Instance linDec_prod X Y `{_ : linTimeDecodable X} `{_:linTimeDecodable Y} : linTimeDecodable (X * Y). 
Proof. 
  evar (c : nat). exists c. 
  unfold decode, decode_prod, prod_decode; cbn. 
  extract. recRel_prettify2; cbn [size]; ring_simplify. 
  [c]: exact (max (max (c__linDec X) (c__linDec Y)) 14). all: unfold c; try nia. 
Qed. 

Instance linDec_sum X Y `{_ : linTimeDecodable X} `{_:linTimeDecodable Y} : linTimeDecodable (X + Y). 
Proof. 
  evar (c : nat). exists c. 
  unfold decode, decode_sum, sum_decode; cbn. 
  extract. recRel_prettify2; cbn [size]; ring_simplify. 
  [c]: exact (max (max (c__linDec X) (c__linDec Y)) 14). all: unfold c; try nia. 
Qed. 

