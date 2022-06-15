From Undecidability.L.Tactics Require Import LTactics.
From Undecidability.L.Datatypes Require Import LNat Lists LTerm LOptions LUnit.

From Undecidability.L.Complexity.LinDecode Require Export LTD_def LTDbool LTDlist LTDnat.

From Undecidability.L Require Import Functions.Decoding.


#[export]
Instance linDec_unit : linTimeDecodable unit.
Proof. 
  evar (c : nat). exists c. 
  unfold decode, decode_unit. cbn. extract. 
  solverec. [c]: exact 5. all: unfold c; lia. 
Qed. 

#[export]
Instance linDec_term : linTimeDecodable term.
Proof.
  evar (c:nat). exists c.
  unfold decode,decode_term;cbn. extract.
  recRel_prettify2;cbn[size];ring_simplify.
  [c]:exact (max (c__linDec nat) 10).
  all:unfold c;try nia.
Qed.

#[export]
Instance linDec_prod X Y `{_ : linTimeDecodable X} `{_:linTimeDecodable Y} : linTimeDecodable (X * Y). 
Proof. 
  evar (c : nat). exists c. 
  unfold decode, decode_prod, prod_decode; cbn. 
  extract. recRel_prettify2; cbn [size]; ring_simplify. 
  [c]: exact (max (max (c__linDec X) (c__linDec Y)) 14). all: unfold c; try nia. 
Qed. 

#[export]
Instance linDec_sum X Y `{_ : linTimeDecodable X} `{_:linTimeDecodable Y} : linTimeDecodable (X + Y). 
Proof. 
  evar (c : nat). exists c. 
  unfold decode, decode_sum, sum_decode; cbn. 
  extract. recRel_prettify2; cbn [size]; ring_simplify. 
  [c]: exact (max (max (c__linDec X) (c__linDec Y)) 14). all: unfold c; try nia. 
Qed. 

