From Undecidability.L.Tactics Require Import LTactics.
From Undecidability.L.Datatypes Require Import LProd LTerm.

From Undecidability.L Require Import Functions.Encoding.
From Complexity Require Import Complexity.Monotonic .

Class encodableP `(X:Type) `{encodable X}: Type :=
  {
    c__regP : nat;
    comp_enc_lin : computableTime' (enc (X:=X)) (fun x _ => (size (enc x) *c__regP,tt));
  }.

Arguments encodableP : clear implicits.
Arguments encodableP _ {_}.
Arguments c__regP : clear implicits.
Arguments c__regP _ {_ _} : simpl never.
Hint Mode encodableP + + : typeclass_instances. (* treat argument as input and force evar-freeness*)

Existing Instance comp_enc_lin.
Typeclasses Opaque enc.


Instance regP_nat : encodableP nat.
Proof.
  evar (c:nat).
  exists c.
  eexists _. 
  eapply computesTime_timeLeq.
  2:now apply term_nat_enc.
  repeat intro. split. 2:easy.
  cbn [fst]. rewrite -> size_nat_enc. [c]:exact 14. unfold c, c__natsizeS, c__natsizeO. nia.
Qed.


Instance regP_term : encodableP term.
Proof.
  evar (c:nat).
  exists c.
  eexists _. 
  eapply computesTime_timeLeq.
  2:now apply term_term_enc.
  repeat intro. split. 2:easy.
  cbn [fst]. rewrite -> size_term_enc_r. [c]:exact 30. unfold c. nia.
Qed.

Instance regP_Prod X Y `{encodableP X} `{encodableP Y}: encodableP (X*Y).
Proof.
  evar (c:nat).
  exists c.
  eexists _. 
  eapply computesTime_timeLeq.
  2:now apply term_prod_enc.
  intros [] _. split. 2:easy.
  cbn [fst]. rewrite -> size_prod.
  cbn. [c]:exact (c__regP X + c__regP Y + 4). unfold c. nia.
Qed.

From Undecidability.L.Datatypes Require Import Lists.

Instance regP_list X `{encodableP X}: encodableP (list X).
Proof.
  evar (c:nat).
  exists c.
  eexists _. 
  eapply computesTime_timeLeq.
  2:now apply term_list_enc.
  intros l _. split. 2:easy.
  cbn [fst]. rewrite -> size_list.
  cbn. [c]:exact (c__regP X + 17). unfold c, c__listsizeCons, c__listsizeNil.
  induction l;cbn. all:nia.
Qed.

Import LOptions.

Instance regP_option X `{encodableP X}: encodableP (option X).
Proof.
  evar (c:nat).
  exists c.
  eexists _. 
  eapply computesTime_timeLeq.
  2:now apply term_option_enc.
  intros l _. split. 2:easy.
  cbn [fst]. rewrite -> size_option.
  [c]:exact (c__regP X + 5). unfold c.
  now destruct l.
Qed.

Instance regP_bool : encodableP bool.
Proof.
  evar (c:nat).
  exists c.
  eexists _. 
  eapply computesTime_timeLeq.
  2:now apply bool_enc.
  intros l _. split. 2:easy.
  unfold enc;cbn.
  [c]:exact (4). unfold c.
  destruct l;cbn [size ]. all:lia.
Qed.
