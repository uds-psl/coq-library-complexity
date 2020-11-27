From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Import LNat Lists LProd LFinType.
From Undecidability.L Require Import TM.TMEncoding.


From Undecidability Require Import TM.TM.

From Undecidability.L Require Import Functions.Decoding.
From Complexity.L Require Import Complexity.Synthetic Complexity.LinTimeDecodable.

From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Import LNat Lists LProd LFinType LVector.
From Undecidability.L Require Import Functions.EqBool.

From Undecidability Require Import TM.Util.VectorPrelim.


From Undecidability Require Import TM.TM.
Require Import Undecidability.Shared.Libs.PSL.FiniteTypes.FinTypes.

Import L_Notations.

From Undecidability Require Import TMEncoding.


Import L.
Definition tape_decode X `{decodable X} (s : term) : option (tape X) :=
  match s with
  | lam (lam (lam (lam 3))) => Some (niltape _)
  | lam (lam (lam (lam (app ( app 2 c) r)))) =>
     match decode X c,decode (list X) r with
       Some x, Some xs => Some (leftof x xs)
     | _,_ => None
     end
  | lam (lam (lam (lam (app ( app 1 c) l)))) =>
    match decode X c,decode (list X) l with
      Some x, Some xs => Some (rightof x xs)
    | _,_ => None
    end
  | lam (lam (lam (lam (app ( app (app 0 l) c) r)))) =>
    match decode X c,decode (list X) l,decode (list X) r with
      Some x, Some xs, Some r => Some (midtape xs x r)
    | _,_,_ => None
    end
  | _ => None
  end.

Arguments tape_decode : clear implicits.
Arguments tape_decode _ {_ _} _.

Instance decode_tape X {Hreg:encodable X} {Hdec:decodable X}: decodable (tape X).
Proof.
  exists (tape_decode X).
  all:unfold enc at 1. all:cbn.
  -destruct x;cbn.
   all:repeat setoid_rewrite decode_correct. all:easy.
  -destruct t eqn:eq. all:cbn.
   all:repeat let eq := fresh in destruct _ eqn:eq. all:try congruence.
   all:intros ? [= <-].
   easy.
   all:cbn.
   all: (setoid_rewrite @decode_correct2;[ |try eassumption..]).
   all:reflexivity.
Defined.


Instance linDec_tape X `{_:linTimeDecodable X}: linTimeDecodable (tape X).
Proof.
  evar (c:nat). exists c.
  unfold decode, decode_tape,tape_decode.
  extract.
  recRel_prettify2;cbn[size];ring_simplify. idtac. 
  [c]:exact (max (c__linDec (list X)) (max (c__linDec (X)) 11)).
  all:unfold c;try nia.
Qed.
