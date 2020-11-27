From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Import LNat Lists LProd LOptions LBool.
From Undecidability.L Require Import Functions.Decoding.


From Complexity.L.TM Require Export TMflat.
From Undecidability.L.TM Require Import TMEncoding.

Import Nat TM_facts.
Import TMflat.
Import GenEncode.
MetaCoq Run (tmGenEncode "flatTM_enc" flatTM).
Hint Resolve flatTM_enc_correct : Lrewrite.


Instance term_Build_TM : computableTime' (Build_flatTM) (fun _ _ => (1,fun _ _ => (1,fun _ _ => (1,fun _ _ => (1,fun _ _ => (1,fun _ _ => (1,tt))))))).
Proof.
  extract constructor. solverec. 
Defined.

Instance term_sig : computableTime' sig (fun _ _ => (9,tt)).
Proof.
  extract. solverec.
Defined.


Instance term_tapes : computableTime' tapes (fun _ _ => (9,tt)).
Proof.
  extract. solverec.
Defined.

Instance term_states : computableTime' states (fun _ _ => (9,tt)).
Proof.
  extract. solverec.
Defined.

Instance term_trans : computableTime' trans (fun _ _ => (9,tt)).
Proof.
  extract. solverec.
Defined.

Instance term_start : computableTime' start (fun _ _ => (9,tt)).
Proof.
  extract. solverec.
Defined.

Instance term_halt : computableTime' halt (fun _ _ => (9,tt)).
Proof.
  extract. solverec.
Defined.


(*
Definition TM_decode (s : term) : option TM :=
  match s with
  | lam (app(app(app(app(app (app O sig) tapes) states) trans) start) halt) =>
    match decode nat sig,decode nat tapes, decode nat states, decode (list (nat * list (option nat) * (nat * list (option nat * TM.move)))) trans, decode nat start, decode (list bool) halt with
      Some sig, Some tapes, Some states, Some trans, Some start, Some halt =>
      Some (Build_TM sig tapes states trans start halt)
    | _,_,_,_,_,_ => None
    end
  | _ => None
  end.

Arguments list_decode : clear implicits.
Arguments list_decode _ {_ _} _.

Instance decode_TM : decodable TM.
Proof.
  exists (list_decode X).
  all:unfold enc at 1. all:cbn.
  -induction x;cbn.
   +easy.
   +setoid_rewrite decode_correct. now rewrite IHx.
  -apply (size_induction (f := size) (p := (fun t => forall x, list_decode X t = Some x -> list_enc x = t))). intros t IHt s.
   destruct t eqn:eq. all:cbn.
   all:repeat let eq := fresh in destruct _ eqn:eq. all:try congruence.
   all:intros [= <-].
   +easy.
   +cbn. change (match H with
                | @mk_encodable_ enc _ _ => enc
                 end x) with (enc x). erewrite decode_correct2. 2:easy.
    erewrite IHt.
    *reflexivity.
    *cbn;lia.
    *easy.
Defined.


Instance linDec_TM : linTimeDecodable TM.
Proof.
  exists c__encTM.
  eexists _. 
  eapply computesTime_timeLeq.
  2:now apply term_TM_enc.
  intros l _. split. 2:easy.
  cbn [fst]. reflexivity.
Qed.

*)

Lemma size_TM (M:flatTM):
  size (enc M) = let (a,b,c,d,e,f) := M in size (enc a) + size (enc b) +size (enc c) +size (enc d) + size (enc e) + size (enc f) + 8.
Proof.
  unfold enc;cbn. destruct M as []. cbn. solverec.
Qed.

From Complexity.L.Complexity Require Export EncodableP LinTimeDecodable.


Instance term_move_enc
  :computableTime' (enc (X:=move)) (fun x _ => (15,tt)).
Proof.
  unfold enc;cbn. extract. solverec.
Qed.

Instance regP_move : encodableP TM.move.
Proof.
  evar (c:nat).
  exists c.
  eexists _. 
  eapply computesTime_timeLeq.
  2:now apply term_move_enc.
  intros l _. split. 2:easy.
  cbn.
  [c]:exact (4). unfold c.
  destruct l;cbv. all:lia.
Qed.


Definition c__encTM := max (c__regP (list (nat * list (option nat) * (nat * list (option nat * TM.move))))) (max (c__regP nat) (max (c__regP (list bool)) 4)).

Instance term_TM_enc
  :computableTime' (enc (X:=flatTM)) (fun x _ => (size (enc x) * c__encTM,tt)).
Proof.
  unfold enc;cbn.
  extract.
  intros _ M [].
  recRel_prettify2. cbn [size].
  repeat (lazymatch goal with |- context C [ @size ?a] => generalize (@size a);intro end).
  assert (H':c__encTM <= c__encTM) by easy.
  repeat setoid_rewrite Nat.max_lub_iff in H'.
  destruct H' as (H1&H2&H3&H4).
  repeat rewrite H1. repeat rewrite H2. repeat rewrite H3. lia.
Qed.

Instance regP_TM : encodableP flatTM.
Proof.
  exists c__encTM.
  eexists _. 
  eapply computesTime_timeLeq.
  2:now apply term_TM_enc.
  intros l _. split. 2:easy.
  cbn [fst]. reflexivity.
Qed.
