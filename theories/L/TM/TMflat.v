From Undecidability Require Import TM.Util.TM_facts.
Require Import Undecidability.Shared.Libs.PSL.FiniteTypes.

(** A firstorder encoding and the connection to an arbitrary TM *)
Inductive flatTM : Type :=
  { sig : nat;
    tapes : nat;
    states : nat;    
    trans : list ((nat * list (option nat)) * (nat * list (option nat * move)));
    start : nat;
    halt : list bool
  }.

Inductive isFlatteningTransOf {st sig : finType} {n}
          (f:list (nat * list (option nat) * (nat * list (option nat * move))))
          (f': st * Vector.t (option sig) n -> st * Vector.t (option sig * move) n): Prop :=
  mkIsFlatteningTransOf
    (R__sound :
       (forall s s' v v', (((s,v),(s',v')) el f ->
                     ((exists s0 s0' v0 v0', ( f' (s0,v0) = (s0', v0')
                                          /\ s = index s0
                                          /\ s' = index s0'
                                          /\ v = map (option_map index) (Vector.to_list v0)
                                          /\ v' = map (map_fst (option_map index)) (Vector.to_list v0')))))))
    (R_complete : (forall s0 v0, let (s0',v0') := f' (s0,v0)
                             in ((index s0,map (option_map index) (Vector.to_list v0))
                                 ,(index s0',map (map_fst (option_map index)) (Vector.to_list v0'))) el f
                                \/ (s0=s0' /\ v0' = Vector.const (None,TM.Nmove) n)))
  : isFlatteningTransOf f f'.

Inductive isFlatteningHaltOf {st:finType} (f : list bool) (f' : st -> bool) : Prop :=
  mkIsFlatteningHaltOf
    (R__halt : forall (p:st),
        nth (index p) f false = f' p) : isFlatteningHaltOf f f'.

Inductive isFlatteningTMOf {sig' n} (M:flatTM) (M': TM sig' n) : Prop :=
  mkIsFlatteningTMOf
    (eq__tapes : tapes M = n)
    (eq__sig : sig M = |elem sig'|)
    (eq__states : (states M) = |elem (TM.state M')| )
    (R__trans : isFlatteningTransOf (trans M) (TM.trans (m:=M')))
    (eq__start : start M = index (TM.start M'))
    (R__halt : isFlatteningHaltOf (halt M) (TM.halt (m:=M')))
  : isFlatteningTMOf M M'.

Inductive isFlatteningTapesOf {sig : finType} {n}: list (tape nat) ->  Vector.t (tape sig) n -> Prop :=
  mkIsFlatteningTapeOf t : isFlatteningTapesOf (Vector.to_list(mapTapes index t)) t.


Lemma isFlatteningTapesOf_iff (sig : finType) (n : nat) y (t:Vector.t (tape sig) n):
  isFlatteningTapesOf y t <-> y = (Vector.to_list (mapTapes index t)).
Proof.
  split. now inversion 1. intros ->;easy.
Qed.

Definition mconfigFlat :Type := nat * list (tape nat).
Inductive isFlatteningConfigOf {st sig : finType} {n}: mconfigFlat -> mconfig st sig n -> Prop :=
  mkisFlatteningConfigOf t c'  (Ht:isFlatteningTapesOf t c'.(ctapes))
  : isFlatteningConfigOf (index c'.(cstate),t) c'.


Lemma isFlatteningConfigOf_iff {st sig : finType} n c (c' : mconfig st sig n):
  isFlatteningConfigOf c c' <-> exists t, isFlatteningTapesOf t c'.(ctapes) /\ c = (index c'.(cstate),t).
Proof.
  split. inversion 1;subst. eauto. intros (?&?&->). easy.
Qed.
