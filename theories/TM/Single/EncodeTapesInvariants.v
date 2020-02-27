From Undecidability.TM Require Import TM ProgrammingTools Single.EncodeTapes Single.StepTM.

Import Lia.

From Undecidability Require Shared.Prelim. 

(* MOVE START *)
Hint Rewrite filter_app : list.
Lemma filter_rev (A : Type) (f : A -> bool) (l : list A): filter f (rev l) = rev (filter f l).
Proof.
  induction l;cbn in *. easy. autorewrite with list. cbn;destruct f. all:cbn;now autorewrite with list;congruence.
Qed.
Hint Rewrite filter_rev : list. 
(* MOVE END*)




Lemma encode_tape_invariants sig t0 :
  t0 = (@niltape _)
  \/ exists b__L b__R t, encode_tape t0 = LeftBlank b__L :: t ++[RightBlank b__R]
               /\ (forall x, x el t -> isSymbol x = true)
               /\ length (filter (@isMarked sig) (encode_tape t0)) = 1
               /\ t <> nil.
Proof.
  assert (H' : forall l x, x el map UnmarkedSymbol l -> (@isSymbol sig) x = true).
  { intros ? ? (?&<-&?)%in_map_iff. easy. }
  assert (H1' : forall l, filter (@isMarked sig) (map UnmarkedSymbol l) = []). 1:{induction l;cbn. all:easy. }
  
  destruct t0;cbn. now left.
  all:right. all:eexists _,_.
  3:eexists (_++[_]++_).  2:eexists (_++[_]). 1:eexists (_::_).
  all:split;[cbn;autorewrite with list;reflexivity | ].
  all:cbn in *;repeat setoid_rewrite in_app_iff;cbn. all:split;[now intuition (subst;eauto 3) | ].
  all:repeat (repeat rewrite map_rev;autorewrite with list;cbn).
  all:repeat rewrite H1'. all:split;[easy | ]. all:now length_not_eq.
Qed.



Lemma encode_tape_invariants_partial sig (x:tape sig) b t t__R:
  encode_tape x = LeftBlank b :: t ++t__R
  -> (forall x, x el t  -> isSymbol x = true)
  -> (exists init__R b',
      t__R = init__R++[RightBlank b']
      /\ (forall c , c el init__R -> isSymbol c = true))
      /\ (length (filter (@isMarked _) (t__R++t++[LeftBlank b])) = 1)
      /\ length (t++t__R) > 1.
Proof.
  destruct (encode_tape_invariants x) as [-> | (b__L&b__R&t'&Hx&Hsymb&Hmarked&Hnnil)].
  {cbn;congruence. }
  rewrite Hx. intros [= <- Ht'] Hall.
  assert (H__R : t__R <> []). 1:{ destruct t__R. 2:easy. rewrite app_nil_r in Ht'. subst t. ediscriminate (Hall (RightBlank _)). now eauto. }
  apply exists_last in H__R as (init__R&last__R&->). 
  rewrite !app_assoc in Ht';apply Prelim.last_app_eq in Ht' as [-> [= <-]]. 
  split. 1:{ eexists _, _;split. reflexivity. intros. apply Hsymb. eauto. }
  destruct x;cbn in Hx,Hmarked;autorewrite with list in Hmarked,Hx;revert Hx. easy.
  all:intros [= <- H];revert H.
  2:rewrite (app_comm_cons' _ _ (UnmarkedSymbol _)).
  all:rewrite ?app_comm_cons, <- !app_assoc_reverse. all:intros [H <-]%Prelim.last_app_eq;revert H.
  all:intros H%(f_equal (fun l => length (filter (isMarked (sig:=sig)) l) )).
  all:repeat (autorewrite with list in Hmarked,H|-*;cbn in Hmarked,H|-* ).
  all:split;[ | now destruct t;[destruct init__R| ];cbn in *;try congruence;nia].
  all:nia.
Qed.

Lemma invert_symbols_0_marked sig t:
  length (filter (@isMarked sig) t ) = 0
  -> (forall x, x el t -> isSymbol x = true)
  -> exists s : list sig, t = map UnmarkedSymbol s.
Proof.
  induction t. now eexists [].
  cbn. intros H1 H2. destruct a eqn:H';cbn in *.
  1,2,3:now specialize (H2 a);subst a;discriminate H2;eauto.
  -nia.
  -edestruct IHt as (?&->). 3:now eexists (_::_). all:eauto;easy.
Qed.

Lemma invert_symbols_1_marked sig t:
  length (filter (@isMarked sig) t ) = 1
  -> (forall x , x el t -> isSymbol x = true)
  -> exists s1 c (s2 : list sig), t = map UnmarkedSymbol s1 ++ (MarkedSymbol c :: map UnmarkedSymbol s2).
Proof.
  induction t. now inversion 1.
  cbn. intros H1 H2. destruct a eqn:H';cbn in *.
  1,2,3:now specialize (H2 a);subst a;discriminate H2;eauto.
  -edestruct @invert_symbols_0_marked with (t:=t) as (?&->).  1,2:eauto;easy.
   eexists [],_,_. reflexivity.
  -edestruct IHt as (?&?&?&->). 3:now eexists (_::_),_,_. all:eauto;easy.
Qed.
