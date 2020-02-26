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
               /\ length (filter (@isMarked sig) (encode_tape t0)) = 1.
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
  all:repeat rewrite H1'. all:now cbn.
Qed.



Lemma encode_tape_invariants_partial sig (x:tape sig) b t t__R:
  encode_tape x = LeftBlank b :: t ++t__R
  -> (forall x, x el t  -> isSymbol x = true)
  -> t__R <> []
    /\ (forall c , c el tail (rev t__R) -> isSymbol c = true)
    /\ (exists b', head (rev t__R) = Some (RightBlank b'))
    /\ (length (filter (@isMarked _) (t__R++t++[LeftBlank b])) = 1)
    /\ length (t++t__R) > 1.
Proof.
  destruct (encode_tape_invariants x) as [-> | (b__L&b__R&t'&Hx&Hsymb&Hmarked)].
  {cbn;congruence. }
  rewrite Hx. intros [= <- Ht'] Hall.
  destruct t__R eqn:Ht__R in |-. 1:{ subst. rewrite app_nil_r in Ht'. subst t. ediscriminate (Hall (RightBlank _)). now eauto. }
  split. now congruence.
  destruct (rev t__R) eqn: H__rev. 1:{ subst t__R. length_not_eq in H__rev. }
  cbn in *.
  rewrite <- rev_involutive with (l:=t__R) in Ht'. rewrite H__rev in Ht';cbn in Ht'.
  rewrite app_assoc in Ht'. apply Prelim.last_app_eq in Ht' as (->&<-).        
  split. 2:split. 3:split.
  -setoid_rewrite in_app_iff in Hsymb. setoid_rewrite <- in_rev in Hsymb. eauto.
  -eauto.
  -apply (f_equal (@rev _)) in H__rev. rewrite rev_involutive in H__rev.  rewrite H__rev. cbn.
   rewrite Hx in Hmarked. cbn in *.  autorewrite with list in *;cbn in *.
   destruct b__L,b__R;cbn in *. all:autorewrite with list in *;cbn in *. all:nia.
  -subst t__R. destruct t. 2:now autorewrite with list;cbn;nia.
   cbn in *. destruct l. 2:cbn;nia.
   inv H__rev.
   destruct x;inv Hx. all: length_not_eq in H1. 
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
