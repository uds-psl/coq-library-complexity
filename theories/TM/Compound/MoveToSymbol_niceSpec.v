From Undecidability Require Import TM.Util.Prelim.
From Undecidability Require Import TM.Util.TM_facts TM.Compound.MoveToSymbol.

Require Import ssrbool Lia.

Lemma last_not_default X (d d':X) A :
  A <> [] -> last A d = last A d'.
Proof. induction A. easy. destruct A;cbn. easy. intros ?. now apply IHA. Qed.


Lemma removelast_as_tail X (x:list X): removelast x = rev (tail (rev x)).
Proof.
  rewrite tl_rev. now autorewrite with list.
Qed.

Local Arguments removelast : simpl nomatch.
Local Arguments last : simpl nomatch.

(** TIPP: Look in ./Copy.v **)
(** I have no Idea anymore why i called this nicer ... *)

Definition MoveToSymbol_Rel_nice (sig':finType) (f:sig' -> bool) (g:sig' -> sig') t t' := 
  ((current t = None /\ t = t')
   \/ (exists t__L c t__R1 t__R2,
         t = midtape t__L c (t__R1++t__R2)
         /\ (forall x, x el (removelast (c::t__R1)) -> f x = false)
         /\ f (last (c::t__R1) c) = ssrbool.isSome (current t')
         /\ (t' = midtape (rev (map g (removelast (c::t__R1)))++t__L) (g (last (c::t__R1) c)) t__R2
            \/ (t' = rightof (g (last (c::t__R1) c)) (rev (map g (removelast (c::t__R1)))++t__L) /\ t__R2 = [])))).

Lemma MoveToSymbol_Fun_nice (sig':finType) (f:sig' -> bool) (g:sig' -> sig') t t' :
  MoveToSymbol_Fun f g t = t' <-> MoveToSymbol_Rel_nice f g t t'. 
Proof.
  remember (tape_local t) as A eqn:eqA.
  revert t t' eqA. unfold MoveToSymbol_Rel_nice.
  induction A using (size_induction (f:=@length sig'));intros t t' eqA.
  rewrite MoveToSymbol_Fun_equation. destruct current eqn:eq.
  2:{ split. now left. intros [ | H']. easy. destruct H' as (?&?&?&?&->&?). easy. }
  destruct f eqn:Hf.
  { destruct t;inv eq. all:cbn. split.
    -intros <-. right. eexists _,_,[],_.
     repeat split;eauto.
    -intros [ | (t__L&c&t__R1&t__R2&[= -> -> -> ]&Hfalse&Hc&H'')];[ easy | ].
     destruct t__R1 as [ | c__R t__R1].
     2:{exfalso. cbn in *. rewrite Hfalse in Hf;auto. }
     cbn in *. 
     destruct H'' as [-> | [-> -> ]]. all:cbn in *;now eauto + congruence.
  }
  destruct t. all:inv eq. destruct l0. all:cbn - [removelast].
  all:rewrite H;[ | | reflexivity];[cbn | cbn;nia].
  - cbn. split.
    +intros [(_&<-)| (?&?&?&?&[=]&?)];[]. right.
     eexists _,_,[],[]. split;[reflexivity| ]. split;[easy| ]. unfold last, removelast;cbn. eauto. 
    +intros [([=]&?)|(t__L&c&t__R1&t__R2&[= <- <- H__nil]&Hfalse&Hc&H'')];[].
     destruct t__R1;[ |now inv H__nil]. destruct t__R2;[ |now inv H__nil]. clear H__nil.
     cbn in H''|-*. destruct H'' as [-> | [-> _ ]]. 2:now left. now unfold last in Hc;cbn in Hc;congruence.
  -eapply Morphisms_Prop.or_iff_morphism. easy.
   split. all:intros (t__L&c&t__R1&t__R2&Heq&Hfalse&Hc&H');revert Heq.
   +intros [= <- -> ->]. eexists _,_,(_::_),_. split. reflexivity.
    cbn. split. now intros ? [-> | ];eauto.
    autorewrite with list in |-*;cbn. erewrite last_not_default. split;now eauto. easy.
   +intros [= -> -> Heq]. destruct t__R1.
    {cbn in *. destruct H' as [ -> | [-> ->]]. all: now cbn in *;congruence. }
    revert Heq;intros [= -> ->].
    eexists (_::_),_,_,_. split. reflexivity. cbn in *.
    split. now eauto. autorewrite with list in H';cbn. erewrite last_not_default. 2:easy. split;now eauto.
Qed.

Lemma MoveToSymbol_Fun_is_rel (sig':finType) (f:sig' -> bool) (g:sig' -> sig') t :
  MoveToSymbol_Rel_nice f g t (MoveToSymbol_Fun f g t).
Proof.
  now rewrite <- MoveToSymbol_Fun_nice.
Qed.
