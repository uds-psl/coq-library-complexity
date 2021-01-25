From Undecidability Require Import TM.Util.TM_facts TM.Util.Relations.
From Undecidability.L Require Import LM_heap_def.

Set Default Proof Using "Type".
Require Import FunInd.

Lemma lookup_el H alpha x c: lookup H alpha x = Some c -> exists beta, Some (c,beta) el H.
Proof.
  induction x in alpha, c|-*.
  all:cbn. all:destruct nth_error as [[[] | ]| ] eqn:eq.
  all:intros [= eq'].
  1:subst.
  all:eauto using nth_error_In.
Qed.

Section Analysis.


  (*Variable s : term.*)
 (* Hypothesis cs : closed s.*)
  Variable T V : list HClos.
  Variable H H__init: list HEntr.

  Lemma jumpTarget_eq c c0 c1 c2: jumpTarget 0 c0 c = Some (c1,c2) -> c1++[retT]++c2=c0++c.
  Proof.
    generalize 0 as k. 
    induction c as [ |[]] in c1,c2,c0|-*;cbn. congruence.
    all:intros ? H'.
    4:destruct k;[inv H';congruence| ].
    all:apply IHc in H'. 
    all:autorewrite with list in *.
    all:now cbn in *. 
  Qed.


  Lemma tailRecursion_incl P alpha T': tailRecursion (alpha,P) T' <<= (alpha,P)::T'.
  Proof.
    destruct P as [ |[]];cbn. all:eauto.
  Qed.

  Lemma tailRecursion_length P alpha T': | tailRecursion (alpha,P) T' | <= 1+ length T'.
  Proof.
    destruct P as [ |[]];cbn. all:eauto.
  Qed.

  
  Variable i : nat.

  Variable P0 : Pro.
  Hypothesis R: pow step i ([(0,P0)],[],H__init) (T,V,H).
  Hypothesis empty_H__init: forall c, c el H__init -> c = None.

  Import Lia.
  
  Lemma size_clos P a : ((a,P) el (T++V) -> sizeP P <= sizeP P0 /\ a <= length H /\ largestVarP P <= largestVarP P0)
                        /\ (forall beta, Some ((a,P),beta) el H -> sizeP P <= sizeP P0 /\ a <= length H /\ beta <= length H /\ largestVarP P <= largestVarP P0).
  Proof using empty_H__init R.
    unfold sizeP.
    induction i in T,V,H,R,P,a|-*.
    -inv R. split.
     +intros [[= <- <-]|[]].
      eauto using Nat.le_0_l.
     +intros ? ?%empty_H__init. easy.
    -replace (S n) with (n + 1) in R by lia. apply pow_add in R. destruct R as [[[T' V'] H'] [R1 R2]].
     specialize (IHn _ _ _ R1).
     eapply rcomp_1 in R2.
     split.
     +intros Hel.
      apply in_app_or in Hel. 
      inv R2.
      *apply jumpTarget_eq in H2.  cbn in H2;inv H2.
       destruct Hel as [H1|[[= <- <-] | ]].
       apply tailRecursion_incl in H1 as [[= <- <-]| ].
       
       all:repeat (autorewrite with list in *;cbn in * ).
       1:specialize (proj1 (IHn _ a0) ltac:(eauto)).
       3:specialize (proj1 (IHn _ a0) ltac:(eauto)).
       
       1,3:repeat (autorewrite with list in *;cbn in * ).

       3:specialize (proj1 (IHn P a) ltac:(eauto)).
       4:specialize (proj1 (IHn P a) ltac:(eauto)).

       1,2:intros (?&?&H');rewrite maxl_app in H';cbn in H';unfold largestVarP in *.

       all:split;[|split];try lia.
      * inv H2.
        destruct Hel as [[[= <- <-] | ]| ].
        2:apply tailRecursion_incl in H as [[= <- <-]| ].
        all:repeat ((try setoid_rewrite in_app_iff in IHn);cbn in IHn).
        --specialize (proj1(IHn Q _) ltac:(eauto)).
          repeat (autorewrite with list in *;cbn in * ).
          now lia.
        --specialize (proj1(IHn _ a0) ltac:(eauto)).
          repeat (autorewrite with list in *;cbn in * ). unfold largestVarP in *.
          now lia.
       --specialize (proj1(IHn P a) ltac:(eauto)).
         autorewrite with list in IHn.
         repeat (autorewrite with list in *;cbn in * ).
         now lia.
       --specialize (proj1(IHn P a) ltac:(eauto)).
         autorewrite with list in IHn.
         repeat (autorewrite with list in *;cbn in * ).
         try now lia.
      * destruct Hel as [ |[-> | ]].
        apply tailRecursion_incl in H0 as [[= <- <-]| ].
        all:repeat ((try setoid_rewrite in_app_iff in IHn);cbn in IHn).
        --specialize (proj1(IHn _ a0) ltac:(eauto)).
          repeat (autorewrite with list in *;cbn in * ). unfold largestVarP in *.
          now lia.
        --specialize (proj1(IHn _ a) ltac:(eauto)).
          repeat (autorewrite with list in *;cbn in * ).
          now lia.
        --apply lookup_el in H2 as (?&?).
          specialize (proj2 (IHn _ a) _ ltac:(eauto)).
          repeat (autorewrite with list in *;cbn in * ).
          now lia.
        --specialize (proj1(IHn _ a) ltac:(eauto)).
          repeat (autorewrite with list in *;cbn in * ).
          now lia.
     +intros ? Hel. inv R2.
      1,3:now apply IHn.
      inv H2.
      apply in_app_or in Hel.
      edestruct Hel as [ |[[= -> ->]|[]]].
      1:specialize (proj2(IHn _ a) _ ltac:(eauto)).
      all:autorewrite with list;cbn.
      now lia.
      1:specialize (proj1(IHn _ a) ltac:(eauto)).
      1:specialize (proj1(IHn _ beta) ltac:(eauto)).
      lia.
  Qed.

  Lemma length_H : length H <= length H__init+i.
  Proof using empty_H__init R.
    induction i in T,V,H,R|-*.
    -inv R. cbn;lia.
    -replace (S n) with (n + 1) in R by lia.
     apply pow_add in R. destruct R as [[[T' V'] H'] [R1 R2]].
     specialize (IHn _ _ _ R1).
     eapply rcomp_1 in R2.
     inv R2.
     1,3:now lia.
     inv H2. autorewrite with list. cbn. lia.
  Qed.  

  Lemma length_TV : length T + length V <= 1+i.
  Proof using empty_H__init R.
    induction i in T,V,H,R|-*.
    -inv R. cbn;lia.
    -replace (S n) with (n + 1) in R by lia.
     apply pow_add in R. destruct R as [[[T' V'] H'] [R1 R2]].
     specialize (IHn _ _ _ R1).
     eapply rcomp_1 in R2.
     inv R2.
     all:cbn in *.
     specialize (tailRecursion_length P' a T0). 
     1,2:specialize (tailRecursion_length P a T0). all:unfold tailRecursion.
     1,2:nia.
     destruct P. nia. cbn. nia.
  Qed.
  
(* Damit: länge eines zustandes beschränkt durch (i+i)*(3*(i+1)+2*|s|)*)
  

End Analysis.
