From Undecidability Require Import TM.Util.TM_facts TM.Util.Relations.
From Undecidability.L Require Import LM_heap_def UnfoldClos Programs.
From Complexity.L Require Import LambdaDepth.

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

Definition boundHeap (H:Heap) maxPro maxVar maxDepth:=
  (forall a P beta, Some ((a,P),beta) el H ->
    sizeP P <= maxPro /\ a <= length H /\ beta <= length H /\ lambdaDepthP 1 P <= maxDepth/\ largestVarP P <= maxVar ).

Definition unfoldTailRecStep_sizes (H:Heap) maxPro maxVar maxDepth: list (HClos * nat) -> Prop :=
  fun stack =>
    forall a P k, ((a,P),k) el stack
      -> sizeP P <= maxPro
      /\ a <= length H
      /\ largestVarP P <= maxVar
      /\ lambdaDepthP k P <= maxDepth + 1.

Lemma unfoldTailRecStep_sizes_correct' H maxPro maxVar maxDepth a k s P s' stack stack' res fuel :
  boundHeap H maxPro maxVar maxDepth
  -> LM_heap_correct.unfolds H a k s s'
  -> ARS.pow (fun a b => inl b = unfoldTailRecStep H a) fuel ((a,compile s++P,k)::stack,res) stack'
  -> (sizeP (compile s++P) <= maxPro /\ a <= length H /\ largestVarP (compile s++P) <= maxVar /\ lambdaDepthP k ((compile s++P)) <= maxDepth)
  -> (unfoldTailRecStep_sizes H maxPro maxVar maxDepth stack)
  -> (exists fuel', fuel' < fuel /\ 
      ARS.pow (fun a b => inl b = unfoldTailRecStep H a) fuel' ((a,P,k)::stack,rev (compile s')++res) stack')
     \/ unfoldTailRecStep_sizes H maxPro maxVar maxDepth (fst stack').
Proof.
  intros HH.
  revert a k s P s' stack stack' res.
  induction fuel as [fuel IH] using lt_wf_ind.
  intros ? ? ? ? ? ? ? ? Hunf HR Hhd Htl.
  destruct fuel as [|fuel].
  {hnf in HR. subst stack'. cbn [fst]in *. right. intros ? ? ? [[= <- <- <-]|]. all:now eauto. }
  change (S fuel) with (1+fuel) in *. eapply pow_add in HR as (stack''&Hstep%(rcomp_1)&HR).
  symmetry in Hstep. 
  induction Hunf in P,stack,Hstep,Hhd,Htl|-*. 1-3:cbn in Hstep.
  - destruct (Nat.leb_spec k n). now exfalso;nia.
    injection Hstep as [= <-]. left. eauto.
  - destruct (Nat.leb_spec k n). 2: now exfalso;nia.
    rewrite H1 in Hstep. injection Hstep as [= <-]. inv H2. inv Hunf.
    destruct (lookup_el H1) as (?&Hel). hnf in HH. specialize HH with (1:= Hel) as (?&?&?&?&?).
    specialize IH with (2:= H5) (P:=[]) as IH'. rewrite app_nil_r in IH'. specialize IH' with (2:=HR) as [(fuel'&?&IH')|IH'].
    + nia.
    + specialize (lambdaDepthP_min 1 (compile s0)). repeat simple apply conj;try nia.
    + hnf. intros ? ? ? [[= <- <- <-]|]. 2:now eauto. 
      specialize (lambdaDepthP_min k P).  
      cbn - [max] in Hhd|-*. repeat simple apply conj;try nia.
    + destruct fuel' as [|fuel'].
      {
        hnf in IH'. subst stack'. right. hnf;cbn. intros ? ? ? [[= <- <- <-] | [[= <- <- <-]| ]].
        3:now eauto. { cbn. unfold sizeP in *. nia. }
        cbn - [max] in Hhd|-*. unfold sizeP, largestVarP in *. specialize (lambdaDepthP_min k P). repeat simple apply conj;try nia.
      }
      change (S fuel') with (1+fuel') in *. eapply pow_add in IH' as (stack''&Hstep%(rcomp_1)&IH').
      cbn in Hstep. injection Hstep as [=->].
      destruct fuel' as [|fuel'].
      {
        hnf in IH'. subst stack'. right. hnf;cbn. intros ? ? ? [[= <- <- <-]| ].
        2:now eauto.
        cbn - [max] in Hhd|-*. unfold sizeP, largestVarP in *. specialize (lambdaDepthP_min k P). repeat simple apply conj;try nia.
      }
      change (S fuel') with (1+fuel') in *. eapply pow_add in IH' as (stack''&Hstep%(rcomp_1)&IH').
      cbn in Hstep. injection Hstep as [=->].
      cbn. autorewrite with list;cbn. left;eexists;split. 2:eassumption. nia.
    +now right.
  - injection Hstep as [= <-]. cbn in Hhd. rewrite <- app_assoc in HR,Hhd.
    specialize IH with (2:=Hunf) (3:=HR) as [(fuel'&?&IH')|IH'].
    + nia.
    + cbn in Hhd|-*. unfold sizeP,largestVarP. nia.
    + easy.
    + cbn in Hhd|-*. autorewrite with list in Hhd|-*. rewrite lambdaDepthP_compile', maxl_app in Hhd. cbn - [max]in Hhd|-*.
      destruct fuel' as [|fuel'].
      {
        hnf in IH'. subst stack'. right. hnf;cbn. intros ? ? ? [[= <- <- <-]| ].
        2:now eauto.
        cbn - [max] in Hhd|-*. unfold sizeP in *. repeat simple apply conj;try nia.
      }
      change (S fuel') with (1+fuel') in *. eapply pow_add in IH' as (stack''&Hstep%(rcomp_1)&IH').
      cbn in Hstep. injection Hstep as [=->].
      left;do 2 eexists. 2:eassumption. nia. 
    + easy.
  - cbn [compile] in Hstep,Hhd. rewrite <- !app_assoc in Hstep,Hhd.
    edestruct IHHunf1  as [(fuel'&?&IH')|IH']. 3:eassumption.
    1,2,4:easy.
    cbn in Hhd|-*. unfold sizeP,largestVarP in Hhd. autorewrite with list in Hhd|-*.  
    rewrite !lambdaDepthP_compile', !maxl_app in Hhd. cbn - [max]in Hhd|-*.
    specialize IH with (3:=IH') as [(fuel''&?&IH'')|IH'']. 2:eassumption.
    + nia.
    + cbn in Hhd|-*. unfold sizeP,largestVarP in Hhd|-*. autorewrite with list. rewrite !lambdaDepthP_compile', !maxl_app;cbn.
      repeat simple apply conj;try nia.
    + easy.
    + destruct fuel'' as [|fuel''].
      {
        hnf in IH''. subst stack'. right. hnf;cbn. intros ? ? ? [[= <- <- <-]| ].
        2:now eauto.
        cbn - [max] in Hhd|-*. unfold sizeP in *. repeat simple apply conj;try nia.
      }
      change (S fuel'') with (1+fuel'') in *. eapply pow_add in IH'' as (stack'''&Hstep'%(rcomp_1)&IH''').
      cbn in Hstep. injection Hstep' as [=->].
      left;do 2 eexists. 2:eassumption. nia. 
    + easy.
Qed.

Lemma unfoldTailRecStep_sizes_correct H maxPro maxVar maxDepth a k s s' stack' res fuel :
  boundHeap H maxPro maxVar maxDepth
  -> LM_heap_correct.unfolds H a k s s'
  -> ARS.pow (fun a b => inl b = unfoldTailRecStep H a) fuel ([(a,compile s,k)],res) stack'
  -> sizeP (compile s) <= maxPro /\ a <= length H /\ LargestVar.largestVar s<= maxVar /\ k + lambdaDepth s <= maxDepth
  -> unfoldTailRecStep_sizes H maxPro maxVar maxDepth (fst stack').
Proof.
  intros H1 H2 H3 ?.
  edestruct unfoldTailRecStep_sizes_correct' with (P:=@nil Tok) (1:=H1) (2:=H2)as [(fuel'&?&H')|H'].
  -rewrite app_nil_r. eassumption.
  -rewrite app_nil_r. rewrite lambdaDepthP_compile, largestVar_compile. easy.
  -easy.
  -destruct fuel'.
   { hnf in H'. subst stack';cbn. hnf. intros ? ? ? [[= <- <- <-]|[]];cbn. unfold sizeP in *. nia. }
   change (S fuel') with (1+fuel') in *. eapply pow_add in H' as (stack''&Hstep%(rcomp_1)&H').
   cbn in Hstep. injection Hstep as [=->].
   destruct fuel'.
   +hnf in H'. subst stack';cbn. hnf. easy.
   +exfalso.  change (S fuel') with (1+fuel') in *. eapply pow_add in H' as (stack''&Hstep%(rcomp_1)&_). easy.
  -easy.
Qed.

From Complexity.L.AbstractMachines Require Import SizeAnalysisStep SubtermProperty.


Lemma abstractMachine_boundHeap k s a s0 H :
  ARS.pow step k (LM_heap_def.init s) ([], [(a, compile s0)], H) -> 
  boundHeap H (sizeP (compile s)) (LargestVar.largestVar s) (lambdaDepth s).
Proof.
  intros H'. unfold boundHeap. intros ? ? ? HH.
  specialize subterm_property with (1:=H') as (_&_&Hsub). specialize Hsub with (1:=HH) as (?&?&tmp);cbn in tmp;subst P.
  specialize size_clos with (1:=H') as (_&Hlength). easy. specialize Hlength with (1:=HH) as (?&?&?&?).
  repeat simple apply conj;try eassumption.
  -apply lambdaDepth_subterm in H0 as <-. cbn. now rewrite lambdaDepthP_compile.
  -now rewrite <- largestVar_compile.
Qed.

Lemma abstractMachine_boundRes k s a s0 H :
  ARS.pow step k (LM_heap_def.init s) ([], [(a, compile s0)], H) -> 
  sizeP (compile s0) <= sizeP (compile s) /\
  a <= | H | /\
  LargestVar.largestVar s0 <= LargestVar.largestVar s /\
  1 + lambdaDepth s0 <= lambdaDepth s.
Proof.
  intros H'. 
  specialize subterm_property with (1:=H') as (_&Hsub&_). specialize Hsub as (?&?&tmp). now left.
  apply compile_inj in tmp as <-.
  specialize size_clos with (1:=H') as (Hlength&_). easy. specialize Hlength as (?&?&?). now left.
  repeat simple apply conj;try eassumption.
  -now rewrite <- !largestVar_compile.
  -apply lambdaDepth_subterm in H0 as <-. cbn. easy.
Qed.


