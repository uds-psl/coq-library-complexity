From Undecidability.TM Require Import Copy WriteValue CaseList CasePair SizeBounds.
(* From Complexity.TM Require Code.Decode Code.DecodeList. *)
(* From Undecidability.TM Require Import TM SizeBounds. *)
From Undecidability.L.Complexity  Require Import UpToCNary.
(* From Complexity.NP.L  Require Import LMGenNP. *)
From Undecidability.L.AbstractMachines Require Import FlatPro.Programs LM_heap_correct LM_heap_def.
From Complexity.L.AbstractMachines Require Import (*FlatPro.Computable.Compile *) SizeAnalysisUnfoldClos LambdaDepth.
(* Unset Printing Coercions. *)
From Undecidability.TM.L Require Import Eval UnfoldClos.
(* From Coq Require Import Lia Ring Arith. *)
(* From Undecidability.TM.L Require Import Boollist_to_Enc. *)
From Complexity.L.AbstractMachines.TM_LHeapInterpreter Require Import LMBounds LMBounds_Loop.

(* Import DecodeList Decode. *)
(* Import ProgrammingTools Combinators M_LHeapInterpreter. *)

Import List List.ListNotations.

Set Keyed Unification.
Arguments c__leUpToC {_ _ _} _.

Lemma Private_UnfoldClos_steps_step_nice' :
  { c | forall (H:Heap) maxPro maxVar maxDepth stack, boundHeap H maxPro maxVar maxDepth
         -> unfoldTailRecStep_sizes H maxPro maxVar maxDepth stack
         -> Private_UnfoldClos.steps_step H stack <= c * (Code.size H * S maxVar + maxPro + maxDepth + 1)}.
Proof.
  evar (c:nat). exists c.
  intros H maxPro maxVar maxDepth stack HH Hstack.
  remember (Code.size H) as sH.
  assert (Hlength:length H <= sH)by (subst;rewrite Encode_Heap_hasSize_ge_length,Code.Encode_list_hasSize;easy ).
  assert (HsH : 1 <= sH) by (subst;apply Encode_Heap_hasSize_ge1).
  destruct stack as [|[[a P] k] stack]. now apply Nat.le_0_l.
  hnf in Hstack. specialize Hstack with (1:=or_introl eq_refl) as H'. destruct H' as (HP&Ha&Hk&Hvar).
  unfold Private_UnfoldClos.steps_step.
  destruct P as [|t P].
  - cbn in Hvar. 
   unfold Reset_steps at 1 2 3. rewrite !Code.Encode_nat_hasSize. rewrite Ha at 1. rewrite Hvar.
   destruct stack as [|[[a' P']k']];cbn [fst snd].
   all:cbv [CaseList_steps_nil Reset_steps  CaseList_steps Code.encode Alphabets.Encode_Prog Code.Encode_list Code.encode_list Alphabets.Encode_Com].
   all:change (Code.size []) with 1.
   all:cbn [length]. all:ring_simplify. 
   +enough (68  <= c) by nia. shelve.
   +specialize (Hstack a' P' k') as (HP'&Ha'&Hk'&Hvar'). easy.
    unfold CaseList_steps_cons ,CasePair_steps,Translate_steps.
    repeat (rewrite Code.Encode_pair_hasSize;unfold Code.Encode_pair_size).
    rewrite !Code.Encode_nat_hasSize. rewrite size_le_sizeP,HP',Ha'. assert (k'<= maxDepth + 1) as -> by now rewrite lambdaDepthP_min.
    ring_simplify. enough (248 <= c) by nia. shelve.
  - unfold CaseList_steps,CaseList_steps_cons.
    destruct t.
    2-4:cbv - [length "+" "*" c];cbn [length];ring_simplify;enough (103 <= c) by nia;shelve.
    assert (Hn : n<= maxVar) by now cbn in Hk.
    rewrite LMBounds.size_Var;cbv [CaseCom.CaseCom_steps CopyValue_steps ].
    rewrite UpToC_le. do 3 rewrite Code.Encode_nat_hasSize. assert (k<= maxDepth+ 1) as Hk2 by now rewrite lambdaDepthP_min.
    rewrite Hk2 at 1 2. rewrite Hn at 1 2.
    destruct (Nat.leb_spec k n).
    2:{
      unfold  CaseCom.Constr_varT_steps, Constr_cons_steps , Reset_steps.
      rewrite LMBounds.size_Var;cbv [CaseCom.CaseCom_steps CopyValue_steps ].
      rewrite Code.Encode_nat_hasSize. unshelve erewrite ( _ : n - k <= maxVar). nia.
      change (Pos.to_nat 3) with 3.
      rewrite Hn. ring_simplify. enough (c__leUpToC (projT1 NatSub.Subtract_SpecT) +245 <= c) as H1 by (rewrite <- H1; nia ). shelve.
    }
    destruct lookup as [[]|]eqn: Hlookup.
    2:{ 
      unfold  CaseCom.Constr_varT_steps, Constr_cons_steps , Reset_steps.
      rewrite Code.Encode_nat_hasSize. rewrite Hn.
       ring_simplify. enough (c__leUpToC (projT1 NatSub.Subtract_SpecT) +215 <= c)as H1 by (rewrite <- H1; nia ). shelve.
     }
     specialize (proj2_sig LMBounds.LM_Lookup_nice.Lookup_steps_nice H a (n-k)) as H'. hnf in H'.
     rewrite H',!Code.Encode_nat_hasSize.
     rewrite LM_Lookup_nice.heap_greatest_address_leq, heap_greatest_address2_bound with (c:= length H).
     2:{ intros [] ? ?. now eapply HH. }
     rewrite Ha at 1 2. rewrite Max.max_idempotent.
     cbv [Cons_constant.Cons_constant.time CaseNat.Constr_S_steps].
     set (tmp:=Code.size retT);cbv in tmp;subst tmp.
     unfold CaseList_steps_cons ,CasePair_steps,Constr_pair_steps ,Translate_steps,MoveValue_steps,Constr_cons_steps,Reset_steps,WriteValue_steps  .
     cbn [fst snd].
     repeat (rewrite Code.Encode_pair_hasSize;unfold Code.Encode_pair_size).
     rewrite size_le_sizeP. unshelve erewrite (_ : sizeP (retT :: P) <= maxPro). {cbv [sizeP] in *;cbn in *;nia. }
     eapply lookup_el in Hlookup as (?&Hlookup).
     eapply HH in Hlookup as (Hlk1&Hlk2&Hlk3&Hlk4).
     rewrite !Code.Encode_nat_hasSize.
     rewrite Hlk2. change (Pos.to_nat 11) with 11.
     unshelve erewrite ( _ : n - k <= maxVar). nia. 
     rewrite Ha, Hk2,Hn.
     set (tmp:=Code.size lamT);cbv in tmp;subst tmp.
     rewrite Hlength, <- HeqsH,size_le_sizeP,Hlk1.
     assert (proj1_sig LM_Lookup_nice.Lookup_steps_nice * 3 + c__leUpToC (projT1 NatSub.Subtract_SpecT) + 570 <= c) as H1 by shelve.
     rewrite <- H1.
     Zify.zify;nia.
     Unshelve.
     9: unfold c;reflexivity. all:unfold c;lia.
Qed.

Import ZArith.
Lemma Private_UnfoldClos_steps_loop_nice' :
  { c | forall (H:Heap) maxPro maxVar maxDepth res s s' k a n, 
    boundHeap H maxPro maxVar maxDepth
    -> LM_heap_correct.unfolds H a k s s'
    -> sizeP (compile s) <= maxPro /\ a <= length H /\ LargestVar.largestVar s<= maxVar /\ k + lambdaDepth s <= maxDepth
   -> Private_UnfoldClos.steps_loop H n ([(a,compile s,k)],res) <= c * n * (Code.size H * S maxVar + maxPro + maxDepth + 1) }.
Proof.
  evar (c:nat). exists c.
  intros H maxPro maxVar maxDepth res s s' k a n HH Hunf Hs.
  remember  ([(a,compile s,k)],res) as stack' eqn:Htmp.
  assert (HR : exists fuel, ARS.pow (fun a b => inl b = UnfoldClos.unfoldTailRecStep H a) fuel stack' stack') by (exists 0;reflexivity).
  setoid_rewrite Htmp in HR at 1. clear Htmp.
  unfold Private_UnfoldClos.steps_loop. cbn.
  induction n in stack',res,HR|-*. now intros;apply Nat.le_0_l.
  erewrite (proj2_sig Private_UnfoldClos_steps_step_nice' _ _ _ _ _ HH).
  2:{ edestruct HR; eapply unfoldTailRecStep_sizes_correct. all:eassumption. }
  destruct UnfoldClos.unfoldTailRecStep as [[]|] eqn:Hstep.
  -rewrite IHn.
   2:{ destruct HR as (f&Hf). exists (f+1). eapply pow_add. eexists;split. eassumption. eapply (proj1 (rcomp_1 _ _ _)). easy. }
   [c]:exact (proj1_sig Private_UnfoldClos_steps_step_nice' + 1).
   subst c. nia.
  -unfold c. set (c':= Code.size _). set (c'':= proj1_sig _).
   ring_simplify.
   repeat rewrite <- PeanoNat.Nat.add_assoc;nia.
Qed.

Import TM.PrettyBounds.PrettyBounds.

Lemma Private_UnfoldClos_steps_nice' :
  { c | forall (H:Heap) maxPro maxVar maxDepth a k s s', 
  boundHeap H maxPro maxVar maxDepth
  -> LM_heap_correct.unfolds H a k s s'
  -> sizeP (compile s) <= maxPro /\ a <= length H /\ LargestVar.largestVar s<= maxVar /\ k + lambdaDepth s <= maxDepth
  ->Private_UnfoldClos.steps H a k s s' <= c*(L_facts.size s'+ 1) * (Code.size H * S maxVar + maxPro + maxDepth + 1)  }.
Proof.
  eexists ?[c]. intros. unfold Private_UnfoldClos.steps.
  erewrite (proj2_sig Private_UnfoldClos_steps_loop_nice' _ _ _ _ _ _).
  2,3,4:eassumption.
  {
  remember (size H * S maxVar + maxPro + maxDepth + 1) as c0 eqn:Hc0.
  [c]: exact (3*proj1_sig Private_UnfoldClos_steps_loop_nice' + 2 * WriteValue_steps 1 + 3). 
  set (c':=proj1_sig _);clearbody c'. lia.
  }
Qed.
  
Lemma UnfoldClos_steps_nice' :
  { c | forall (H:Heap) maxPro maxVar maxDepth a s t, 
  boundHeap H maxPro maxVar maxDepth
  -> LM_heap_correct.unfolds H a 1 s t
  -> sizeP (compile s) <= maxPro /\ a <= length H /\ LargestVar.largestVar s<= maxVar /\ 1 + lambdaDepth s <= maxDepth
  -> UnfoldClos.steps H (a,compile s) (L.lam t) <= c*(L_facts.size t + 1) * (Code.size H * S maxVar + maxPro + maxDepth + 1)  }.
Proof.
  evar (c:nat). eexists c. intros ? ? ? ? ? ? ? ? ? (Hs&Ha&Hvar&Hk). unfold UnfoldClos.steps.
  assert (Hlength:length H <= size H) by (rewrite Encode_Heap_hasSize_ge_length,Code.Encode_list_hasSize;easy ).
  rewrite decompile_correct.
  unfold CasePair_steps,Translate_steps.
  rewrite (correct__leUpToC (Rev.Rev_Append_steps_nice _)).
  repeat (rewrite Code.Encode_pair_hasSize;unfold Code.Encode_pair_size).
  rewrite !Code.Encode_nat_hasSize.
  cbn [L_facts.size fst].
  rewrite (proj2_sig Private_UnfoldClos_steps_nice' _),Ha,Hlength. 2-4:easy.
  remember (size H * S maxVar + maxPro + maxDepth) as c0 eqn:Hc0.

  set (tmp:=WriteValue_steps (size [retT]));cbv in tmp;subst tmp.
  set (tmp:=Cons_constant.Cons_constant.time lamT);cbv in tmp;subst tmp.
  set (tmp:=WriteValue_steps 2);cbv in tmp;subst tmp.
  rewrite !size_le_sizeP,!Hs.
  replace (sizeP (rev (compile t))) with (sizeP (compile t)).
  2:{ unfold sizeP. now rewrite map_rev,<- sumn_rev. }
  unfold sizeP;rewrite sizeP_size. ring_simplify.
  unshelve erewrite ( _ : size H <= c0);[nia|].   unshelve erewrite ( _ : maxPro <= c0);[nia|].
  [c]:exact (proj1_sig Private_UnfoldClos_steps_nice' + 6*c__leUpToC (Rev.Rev_Append_steps_nice Alphabets.Encode_Com) + 126). unfold c.
  cbn - ["+" "*"].
  set (x:=proj1_sig Private_UnfoldClos_steps_nice'). change (proj1_sig Private_UnfoldClos_steps_nice') with x.
  set (y:=c__leUpToC (Rev.Rev_Append_steps_nice Alphabets.Encode_Com)). ring_simplify. lia.
Qed.

Lemma EvalL_steps_nice' :
{ c | forall s k t Hcl Hr, @EvalL.steps s k t Hcl Hr
  <=(c) (k+1)*(k+L_facts.size s)* ( L_facts.size s * (k+1) + L_facts.size t * (LargestVar.largestVar s+ 1) ) }.
Proof.
  evar (c:nat). eexists c. intros ? ? ? ? ?.
  unfold EvalL.steps.
  destruct completenessTimeInformative as ((a&s')&H&(t'&Hrep&Hrep2)%reprC_elim&HR). cbn [fst snd] in *. inv Hrep.
  inv Hrep2.

  repeat (set (n:=WriteValue_steps _);cbv in n;subst n).
  set (n:=Reset_steps 0);cbv in n;subst n.
  set (n:=Constr_pair_steps 0);cbv in n;subst n.
  set (n:=Reset_steps []);cbv in n;subst n.
  unfold Translate_steps,CopyValue_steps,Reset_steps,Constr_cons_steps,CaseList_steps,CaseList_steps_cons .
  do 2 (rewrite Encode_pair_hasSize; unfold Encode_pair_size).
  set (size (X:=HAdd) 0);cbv in n; subst n.

  evar (c':nat). evar (tmp:nat).
  eapply dominatedWith_trans with (c:=c') (y:=tmp).
  ring_simplify. 2:unfold tmp;eapply dominatedWith_refl with (c:=1). 2:nia. 
  subst c'. subst tmp.

  unfold init in HR.


  unshelve eassert (Hclos:=SizeAnalysisStep.size_clos HR _). easy. cbn in Hclos. 
  unshelve eassert (HHlength:=SizeAnalysisStep.length_H HR _). easy. cbn - ["*"] in HHlength.

  specialize (proj2_sig UnfoldClos_steps_nice') as Hunf.
  set (c1:= proj1_sig _) in Hunf.  cbn beta in Hunf.
  specialize Hunf with (2:=H2).

  setoid_rewrite Hunf.
  2: now eapply abstractMachine_boundHeap.
  2: now eapply abstractMachine_boundRes.

  unshelve erewrite (_ : size a <= (3*k+1 + 1)).
  {
    rewrite Encode_nat_hasSize. transitivity (1 + length H). 2:now rewrite SizeAnalysisStep.length_H;try easy;cbn;nia.
    unshelve edestruct SizeAnalysisStep.size_clos with (1:=HR) as [(?&H'&?) _]. 3,4:cbn;easy. nia.
  }

  unshelve eassert (tmp:=proj2_sig Heap_size_nicer2' _ _ _ _  _ HR); hnf in tmp; rewrite tmp; clear tmp.
  do 3 rewrite size_le_sizeP.

  unshelve erewrite (_ : sizeP (compile s0) <= sizeP (compile s)). now eapply (proj1 (Hclos _ _)).

  set (cHeap:=proj1_sig _).
  setoid_rewrite (correct__leUpToC Loop_steps_nice) with (x:=(compile s,3*k+1));cbn beta iota.
  set (c0:=c__leUpToC Loop_steps_nice).

  set (k':= 3*k+1).

  rewrite lambdaDepth_size.

  repeat (unfold sizeP;rewrite sizeP_size). cbn [L_facts.size].
  set (m_s := L_facts.size s). set (m_s' := L_facts.size s'). set (var_s := LargestVar.largestVar s).

  (*
   m_s
  + (k+1)*(k+1)*(k+m_s)* m_s
  + k + m_s
  + m_s' * ((k+1) * (k + m_s) * (var_s + 1) + m_s)
  + (k+1)*(k+m_s) + m_s'

  simplified using m_s > 0

  (k+1)*(k+1)*(k+m_s)* m_s
  + m_s' * (k+1) * (k + m_s) * (var_s + 1)
  = (k+1)*(k+m_s)* ( m_s * (k+1) + m_s' * (var_s + 1) )
  *)
  assert (Hs : m_s = (m_s - 1) + 1) by now (subst m_s;clear;destruct s;cbn).
  assert (Hs' : m_s' = (m_s' - 1) + 1) by now (subst m_s';clear;destruct s';cbn).

  assert (Hk : k' <=(3) k + 1). { subst k'. hnf. nia. }
  assert (Hk' : k' + 1 <=(3) k + 1). { subst k'. hnf. nia. }

  repeat simple apply dominatedWith_add.
  -repeat apply dominatedWith_mult_l;apply dominatedWith_solve.
   transitivity (k + m_s). easy. generalize (k + m_s);intro. destruct m_s. now exfalso. lia.
  -apply dominatedWith_mult_l. rewrite <- !mult_assoc.
   replace ((k' + 1) * ((k' + 1) * ((k' + 2 * m_s) * (2 * m_s))))
    with ((k' + 1) * ((k' + 2 * m_s) * (2 * (m_s * (k' + 1))))) by nia.
    eapply dominatedWith_mult. exact Hk'.
    eapply dominatedWith_mult. {instantiate (1:=3). hnf. subst k'. rewrite Hs at 2. clear. nia. }
    eapply dominatedWith_mult_l. {instantiate (1:=3). hnf. subst k'. rewrite Hs at 2. clear. nia. }
  -eapply dominatedWith_mult_l, dominatedWith_trans. eassumption.
  eapply dominatedWith_solve. rewrite <- !mult_assoc.  etransitivity. 2:eapply Nat.mul_le_mono_nonneg_l;[|].
   2:nia. now rewrite Nat.mul_1_r. clear - Hs. eapply LM_Lookup_nice.ge1_mul. nia. nia.
   -repeat eapply dominatedWith_mult_l. instantiate (1:=1). hnf. ring_simplify.
    transitivity (m_s * m_s'). now nia. repeat first [eapply le_plus_r|etransitivity;[|eapply le_plus_l]].
  -eapply dominatedWith_mono_c with (c:=3+8*c1+18*c1*cHeap).
  2:now unfold c1, cHeap;reflexivity. destruct m_s,m_s'. 1,2,3:exfalso;nia. hnf. unfold k'.
  clear. lia.
  -do 2 eapply dominatedWith_mult_l.
  eapply dominatedWith_mono_c with (c:=9).
  2:now unfold c1, cHeap;reflexivity. destruct m_s,m_s'. 1,2,3:exfalso;nia. hnf. unfold k'. lia.
  -do 3 eapply dominatedWith_mult_l. instantiate (1:=1). destruct m_s. exfalso;nia. hnf.
  lia.
  -eapply dominatedWith_const. hnf.  destruct m_s,m_s'. 1,2,3:exfalso;nia. hnf. unfold k'. ring_simplify.
  etransitivity. 2:eapply le_plus_r. nia.
Qed.
