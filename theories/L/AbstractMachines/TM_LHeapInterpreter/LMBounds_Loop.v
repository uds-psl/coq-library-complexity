
From Complexity Require Import TM.PrettyBounds.PrettyBounds.
From Complexity Require Import TM.PrettyBounds.BaseCode.
From Undecidability Require Import LM_heap_def TM.PrettyBounds.MaxList.

From Undecidability.TM.L Require Import Alphabets CaseCom StepTM M_LHeapInterpreter.
From Complexity.L.AbstractMachines Require Import SizeAnalysisStep LMBounds.

From Undecidability Require Import UpToC UpToCNary.



Lemma sizeT_ge_1 t:
  1 <= sizeT t.
Proof.
  destruct t;cbn. all:nia.
Qed.

Lemma size_sizeT_le t:
  size t <= 2* sizeT t.
Proof.
  destruct t.
  1:rewrite size_Var.
  all:cbv - [plus mult]. all:nia.
Qed.

Lemma size_le_sizeP P:
  size P <= 3 * sizeP P.
Proof.
  induction P as [ | t P].
  {now cbv. }
  setoid_rewrite encodeList_size_cons. rewrite IHP.
  unfold sizeP;cbn. rewrite size_sizeT_le.
  specialize (sizeT_ge_1 t). nia.
Qed.

Lemma sizeT_le_size t:
  sizeT t <= size t.
Proof.
  destruct t.
  1:rewrite LMBounds.size_Var.
  all:cbv - [plus mult]. all:nia.
Qed.

Lemma sizeP_le_size P:
  sizeP P <= size P.
Proof.
  induction P as [ | t P].
  {now cbv. }
  setoid_rewrite BaseCode.encodeList_size_cons. rewrite <- IHP.
  unfold sizeP;cbn. rewrite sizeT_le_size. nia.
Qed.

(*
Lemma sizeH_le H:
  size H <= 
Proof.
  induction P as [ | t P].
  {now cbv. }
  setoid_rewrite encodeList_size_cons. rewrite IHP.
  unfold sizeP;cbn. rewrite size_sizeT_le.
  specialize (sizeT_ge_1 t). nia.
Qed.
 *)

Lemma size_list (sig X : Type) (cX : codable sig X) (xs : list X):
  size xs = length xs + sumn (map size xs) + 1.
Proof.
  induction xs. now rewrite encodeList_size_nil.
  rewrite encodeList_size_cons. cbn [length map sumn]. nia.
Qed.

Lemma size_list_le_bound (sig X : Type) (cX : codable sig X) (xs : list X) c:
  (forall x, x el xs -> size x <= c)
  -> size xs <= length xs * (c+1) + 1.
Proof.
  intros H. rewrite size_list. rewrite sumn_le_bound.
  2:{ intros ?. rewrite in_map_iff. intros (?&<-&?). eauto. }
  rewrite map_length. nia.
Qed.

Lemma size_HClos_le (g : HClos):
  size g = fst g + size (snd g) + 1.
Proof.
  rewrite Encode_Clos_hasSize. destruct g as [a P];cbn.
  replace (Encode_list_size _ P) with (size P). nia. apply Encode_list_hasSize.
Qed.

Lemma heap_greatest_address2_bound H c:
  (forall P a, Some (P,a) el H -> a <= c) -> LM_Lookup_nice.heap_greatest_address2 H <= c.
Proof.
  induction H as [ | [ [] | ] ]. all:cbn.
  -easy.
  -intros H'. rewrite IHlist. rewrite H' with (a:=n). all:now auto.
  -eauto.
Qed.

Section FixInit.
  Variable H__init: list HEntr.

  (*Variable T V : list HClos.
  Variable H H__init: list HEntr.
  Variable i : nat.
  *)
  (*Hypothesis R: pow step i ([(0,P0)],[],H__init) (T,V,H).*)
  Hypothesis empty_H__init: forall c, c el H__init -> c = None.

  Lemma Heap_size_nicer P0 (T V : list HClos) (H : Heap) i :
    pow step i ([(0,P0)],[],H__init) (T,V,H)
    -> size H <= (length H__init + i) * (S ((length H__init + i) + 3 * sizeP P0 + 1 + S (length H__init + i)) + 1) + 1.
  Proof using empty_H__init.
    intros H0.
    specialize SizeAnalysisStep.size_clos with (1:=H0) (2:=empty_H__init)as Hsize.
    unfold Encode_Heap, sigHeap. erewrite size_list_le_bound with (xs:=H).
    2:{
      intros [[[a' P'] beta] | ] H1. 2:cbv.  
      -apply Hsize in H1. unfold sigHEntr,HEntr,Encode_HEntr,sigHEntr',Encode_HEntr'. rewrite Encode_option_hasSize.
      cbn. rewrite Encode_pair_hasSize;cbn. rewrite size_HClos_le. cbn.
      rewrite size_le_sizeP, Encode_nat_hasSize. destruct H1 as (->&->&->&_). reflexivity.
      -nia. 
    }
    rewrite length_H. 2:eassumption. 2:easy. reflexivity. 
  Qed.

  Lemma Heap_size_nicer2:
    {c : nat |
      forall P0 (T V : list HClos) (H : Heap) i,
        pow step i ([(0,P0)],[],H__init) (T,V,H)
      -> size H <=(c) (length H__init + i + 1 + sizeP P0) * (length H__init + i + 1)}.
  Proof using empty_H__init.
    eexists ?[c]. intros P0 T V H i H0.
    specialize SizeAnalysisStep.size_clos with (1:=H0) (2:=empty_H__init)as Hsize.
    unfold Encode_Heap, sigHeap. erewrite size_list_le_bound with (xs:=H).
    2:{
      intros [[[a' P'] beta] | ] H1. 2:cbv.  
      -apply Hsize in H1. unfold sigHEntr,HEntr,Encode_HEntr,sigHEntr',Encode_HEntr'. rewrite Encode_option_hasSize.
      cbn. rewrite Encode_pair_hasSize;cbn. rewrite size_HClos_le. cbn.
      rewrite size_le_sizeP, Encode_nat_hasSize. destruct H1 as (->&->&->&_). reflexivity.
      -nia. 
    }
    rewrite length_H. 2:eassumption. 2:easy.
    [c]:exact 4. cbn;hnf. ring_simplify. nia.  
  Qed.

  Import ZArith.

  Lemma Step_steps_nicer :
    {c : nat |
      forall P0 (T V : list HClos) (H : Heap) i,
        pow step i ([(0,P0)],[],H__init) (T,V,H)
        -> Step_steps T V H <=(c) (length H__init + i +1 + sizeP P0 )^3}.
  Proof using empty_H__init.
    eexists. intros P0 T V H i H0. eapply dominatedWith_trans. eapply (proj2_sig LM.Step_steps_nice).
    destruct T as [ | [a P] T].
    2:{
      set (lH := length H__init + i). cbn zeta.
      specialize SizeAnalysisStep.size_clos with (1:=H0) (2:=empty_H__init)as Hsize.
      repeat setoid_rewrite size_le_sizeP. rewrite !Encode_nat_hasSize.
      erewrite size_list_le_bound with (xs:=V).
      2:{ intros [a' P'] ?. rewrite size_HClos_le. cbn.
          rewrite size_le_sizeP.
          edestruct (Hsize P' a') as [(->&->&_) _]. now eauto. reflexivity.
      }
      assert (Htmp:=proj2_sig Heap_size_nicer2 _ _ _ _ _ H0). hnf in Htmp. rewrite Htmp. clear Htmp.
      rewrite heap_greatest_address2_bound.
      2:{ intros [] ?. edestruct Hsize as [_ H']. apply H'. }
      specialize Hsize with (P1:=P) (a0 := a) as [(-> & -> &_) _]. easy.
      rewrite Nat.max_id.
      specialize length_TV  with (1:=H0) (2:=empty_H__init) as H_TV. cbn in H_TV.
      assert (length V <= i) as -> by nia.
      specialize length_H  with (1:=H0) (2:=empty_H__init) as ->. fold lH.
      clear dependent T. clear dependent V. clear dependent H.  clear dependent P. clear dependent a.
      assert (i<=lH) as -> by nia.
      clearbody lH. instantiate (1:=3 + 2*proj1_sig Heap_size_nicer2). 
      generalize (proj1_sig Heap_size_nicer2). intro. clear dependent H__init. 
      cbn [Nat.pow]. hnf. lia. 
    }
    cbn. hnf. lia.
  Qed.

  Lemma Loop_steps_nice' :
    {c : nat |
      forall P0 (T V : list HClos) (H : Heap) k i,
       pow step i ([(0,P0)],[],H__init) (T,V,H)
        -> Loop_steps T V H k <=(c) (k + 1) * (length H__init + (i+k) +1 + sizeP P0 )^3}.
  Proof using empty_H__init.
    evar (c:nat).
    eexists c. intros P0 T V H k.
    induction k in T,V,H |-*.
    all:intros i Hi.
    all:cbn - [Step_steps Nat.pow step_fun plus].
    -eapply dominatedWith_mono_c. eapply dominatedWith_trans. now apply (proj2_sig Step_steps_nicer). apply dominatedWith_solve. now cbn.
     ring_simplify. shelve. 
    -destruct (step_fun (T, V, H)) as [[[T' V'] H'] | ]  eqn:Hstep.
     2:{ eapply dominatedWith_mono_c. eapply dominatedWith_trans. now apply (proj2_sig Step_steps_nicer). apply dominatedWith_solve. now cbn.
         ring_simplify. shelve. }
     destruct is_halt_state.
     1:{ eapply dominatedWith_mono_c. all:repeat simple apply dominatedWith_add.
         1: apply dominatedWith_solve; now cbn.
         1,2: eapply dominatedWith_trans;[eapply (proj2_sig Step_steps_nicer) | ].
         easy. 2:{eapply pow_add. eexists;split. easy. rewrite <- rcomp_1. now apply step_fun_step. }
         1,2: apply dominatedWith_solve;now cbn. ring_simplify. shelve.
     }
     Set Nested Proofs Allowed.
     Lemma dominatedWith_add_split (c x1 x2 y1 y2 : nat) :
       x1 <=(c) y1 -> x2 <=(c) y2 -> x1 + x2 <=(c) y1 + y2.
     Proof.
       unfold dominatedWith. nia.
     Qed.
     set (tmp:= _ ^ 3). replace ( (S k + 1) * tmp) with (tmp + (k+1) * tmp) by nia.
     apply dominatedWith_add_split;subst tmp.
     { eapply dominatedWith_mono_c. eapply dominatedWith_add.
       -apply dominatedWith_solve. now cbn.
       -eapply dominatedWith_trans. now apply (proj2_sig Step_steps_nicer). apply dominatedWith_solve. now cbn.
       -ring_simplify. shelve.
     }
     replace (i + S k) with (i+1+k) by nia.
     eapply IHk.
     eapply pow_add. eexists;split. easy. rewrite <- rcomp_1. now apply step_fun_step.
     Unshelve.
     [c]:exact (2 * proj1_sig Step_steps_nicer + 1). all:subst c;nia.
  Qed.

  Lemma Loop_steps_nice :
    (fun '(P0,k) => Loop_steps [(0,P0)] [] H__init k)
    <=c (fun '(P0,k) => (k + 1) * (length H__init + k +1 + sizeP P0 )^3).
  Proof using empty_H__init.
    eexists. intros [? ?].
    assert (H':= proj2_sig Loop_steps_nice'). cbn beta in H'. unfold dominatedWith in H'. 
    specialize H' with (i:=0). cbn [plus] in H'.
    rewrite H'. 2:reflexivity. reflexivity.
  Qed.
End FixInit.

