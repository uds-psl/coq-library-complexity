
From Undecidability Require Import TM.PrettyBounds.PrettyBounds.
From Undecidability Require Import TM.PrettyBounds.BaseCode.
From Undecidability Require Import LM_heap_def TM.PrettyBounds.MaxList.

From Undecidability.LAM Require Import TM.Alphabets.
From Undecidability.LAM.TM Require Import CaseCom.
From Undecidability.LAM.TM Require Import StepTM LMBounds HaltingProblem.

From Undecidability Require Import UpToCNary.
Print Loop_steps.
Check LM.Step_steps_nice.



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

Section FixInit.

  Variable T V : list HClos.
  Variable H H__init: list HEntr.
  Variable i : nat.

  Variable P0 : Pro.
  Hypothesis R: pow step i ([(0,P0)],[],H__init) (T,V,H).
  Hypothesis empty_H__init: forall c, c el H__init -> c = None.
  (*
  Lemma Step_steps_nice :
    {c : nat |
      forall (T V : list HClos) (H : Heap),
        pow step i ([(0,P0)],[],H__init) (T,V,H)
        -> Step_steps T V H <=(c) (let a := length H__init + i in
                                 1 + a + 
                                size a + size H + size V +
                                size P * (1 + size H + Init.Nat.max a (LM_Lookup_nice.heap_greatest_address2 H) + size P)
                              end}.

Lemma Loop_steps_nice' :
  (fun '(T,V,H,k) => Loop_steps [c] [] [] k) <=c (fun '(T,V,H,k) => 1).
Proof.

Lemma Loop_steps_nice :
  (fun '(T,V,H,k) => Loop_steps [c] [] [] k) <=c (fun '(T,V,H,k) => 1).
Proof.
   *)
End FixInit.
