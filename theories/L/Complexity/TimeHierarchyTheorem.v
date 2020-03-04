From Undecidability.L Require Import L Tactics.LTactics AbstractMachines.LargestVar.

From Undecidability.L Require Import AbstractHeapMachineDef UnfoldTailRec AbstractHeapMachine.
From Undecidability.L.AbstractMachines.Computable Require Import Unfolding HeapMachine Shared EvalForTime EvalForTimeBool.

From Undecidability.L.Complexity Require Import Synthetic AbstractTimeHierarchyTheorem.

From Undecidability.L.Datatypes Require Import Lists LBinNums.
From Undecidability.L.Functions Require Import BinNums BinNumsCompare UnboundIteration.

Section TimeHierarchy.

  Variable f : nat -> nat.
  Hypothesis TC__f : timeConstructible f.
  Hypothesis f_geq_n : forall n, n <= f n.

  Let fT := projT1 TC__f.

  Definition comp_t__E: computableTime' (fun n => N.of_nat (f n)) (fun n _ => (fT n,tt)) := timeConstructible_computableTime' TC__f.
  Definition inO_time_t__E: fT ∈O f := timeConstructible_inO TC__f.
  
  Definition L__f : term * nat -> Prop :=
    Eval unfold L__f in
      @L__f f.


  Definition E (fuel:N) (s:term) := negb (evalForTimeBool false fuel s).
                                      
  
  Instance term_t__E : computableTime' E (fun fuel _ => (1, fun s _ => (t__evalForTimeBool (largestVar s) (size s) (N.to_nat fuel) + 7, tt))).
  Proof.
    extract. solverec.
  Qed.

  Definition t__E (largestVar size:nat) fuel := t__evalForTimeBool largestVar size fuel + 8.

  
  
  Lemma E__spec (s:term) (fuel : N):
      closed s ->
      exists res : bool,
        (extT E) (enc fuel) (enc s) ⇓(<=t__E (largestVar s) (size s) (N.to_nat fuel)) (enc res) /\
        if res
        then ~ (s ⇓(<= N.to_nat fuel ) (enc false))
        else s ⇓(<= N.to_nat fuel) (enc false).
  Proof.
    intros. eexists. split.
    {
      eapply le_evalLe_proper, evalLe_trans. 2,3:reflexivity.
      2:now Lsimpl.
      2:Lreflexivity.
      solverec. reflexivity.
    }
    unfold E. destruct (evalForTimeBool_spec false s fuel).
    -cbn. easy.
    -cbn. easy.
  Qed.
  
  Lemma mono_t__E maxVar maxVar' x x' size size' :
    maxVar <= maxVar' -> x <= x' -> size <= size' -> t__E maxVar size x <= t__E maxVar' size' x'.
  Proof.
    intros H1 H2 H3.
    unfold t__E,t__evalForTimeBool.
    rewrite mono_t__evalForTime. 2-4:eassumption.
    repeat (lazymatch goal with
              |- _ + _ <= _ + _ => eapply plus_le_compat
            | |- _ * _ <= _ * _ => eapply mult_le_compat
            | |- _ => first [eassumption | reflexivity | eapply N_size_nat_monotone | eapply unfoldBool_time_mono | Lia.nia |eapply heapStep_timeBound_mono'] 
            end).
  Qed.

  Lemma suplin_t__E maxVar size x : x <= t__E maxVar size x. 
  Proof.
    unfold t__E,t__evalForTimeBool . intros. rewrite <- suplin_t__evalForTime. Lia.nia.
  Qed.
  
  Lemma inO_size_nat f' g:
    f' ∈O g ->
    (fun n => N.size_nat (N.of_nat (f' n))) ∈O g.
  Proof.
    intros (c0&n0&H).
    eexists c0,n0.
    intros. rewrite N_size_nat_leq. easy.
  Qed.

  Ltac inO_leq n := simple eapply inO_leq with (n0:=n);intros ;try rewrite <- !f_geq_n;nia.
  
  Lemma in_O_t__E :
    (fun n : nat => t__E n (2 * n) (f n)) ∈O (fun n => n * f n * f n).
  Proof.
    unfold t__E,t__evalForTimeBool,t__evalForTime.

    all:unfold unfoldBool_time.
    all:unfold heapStep_timeBound,Lookup.lookupTime.
    smpl_inO.
    1,4,6-11:inO_leq 1.
    2:unfold unfoldBool_time.
    2-3:unfold heapStep_timeBound,Lookup.lookupTime.     
    -eapply inO_size_nat. inO_leq 1.
    -transitivity (fun n => f n * ( n * f n)). 2:inO_leq 1.
     simple eapply inO_mul_l.
     all:smpl_inO.
     1-2,5-8:solve [inO_leq 1].
     +eapply inO_size_nat. smpl_inO. all:inO_leq 1.
     +simple eapply inO_mul_l. all:smpl_inO. all:inO_leq 1.
    -setoid_rewrite Nat.mul_comm at 1. eapply inO_mul_l.
     all:smpl_inO. all:try inO_leq 1.
  Qed.
  
  Lemma LA_In_f_times_step':
    unrestrictedP L__f ∈TimeO (fun n : nat => t__E n (2 * n) (f n)).
  Proof.
    eapply LA_In_f_times_step.
    all:eauto using comp_t__E,E__spec,proc_extT,inO_time_t__E,mono_t__E,suplin_t__E.
  Qed.
  
  Lemma L_A_notIn_f : ~ unrestrictedP L__f ∈Timeo f.
  Proof.
    apply L_A_notIn_f.
  Qed.
  
  Lemma LA_In_f_times_step:
    unrestrictedP L__f ∈TimeO (fun n => n * f n * f n).
  Proof.
    eapply inTime_mono.
    apply in_O_t__E.
    apply LA_In_f_times_step'.
  Qed.

  Lemma TimeHierarchyTheorem :
    exists (P : term * nat -> Prop), ~unrestrictedP P ∈Timeo f /\ unrestrictedP P ∈TimeO (fun n => n * f n * f n).
  Proof.
    exists L__f;split. all:eauto using L_A_notIn_f, LA_In_f_times_step.
  Qed.
End TimeHierarchy.

(**Check TimeHierarchyTheorem.
Axiom free: 
Print Assumptions TimeHierarchyTheorem.
*)
