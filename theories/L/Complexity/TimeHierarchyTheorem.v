From Undecidability.L Require Import L Tactics.LTactics.

From Undecidability.L.AbstractMachines Require Import AbstractHeapMachineDef UnfoldTailRec FunctionalDefinitions.
From Undecidability.L.AbstractMachines.Computable Require Import Unfolding HeapMachine Shared.

From Undecidability.L.Complexity Require Import Synthetic AbstractTimeHierarchyTheorem.

From Undecidability.L.Datatypes Require Import Lists LBinNums.
From Undecidability.L.Functions Require Import BinNums BinNumsCompare UnboundIteration.


(*Require Import LNat LBool LBinNums LTactics Complexity.Synthetic LProd Functions.BinNumsCompare.
Require Import AbstractHeapMachine AbstractMachines.FunctionalDefinitions Programs.
Require Import Equality Eval.
Require Import Functions.UnboundIteration Functions.BinNums.

From L.Functions Require Import Size Proc.

Require Import AbstractMachines.Computable.Shared HeapMachine Unfolding Programs AbstractMachines.Computable.Compile AbstractMachines.LargestVar ARS.
*)
Section E.

  Definition extractRes (sigma : list AbstractHeapMachineDef.task * list clos * list heapEntry) :=
    match sigma with
      ([],[g],_) => Some (g)
    | _ => None
    end.

  Definition E__step '(i,sigma) : _ + bool:=
    let '(_,_,H):= sigma in
    match extractRes sigma with
      Some g => match unfoldBoolean H g with
                Some false => inr false
              | _ => inr true
              end
    | _ => if (0 <? i)%N then 
            match heapStep sigma with
              Some sigma' => inl (N.pred i,sigma')
            | _ => inr true
            end
          else inr true
    end.

  Definition time_E__step x :=
    let '(i,x) := x in
    let '(T,V,H):=x in
    match extractRes x with
      Some g  => unfoldBool_time (length H) (Init.Nat.max (largestVarH H) (largestVarC g))
    | _ => N.size_nat i * 12
            + if (0 <? i)%N
              then heapStep_time T H
              else 0
    end + 81.

  Lemma spec_extractRes sigma:
    match extractRes sigma with
      Some g => exists H, sigma = ([],[g],H)
    | None => forall g H, sigma <> ([],[g],H)
    end.
  Proof.
    unfold extractRes.
    all:repeat (let eq := fresh "eq" in destruct _ eqn:eq).
    all:try congruence. eexists _;repeat f_equal. congruence.
  Qed.

  Arguments extractRes : simpl never.
  
  Lemma spec_E__step i sigma:
    match E__step (i,sigma) with
      inl (i',sigma') => i = N.succ i' /\ step sigma sigma' /\ extractRes sigma = None
    | inr b =>
      match extractRes sigma with
        None => b = true /\ (i = 0%N \/ terminal step sigma)
      | Some g => b = false <-> unfoldBoolean (snd sigma) g = Some false
      end
    end.
  Proof.
    specialize (heapStep_sound sigma) as R.
    specialize (spec_extractRes sigma) as H''.
    all:cbn.
    all:destruct sigma as [[T V] H];cbn [snd].
    all:destruct (N.ltb_spec0 0 i);[|replace i with (0%N) by Lia.nia].
    all:repeat (let eq := fresh "eq" in destruct _ eqn:eq).
    all:try discriminate.
    all:subst.
    all:repeat match goal with
                 H :  inl _ = inl _ |- _ => inv H
               | H :  inr _ = inr _ |- _ => inv H
end.
    1:now split;(tauto + Lia.nia).
    all:try easy.
    all:left.
    all:repeat esplit.
    all:congruence.
  Qed.
  
  Instance termT_extractRes : computableTime' extractRes (fun _ _ => (23,tt)).
  Proof.
  extract. solverec. 
  Qed.
  
  Instance termT_E__step : computableTime' E__step (fun x _ => (time_E__step x,tt)).
  Proof. 
    extract. intros (i&((T&V)&H)). unfold time_E__step. (*recRel_prettify2.*)
    all:solverec.
   Qed. 

  Arguments E__step : simpl never.
  (*
  Lemma time_E__step_eq i T V H:
    ~(T=[] /\ exists g, V=[g]) ->
    time_E__step (i, (T, V, H))
    = N.size_nat i * 12
      + (if (0 <? i)%N then heapStep_time T H else 0)
      + 60.
  Proof.
    intros ?.
    unfold time_E__step. destruct T. destruct V as [|? []]. 2:exfalso.
    all:destruct (N.ltb_spec0 0 i);[|try easy]. all:easy.
  Qed.*)
  
  
  Definition init__E (fuel:N) (s:term) :=
    ((4 * fuel +1)%N,init s).

  Instance termT_init__E : computableTime' init__E (fun fuel (_:unit) => (1,fun s (_:unit) => (size s * 108 + N.size_nat fuel * 84 + 259,tt))).
  Proof.
    eapply computableTimeExt with (x:=fun fuel s => ((fuel + fuel + fuel + fuel +1)%N,init s)).
    -unfold init__E. repeat intro. hnf. f_equal. Lia.nia.
    -extract.
    recRel_prettify2. reflexivity.
    change (N.size_nat 1) with 1. ring_simplify.
    
    repeat rewrite N_size_nat_add_leq.
    rewrite !Nat.max_l. all:try Lia.lia.
  Qed.

  Tactic Notation "destruct" "*" "eqn" :=
    let E := fresh "eq" in destruct * eqn:E.

  Definition R__step := fun '(i,s) '(i',s') => i = N.succ i' /\ step s s'.

  Lemma pow_Rstep k i i' x x':
    ARS.pow R__step k (i,x) (i',x')
    -> i'= (i - N.of_nat k)%N /\ ARS.pow step k x x'.
  Proof.
    intros R.
    induction k in i',x',R|-*.
    {inv R. split. Lia.lia. reflexivity. }
    replace (S k) with (k + 1) in * by omega.
    eapply pow_add in R as ((i''&x'')&R&R'').
    eapply IHk in R as (->&R). eapply rcomp_1 in R'' as [? R''].
    split. Lia.nia. eapply pow_add;eexists. split. eauto. now eapply rcomp_1 with (R:=step).
  Qed.
  Import Undecidability.L.AbstractMachines.LargestVar Undecidability.L.AbstractMachines.AbstractHeapMachine.
  Lemma time_uiter_E__step s fuel:
    closed s ->
    uiterTime E__step (fun x (_:unit) => (time_E__step x,tt)) (N.to_nat fuel + 1) (fuel,init s) <=
    (N.to_nat fuel + 1) * (N.size_nat fuel * 12 + heapStep_timeBound (largestVar s) (N.to_nat fuel) + 90) + (unfoldBool_time (N.to_nat fuel) (largestVar s)).
  Proof.
    intros cs.
    rewrite uiterTime_computesRel
      with (R:= R__step)
           (t__step := N.size_nat fuel * 12 + heapStep_timeBound (largestVar s) (N.to_nat fuel) + 81)
           (t__end := (unfoldBool_time (N.to_nat fuel) (largestVar s))).
    2:{
      intros k' (i'&x') ? R.
      eapply pow_Rstep in R as (->&R). cbn [fst].
      specialize spec_E__step with (i:=(fuel - N.of_nat k')%N) (sigma:=x') as H'.
      specialize (spec_extractRes x') as Hx'.
      -destruct x' as [[T V] Hp].
       cbn [fst snd] in *.
       unfold time_E__step.
       destruct extractRes.
       +destruct E__step as [[]|]. now destruct H'. split. 2:tauto.
        rewrite unfoldBool_time_mono with (l':=(N.to_nat fuel)) (n':=(largestVar s)).
        *now omega.
        *rewrite length_H. 2:eassumption. Lia.nia.
        *eapply subterm_property in R as (_&H__V&H__H).
          eapply Nat.max_case.
         --eapply largestVarH_bound.
           intros [] ? ?. cbn.
           eapply subterm_largestVar.
           apply H__H in H0.
           eapply subterm_lam_inv in H0. easy.
         --destruct Hx' as (?&[= -> -> <-]).
           destruct p.
           eapply subterm_largestVar.
           eapply subterm_lam_inv. eauto.
       +split.
        *rewrite N_size_nat_monotone with (n':=fuel). 2:Lia.nia.
         destruct N.ltb_spec0 with (x:=0%N) (y:=(fuel - N.of_nat k')%N). 2:Lia.nia.
         rewrite heapStep_timeBound_le. 2:eassumption.
         rewrite heapStep_timeBound_mono with (k':=N.to_nat fuel). 2:Lia.nia. Lia.nia.
        *destruct E__step as [[]|]. 2:easy.
         split. 2:easy. easy.
    }
    Lia.nia.
  Qed.  
  
  Lemma sound_E__step fuel x: {b & loopSum (N.to_nat fuel +1 ) E__step (fuel,x) = Some b}.
  Proof.
    remember (N.to_nat fuel) as n eqn:eqn.
    induction n in eqn,fuel,x|-*.
    all:cbn.
    all:specialize (spec_E__step fuel x) as H'.
    all:destruct E__step as [[]|].
    1:exfalso;Lia.nia.
    1,3:eauto.
    {destruct H' as (->&?&?).
     edestruct IHn with (fuel:=n0). Lia.nia.
     eauto.
    }
  Qed.      

  Definition E : term := Eval cbn [convert TH]in (λ fuel s, !!(uiter E__step) (!!(extT (init__E)) fuel s)).

  Definition t__E maxVar (size:nat) fuel :=
    let fuel' := (4*fuel + 1) in
    size *108 + N.size_nat (N.of_nat fuel) * 84+
    unfoldBool_time fuel' maxVar + (fuel' + 1) * (N.size_nat (N.of_nat fuel') * 12
                                                        + heapStep_timeBound maxVar fuel' +90) +262.

  
  Lemma sound_E__step2' i sigma b:
    loopSum (N.to_nat i + 1) E__step (i,sigma) = Some b
    -> reflect (exists k g H, k <= N.to_nat i /\ ARS.pow step k sigma ([],[g],H) /\ unfoldBoolean H g = Some false) (negb b).
  Proof.
    intros H.
    eapply iff_reflect.
    eapply loopSum_rel_correct2 with (R:=R__step) in H as (k&(x'&i')&?&eq1&R&Ter&eq2).
    2:{ clear i H. intros [i x]. assert (H':=spec_E__step i x).
        destruct E__step as [[]|b'].
        +destruct H' as (->&?&?).
         hnf. easy.
        +intros [i' x'] R'. destruct R' as (->&R').
         assert  (Hx:=spec_extractRes x). destruct extractRes.
        -destruct Hx as (?&->).
         inv R'.
        -destruct H' as (->&[|Ter]). easy.
         edestruct Ter. easy.
    }
    eapply pow_Rstep in R as (->&R).
    eassert (H'':=spec_E__step _ _ ).
    unfold state in *.
    rewrite eq2 in H''.
    eassert (H':=spec_extractRes i').
    split;destruct b;cbn;try congruence.
    -intros (k'&g&Hp&?&?&?). exfalso.
     edestruct uniform_confluence_parameterized_terminal
       with (3:=H1) (4:=R) as (n'&R'&eq').
     { eapply functional_uc, step_functional. }
     { intros ? Ht. inv Ht. }
     destruct extractRes.
     +destruct H' as (?&->). destruct n'. now inv R'. destruct R' as (?&R''&?). inv R''.
     +replace n' with 0 in *.
      2:{
        destruct H'' as (_&[]). Lia.nia.
        destruct n'. easy. destruct R' as (?&R'&?). now edestruct H3.
      }
      inv R'. eapply H'. easy.
    -intros _.
     destruct extractRes. 2:easy.
     destruct H' as (?&->).
     firstorder.
  Qed.
  
  Lemma E__spec (s:term) (fuel : N):
    closed s ->
    exists res : bool,
      E (enc fuel) (enc s) ⇓(<=t__E (largestVar s) (size s) (N.to_nat fuel)) (enc res) /\
      if res
      then ~ (s ⇓(<= N.to_nat fuel ) (enc false))
      else s ⇓(<= N.to_nat fuel) (enc false).
  Proof.
    intros cs.
    unfold E.
    edestruct sound_E__step as [b ?].
    exists b.
    split.
    -eapply le_evalLe_proper.
     2-3:reflexivity.
     2:{ Lsimpl.
         eapply uiter_sound.
         eapply e.
     }
     unfold init__E.
     pose (fuel':=(4*fuel + 1)%N).
     fold fuel'.
     recRel_prettify2.
     erewrite time_uiter_E__step. 2:easy.
     unfold t__E.
     replace (4 * N.to_nat fuel + 1) with (N.to_nat fuel') by (unfold fuel';Lia.lia).
     rewrite !Nnat.N2Nat.id.
     Lia.nia.
    -pose (fuel':=(4*fuel + 1)%N).
     fold fuel' in e.
     eapply sound_E__step2' in e.
     destruct b;inv e.
     +intros (k'&Hle&R)%evalLe_evalIn.
      eapply ResourceMeasures.timeBS_evalIn in R.
      eapply correctTime in R as (?&?&?&?). 2:easy.
      apply H.
      do 3 eexists. split;[|split]. 2:now eauto. subst fuel'. Lia.nia.
      eapply unfoldBoolean_complete. easy.
     +destruct H as (k&g&H&Hleq&R&rep).      
      edestruct soundness as (g'&H'&t&n&eq'&EV&rep'&eqk).
      { eassumption. }
      { split. easy. intros ? R'. inv R'. }
      revert eq'. intros [= <- <-].
      eapply unfoldBoolean_sound in rep.
      specialize (reprC_functional rep rep') as <-.
      subst fuel'.
     
      eapply evalIn_evalLe.
      2:{ eapply ResourceMeasures.timeBS_evalIn. eassumption. }
      Lia.lia.
  Qed.

  Lemma mono_t__E maxVar maxVar' x x' size size' :
    maxVar <= maxVar' -> x <= x' -> size <= size' -> t__E maxVar size x <= t__E maxVar' size' x'.
  Proof.
    intros H1 H2 H3.
    unfold t__E.
    repeat (lazymatch goal with
              |- _ + _ <= _ + _ => eapply plus_le_compat
            | |- _ * _ <= _ * _ => eapply mult_le_compat
            | |- _ => first [eassumption | reflexivity | eapply N_size_nat_monotone | eapply unfoldBool_time_mono | Lia.nia |eapply heapStep_timeBound_mono'] 
            end).
  Qed.

  Lemma suplin_t__E maxVar size x : x <= t__E maxVar size x. 
  Proof.
    unfold t__E. Lia.nia.
  Qed.
End E.


Section TimeHierarchy.

  Variable f : nat -> nat.
  Hypothesis TC__f : timeConstructible f.
  Hypothesis f_geq_n : forall n, n <= f n.

  Let fT := projT1 TC__f.
  Check timeConstructible_inO TC__f.
  Definition comp_t__E: computableTime' (fun n => N.of_nat (f n)) (fun n _ => (fT n,tt)) := timeConstructible_computableTime' TC__f.
  Definition inO_time_t__E: fT ∈O f := timeConstructible_inO TC__f.


  Let start (w : term * nat) : term :=
    let '(s,padding) := w in (s (enc w)).

  Lemma E__proc : proc E.
  Proof.
    unfold E. Lproc.
  Qed.
  
  Definition L__f : term * nat -> Prop :=
    Eval unfold L__f in
      @L__f f.
  
  Lemma inO_size_nat f' g:
    f' ∈O g ->
    (fun n => N.size_nat (N.of_nat (f' n))) ∈O g.
  Proof.
    intros [c0 n0 H].
    eexists c0 n0.
    intros. rewrite N_size_nat_leq. easy.
  Qed.

  Ltac inO_leq n := simple eapply inO_leq with (n0:=n);intros ? ?;try rewrite <- !f_geq_n;Lia.nia.

  Ltac inO_safe := once (lazymatch goal with
                           |- (fun n => _ * _ ) ∈O _ =>
                           first [simple eapply inO_mul_c_l
                                 | simple eapply inO_mul_c_r]
                         | |- _ =>
                           first [simple eapply inO_add_l 
                                 | simple eapply inO_mul_c_l
                                 | simple eapply inO_mul_c_r
                                 | simple eapply inO_c with (n0:=1);intro;try rewrite <- !f_geq_n;Lia.nia
                                 | inO_leq 1]
                         end).

  
  Lemma in_O_t__E :
    (fun n : nat => t__E n (2 * n) (f n)) ∈O (fun n => n * f n * f n).
  Proof.
    unfold t__E.
    repeat inO_safe.
    2:unfold unfoldBool_time.
    2-3:unfold heapStep_timeBound,Lookup.lookupTime.
    
    -eapply inO_size_nat. repeat inO_safe.
    -repeat inO_safe.
     simple eapply inO_mul_l.
     all:repeat inO_safe.
    -transitivity (fun n => f n * ( n * f n)). 2:inO_leq 1.
     simple eapply inO_mul_l.
     all:repeat inO_safe.
     +eapply inO_size_nat. repeat inO_safe.
     +simple eapply inO_mul_l.
      all:repeat inO_safe.
  Qed.
  
  Lemma LA_In_f_times_step':
    L__f ∈TimeO (fun n : nat => t__E n (2 * n) (f n)).
  Proof.
    eapply LA_In_f_times_step.
    all:eauto using comp_t__E,E__spec,E__proc,inO_time_t__E,mono_t__E,suplin_t__E.
  Qed.
  
  Lemma L_A_notIn_f : ~ L__f ∈Timeo f.
  Proof.
    apply L_A_notIn_f.
  Qed.
  
  Lemma LA_In_f_times_step:
    L__f ∈TimeO (fun n => n * f n * f n).
  Proof.
    eapply inTime_mono.
    apply in_O_t__E.
    apply LA_In_f_times_step'.
  Qed.

  Lemma TimeHierarchyTheorem :
    exists (P : (term * nat) -> Prop), ~P ∈Timeo f /\ P ∈TimeO (fun n => n * f n * f n).
  Proof.
    exists L__f;split. all:eauto using L_A_notIn_f, LA_In_f_times_step.
  Qed.
End TimeHierarchy.

Check TimeHierarchyTheorem.
Print Assumptions TimeHierarchyTheorem.
