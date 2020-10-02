From Undecidability.L.Datatypes Require Import LNat LBool LProd LTerm.
From Complexity.L Require Import LBinNums.
From Undecidability.L Require Import Tactics.LTactics Functions.Eval Functions.Equality.
From Complexity.L Require Import Synthetic.
From Complexity.L.AbstractMachines Require Import AbstractHeapMachine FunctionalDefinitions.
From Undecidability.L.AbstractMachines Require Import Programs.

From Undecidability.L.Functions Require Import Size Proc.

Tactic Notation "destruct" "*" "eqn" :=
  let E := fresh "eq" in destruct * eqn:E.


From Complexity.L.AbstractMachines.Computable Require Import Shared HeapMachine.
From Undecidability.L Require Import AbstractMachines.LargestVar.
Import Nat.
(*Proof inspired by CS 172 handout 8 from 4/21/2015 from Luca Trevisan and Sipser's book  *)

Import HOAS_Notations.
Import L_Notations_app.


(** * Time Hierarchy theorem *)

Lemma computesTime_evalLe X Y `(registered X) `(registered Y) (f:X -> Y) s__f (t__f : X -> unit -> (nat*unit)):
  computesTime _ f s__f t__f
  -> forall (x:X), s__f (enc x) ⇓(<= fst (t__f x tt)) enc (f x).
Proof.
  cbn [computesTime timeComplexity].
  intros (?&H') x.
  split. 2:Lproc.
  specialize H' with (y:=x) (1:=Logic.eq_refl) (yTime:=tt) as (?&H'&->).
  exact H'.
Qed.
  
Section TimeHierarchy_Parametric.
  (** An Proof that makes the requireements on the step-indexed universal machine explicit *)
  (** We follow Sipser's "Introduction to the theory of Computation", Theorem 9.10, page 311, and
 the analysis in CS 172 handout 8 from 4/21/2015 from Luca Trevisan *)
  Variable f : nat -> nat. (* For TMs: O (t (n)) *)

  Let start (w : term * nat) : term :=
    let '(s,padding) := w in (s (enc w)).

  Definition L__f (w : term * nat) :=~closed (fst w) \/ start w ⇓(<=f(size (enc w))) enc false.

  
  Lemma L_A_notIn_f : ~ (unrestrictedP L__f) ∈Timeo f.
  Proof.
    intros (t__o&[[fdec fdec__intT Hf]]&Ht__o).
    specialize (Ht__o 1) as (n0&Hn0). setoid_rewrite Nat.mul_1_l in Hn0.
    pose (w:=(extT fdec,n0)).  unfold extracted in w.

    assert (E__fdec : (extT fdec) (enc w) ⇓(<=f (size (enc w))) enc (fdec w)).
    {
      eapply le_evalLe_proper. 2-3:reflexivity.
      2:{ eapply computesTime_evalLe, extTCorrect. }
      cbn [fst].
      eapply Nat.lt_le_incl,Hn0.

      rewrite size_prod. unfold w;cbn [fst snd]. rewrite size_nat_enc. 
      unfold c__natsizeS, c__natsizeO. lia.
    }
    clear Hn0.
    specialize (Hf w Logic.I) as f_dec_spec. cbn in f_dec_spec.
    unfold L__f in f_dec_spec. cbn in *. unfold w in f_dec_spec at 1 3.  cbn [start fst snd] in *. fold w in f_dec_spec.
    clearbody w.

    destruct (fdec w) eqn:eq.
    -assert (~(extT fdec) (enc w) ⇓(<=f (size (enc w))) enc false).
     {intros H'.
      enough (H:enc true = enc false) by inv H.
      eapply eval_unique. all:eapply evalLe_eval_subrelation;eassumption.
     }
     intuition.
    -intuition.
  Qed.

  (** ** Decidability in the larger time *)
  
  Let f' := fun n => N.of_nat (f n).

  Variable fT : nat -> nat.
  Context {termT_f : computableTime' f' (fun n (_:unit) => (fT n,tt))}.

  (* This is B from Sipser *)
  Variable E : term.
  Variable t__E : nat -> nat -> nat -> nat.
  (* Hypothesis mono_t__E : forall n x x',  x <= x' -> t__E n x <= t__E n x'.  *)
  
  
  (** "E fuel w" returns false iff 
   the step-indexed machine E can compute that s normalizes to false in less then fuel abstract steps *)
  Hypothesis E__spec :
    forall (s:term) (fuel : N),
      closed s ->
      exists res : bool,
        E (enc fuel) (enc s) ⇓(<=t__E (largestVar s) (size s) (N.to_nat fuel)) (enc res) /\
        if res
        then ~ (s ⇓(<= N.to_nat fuel ) (enc false))
        else s ⇓(<= N.to_nat fuel) (enc false).
  
  Hypothesis E__proc : proc E.
  

  
  Instance term_start : computableTime' start (fun w _ => (size (fst w) *30 + snd w * 14 + 36,tt)).
  Proof.
    unfold start. extract. solverec.
  Qed.

   (* computes the input and fuel for E__spec *)
  Definition U_preproc (w:term * nat) : option (term*N) :=
    let (s,padding) := w in
    let k := size (enc s) + size (enc padding) + 4 in
    let n := f' k in 
    if negb (closedb s)
    then None
    else Some (start w,n).

  Instance term_U_preproc: computableTime' U_preproc
                                          (fun (w:term*nat) _ =>
                                             (let s := fst w in
                                               let k := size (enc w) in
                                               let fuel := f' k in
                                               (if closedb s
                                                then fT k 
                                                else 0) + k * 221,tt)).
  Proof.
    unfold U_preproc.
    change (@enc term _) with term_enc.
    change (@enc nat _) with nat_enc.
    extract. recRel_prettify2.
    all:inv H. all:cbn [fst] in *.
    1,4:now rewrite H0 in H2.
    all:rewrite size_prod. all:cbn [fst snd].
    all:rewrite size_term_enc_r.
    2:rewrite (size_nat_enc_r b) at 1.
    2:change (@enc term _) with term_enc.
    2:change (@enc nat _) with nat_enc.
    all: unfold add_time, c__add, c__add1. 
    all:try lia.
  Qed.
  
  Definition U :term := Eval cbn [TH convert Nat.sub] in
        (λ w, (!!(extT U_preproc)) w
                (λ tmp, !!(extT negb) (tmp (λ start fuel, (!!E) fuel start)))
                !!(enc true)).    

  Lemma U_spec_helper (s:term) (fuel:N) (padding:nat):
    closed s -> exists t : term, E (enc fuel) (enc (start (s,padding))) ⇓ t.
  Proof.
    intros ?.
    edestruct E__spec as (res &H'&?). 
    2:{
      eexists (enc res).
      eapply evalLe_eval_subrelation; exact H'.
    }
    unfold start. Lproc. 
  Qed. 

  Definition U_spec (w:term * nat) : bool :=
    let '(s,padding):= w in
    let fuel := f' (size (enc (s,padding))) in
    match closedb_spec s with
      ReflectT x =>
      let (res,_):= @informative_eval2 (E (enc fuel) (enc (start (s,padding)))) (@U_spec_helper s fuel padding x) in
      term_eqb res (enc false)
    | _ => true
    end.

  Lemma U_correct : computesTime (TyArr _ (TyB _)) U_spec U
                                 (fun w _ => (let '(s,padding):=w in 
                                           let n := size (enc w) in
                                           let fuel := f n in
                                           fT n + t__E (largestVar (start w)) (size (start w)) fuel
                                           + n * 221 + 11,tt)).
  Proof.
    cbn [timeComplexity].
    eapply computesTimeTyArr_helper with (time := (fun w _ => _)).
    { unfold U. Lproc. }
    intros w []. split.
    2:{
      intros ? [= ->].
      eexists. split. 2:now cbn-[U_spec];reflexivity.
      unfold U. Lsimpl. unfold U_spec.
      unfold U_preproc.
      Ltac refineMatch x:=
        let ty := type of x in
        match goal with
          |- evalLe ?i _ _ =>
          refine (_ : evalLe ((fun (y:ty) => ltac:(destruct y)) x) _ _)
        end.
      refineMatch w.  destruct w as [s padding].
      refineMatch (closedb s). destruct closedb_spec.
      all: cbn [negb].
      2:now Lsimpl.
      Lsimpl.
      edestruct E__spec as (res&E1&H__E).
      2:{
        edestruct informative_eval2 as (res'&E2).    
        unshelve eassert (H':=eval_unique E2 (_ : _ ⇓ enc res)). now eapply evalLe_eval_subrelation. subst res'.
        replace ((term_eqb (enc res) (enc true))) with res by now destruct res.
        rewrite (size_prod (s,padding)) in E1 at 2. cbn [fst snd] in E1.
        split. 2:Lproc.
        eapply redLe_app_helper.
        { reflexivity. }
        { eapply evalLe_redLe_subrelation. refine E1. }
        Lsimpl. destruct res;reflexivity. 
      }
      -unfold start. Lproc.
    }
    destruct w as [s padding]. cbn [fst]. unfold f'. rewrite Nnat.Nat2N.id.
    recRel_prettify2. all:try Lia.lia.
  Qed.

  Lemma U_reflects_U_spec w:
    reflect (U (enc w) ⇓ enc true) (U_spec w).
  Proof.
    unfold L__f.
    assert ((U (enc w)) ⇓ (enc (U_spec w))).
    { destruct U_correct as (?&H').
      unshelve edestruct (H' w) as (x&?&?). 2:easy. 2:reflexivity. cbn in c. subst x.
      esplit. now eapply redLe_star_subrelation. Lproc.
    }
    destruct (U_spec w). all:cbn [negb].
    all:econstructor.
    eassumption.
    intros H2.
    specialize (eval_unique H H2). easy.
  Qed.
 
  Lemma spec_L__f w :
    U (enc w) ⇓ enc true <-> L__f w.
  Proof.
    unfold L__f.
    specialize (U_reflects_U_spec w) as H.
    unfold U_spec in H.
    destruct w as [s padding]. all:cbn [fst snd].
    destruct (closedb_spec s) as [cls|].
    2:{ cbn in H. inv H. tauto. }
    destruct informative_eval2 as (res'&R).
    edestruct (@E__spec (start (s,padding)) (f' (size (enc (s,padding))))) as (res&E1&E2).
    {unfold start. Lproc. }
    replace res' with (enc res) in *.
    2:{eapply eval_unique. eapply evalLe_eval_subrelation. all:eassumption. }
    unfold f' in E2. rewrite Nnat.Nat2N.id in E2.
    destruct res;inv H.
    all:tauto.
  Qed.
  
  Hypothesis f_TC : fT ∈O f.

  Hypothesis n_leq_tn : forall n, n <= f n.
  
  
  Lemma largestVar_start w:
    largestVar (start w) <= max (largestVar (fst w)) 2.
  Proof.
    destruct w as [s padding]. cbn. rewrite largestVar_prod. cbn [fst snd].
    rewrite largestVar_term,largestVar_nat. Lia.lia.
  Qed.

  

  Hypothesis mono_t__E : forall maxVar maxVar' x size size',
      maxVar <= maxVar' -> size <= size' -> t__E maxVar size x <= t__E maxVar' size' x.
  Hypothesis suplin_t__E :
    forall maxVar size x, x <= t__E maxVar size x. 
  
  Lemma LA_In_f_times_step:
    unrestrictedP L__f ∈TimeO (fun n => t__E n (2*n) (f n)).
  Proof.
    (* intros H_t__E H_t__step. *)
    eexists (fun n => fT n + t__E n (2*n) (f n) + n * 221 + 12). split. split.
    exists U_spec.
    -eexists.
     eapply computesTime_timeLeq with (fT:= (fun w _ => (_,tt))).
     2:{ exact U_correct. }
     +intros [s padding] [].
      pose (x:=(s,padding)).
      recRel_prettify. split. 2:reflexivity.
      rewrite mono_t__E with (maxVar' := (size (enc x))) (size':=(2 * size (enc x))).
      all:subst x.
      *Lia.lia.
      *rewrite largestVar_start. rewrite size_prod.
       rewrite largestVar_size.
       rewrite size_term_enc_r. change (term_enc) with (@enc term _). cbn [fst].
       Lia.lia.
      *rewrite size_prod. cbn [start fst snd size].
       rewrite size_prod. cbn [fst snd]. rewrite size_term_enc_r with (s:=s). change (term_enc) with (@enc term _). Lia.lia. 
    -intros w ?. cbn. rewrite <- spec_L__f.
     eapply reflect_iff. apply U_reflects_U_spec.
    -repeat apply inO_add_l.
     +etransitivity. exact f_TC.
      exists 1,0. intros. rewrite <- suplin_t__E. Lia.lia.
     +reflexivity.
     +eexists 221,1. intros. rewrite <- suplin_t__E,<- n_leq_tn. Lia.lia.
     +eexists 12,1. intros. rewrite <- suplin_t__E,<- n_leq_tn. Lia.lia.  
  Qed.
End TimeHierarchy_Parametric.
