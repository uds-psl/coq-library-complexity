From Undecidability.L Require Import Tactics.LTactics Prelim.MoreList Prelim.MoreBase.
From Complexity.Complexity Require Import NP Definitions Monotonic Subtypes.
From Complexity.NP.L Require Import GenNP LMGenNP. 

From Undecidability.L Require Import LM_heap_def LM_heap_correct LBool ResourceMeasures LNat LTerm LProd.
From Complexity.L Require Import Compile.

Import Nat.
Lemma GenNP_to_LMGenNP (X:Type) `{R__X : encodable X}:
  GenNP X ⪯p LMGenNP X.
Proof.
  evar (f__steps : nat -> nat). [f__steps]:intros n0.
  pose (f := (fun '(s, maxSize, steps) => (compile s,maxSize : nat, f__steps steps))).
  eapply reducesPolyMO_intro_restrictBy_both with (f:=f).
  2:{
    intros [[s' maxSize] steps].
    intros (cs&Hsmall&Hk). assert (lambda s') as [s0 eq] by Lproc. set (s:=lam s0) in *. subst s'.
    split.
    -hnf. repeat simple apply conj.
     +easy.
     +intros c k sigma R__M.
      eapply soundnessTime with (s:=(L.app s (@enc _ R__X c))) in R__M as (g&H'&t&n&eq__sigma&Rs%timeBS_evalIn&_&eq). 2:Lproc.
      subst k. apply Hsmall in Rs as (c'&k'&Hsize_c'&Hk').
      edestruct completeness as (?&?&?&HM'). 1:{split. exact Hsize_c'. Lproc. }
      1:now Lproc.
      do 2 eexists. repeat simple apply conj. 2:split. 
      1,2:eassumption.  inversion 1.
     +intros c H k sigma' R__M. unfold initLMGen in R__M.
      eapply soundnessTime with (s:=(L.app s (@enc _ R__X c))) in R__M as (g&H'&t&n&eq__sigma&Rs%timeBS_evalIn&_&eq). 2:Lproc.
      subst k. apply Hk in Rs. rewrite Rs. unfold f__steps. reflexivity. easy. 
    -apply Morphisms_Prop.ex_iff_morphism. intros c.
     apply Morphisms_Prop.and_iff_morphism_obligation_1. easy.
     split.
     +intros (?&(?&?&Ev)%evalLe_evalIn). eapply timeBS_evalIn,completenessTime in Ev. 2:Lproc.
      destruct Ev as (g&Heap&?&Rs).
      eexists _,_. split. 2:split. 2:exact Rs. now cbn; lia. now intros ? ?.
     +intros (?&?&?&R__M).
      eapply soundnessTime with (s:=(L.app s (@enc _ R__X c))) in R__M as (g&H'&t&n&eq__sigma&Rs%timeBS_evalIn&_&eq). 2:Lproc.
      eexists. eapply evalIn_evalLe. 2:easy. cbn in H;nia.
  }
  subst f__steps;cbn beta in f.
  evar (time : nat -> nat). [time]:intros n0.
  exists time.
  { unfold f. extract.
    solverec.
    set (n0:=(size (enc (a0, b0, b)))).
    eassert (b <= n0) as H.
    {subst n0. rewrite !LProd.size_prod;cbn [fst snd]. now rewrite size_nat_enc_r at 1. }
    unfold time_compile.
    eassert (size a0 <= n0) as ->.
    {subst n0. rewrite !LProd.size_prod;cbn [fst snd]. now rewrite LTerm.size_term_enc_r at 1. }
    unfold time. unfold add_time, mult_time. rewrite H . reflexivity.
  }
  - unfold time. smpl_inO.
  - unfold time. solve_proper.
  - unfold f. evar (resSize : nat -> nat). [resSize]:intros n0. eexists resSize.
    + intros [[x mSize] steps].
      set(n0:=size (enc (x, mSize, steps))).
      rewrite !LProd.size_prod;cbn [fst snd].
      setoid_rewrite size_nat_enc at 2.
      eassert (steps <= n0) as ->.
      {subst n0. rewrite !LProd.size_prod;cbn [fst snd]. now rewrite size_nat_enc_r at 1. }
      eassert (size (enc mSize) <= n0) as ->.
      {subst n0. rewrite !LProd.size_prod;cbn [fst snd]. easy. }
      rewrite compile_enc_size.
      eassert (size x <= n0) as ->.
      {subst n0. rewrite !LProd.size_prod;cbn [fst snd]. now rewrite size_term_enc_r at 1. }
      unfold resSize. reflexivity.
   + unfold resSize. smpl_inO.
   + unfold resSize. solve_proper.
Qed.

(*
Lemma NPhard_LMGenNP X__cert `{R__cert : encodable X__cert}:
  canEnumTerms X__cert->  NPhard (LMGenNP X__cert).
Proof.
  intros ?%NPhard_GenNP. now eapply (red_NPhard GenNP_to_LMGenNP).
Qed.
*)
