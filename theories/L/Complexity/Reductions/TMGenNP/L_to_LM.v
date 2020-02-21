From Undecidability.L Require Import Tactics.LTactics Prelim.MoreList Prelim.MoreBase.
From Undecidability.L.Complexity Require Import NP Synthetic Monotonic GenNP LMGenNP.

From Undecidability.L Require Import LM_heap_def LM_heap_correct LBool ResourceMeasures Compile LNat LTerm Compile.

Lemma GenNP_to_LMGenNP (X:Type) `{R__X : registered X}:
  restrictBy (LHaltsOrDiverges X) (GenNP X) ⪯p restrictBy (LMHaltsOrDiverges X) (LMGenNP X).
Proof.
  evar (f__steps : nat -> nat). [f__steps]:intros n0.
  pose (f := (fun '(s, maxSize, steps) => (compile s,maxSize : nat, f__steps steps))).
  eapply reducesPolyMO_intro_restrictBy with (f:=f).
  2:{
    intros [[s' maxSize] steps].
    intros (cs&Hsize). assert (lambda s') as [s0 eq] by Lproc. set (s:=lam s0) in *. subst s'.
    split.
    -split. easy.
     intros c H k sigma' R__M. unfold initLMGen in R__M.
     eapply soundnessTime with (s:=(L.app s (@enc _ R__X c))) in R__M as (g&H'&t&n&eq__sigma&Rs%timeBS_evalIn&_&eq). 2:Lproc.
     subst k. apply Hsize in Rs. rewrite Rs. unfold f__steps. reflexivity. easy. 
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
    eassert (b <= n0) as ->.
    {subst n0. rewrite !LProd.size_prod;cbn [fst snd]. now rewrite size_nat_enc_r at 1. }
    unfold time_compile.
    eassert (size a0 <= n0) as ->.
    {subst n0. rewrite !LProd.size_prod;cbn [fst snd]. now rewrite LTerm.size_term_enc_r at 1. }
    unfold time. reflexivity.
  }
  1,2:now unfold time;smpl_inO.
  {unfold f. evar (resSize : nat -> nat). [resSize]:intros n0. eexists resSize.
   {intros [[x mSize] steps].
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
   }
   1,2:unfold resSize;smpl_inO.
  }
Qed.

(*
Lemma NPhard_LMGenNP X__cert `{R__cert : registered X__cert}:
  canEnumTerms X__cert->  NPhard (LMGenNP X__cert).
Proof.
  intros ?%NPhard_GenNP. now eapply (red_NPhard GenNP_to_LMGenNP).
Qed.
*)
