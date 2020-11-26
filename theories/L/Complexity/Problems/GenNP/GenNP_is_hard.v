From Undecidability.L Require Import L.
From Undecidability.L.Datatypes Require Import LProd LTerm LBool.
From Complexity.L.Complexity Require Import NP Synthetic Monotonic CanEnumTerm_def. 
From Complexity.L.Complexity.Problems.GenNP Require Import GenNP.
From Undecidability.L.Functions Require Import Size.

Import Nat.
Import L_Notations.

Lemma NPhard_GenNP X__cert `{R__cert : registered X__cert}:
  canEnumTerms X__cert->  NPhard (restrictBy (LHaltsOrDiverges X__cert) (GenNP X__cert)).
Proof.
  intros enumTerm'.
  destruct (canEnumTerms_compPoly enumTerm') as (enumTerm&[comp1]&[comp2]&[comp3]);clear enumTerm'.
  intros X reg__X regP__X vX Q [R R__comp' R__spec'(*[p Rsound Rcomplete p__poly p__mono]*)].
  destruct (polyCertRel_compPoly R__spec') as (R__spec&[pR__comp]);clear R__spec'.
  destruct (inTimePoly_compTime R__comp') as (timeR&[timeR__comp]&[R__comp]&poly_t__R&mono_t__R);clear R__comp'.
  (*intros X reg__X regP__X vX Q [ R R__dec R__spec].
    destruct R__dec as (time__R&[R__comp]&poly_t__R&mono_t__R). *)
  pose (f x := fun c => f__decInTime R__comp (x,f__toTerm enumTerm c)).
  evar (time : nat -> nat). [time]:intros n.
  assert (computableTime' f (fun x _ => (1,fun c _ => (time (size (enc (x,c))) (*t__R (size (enc (x, c))) + 3*) ,tt))));cbn [timeComplexity] in *.
  {subst f. extract.
   recRel_prettify. intros x _. split. nia. intros c__t _. split. 2:easy.
   remember (size (enc (x, c__t))) as n0 eqn:eqn0.
   rewrite (mono__polyTC enumTerm (x':=n0)). 2:{ subst n0. rewrite size_prod. cbn;lia. }
   erewrite (mono_t__R _).
   2:{
     rewrite size_prod in eqn0|-*;cbn [fst snd] in eqn0|-*.
     rewrite (bounds__rSP enumTerm c__t). rewrite (mono__rSP _ (x':=n0)). 2:{subst n0;nia. }
     instantiate (1:=n0 + resSize__rSP enumTerm n0). nia.
   }
   unfold time;reflexivity. 
  }
  (*specialize inOPoly_computable with (1:=poly__pCR R__spec) as (p__cert'&tf__Rbal'&[]&polyf__Rbal'&leq_f__Rbal'&?&?&?).
    specialize inOPoly_computable with (1:=poly_t__R) as (time__R'&tt__R'&[]&poly_t__R'&leq_t__R'&?&?&?). *)
  evar (stepsInner : nat -> nat). [stepsInner]:intros n0.
  evar (mSize : nat -> nat). [mSize]:intros n0. evar (steps : nat -> nat). [steps]:intros n0.
  pose (g:= fun (x:X) => (lam (trueOrDiverge (extT f (enc x) 0)), mSize (size (enc x))(*f__Rbal' (size (enc x))*)
                   ,steps (size (enc x))(*t__R' (size (enc x) + f__Rbal' (size (enc x))+4)+9*))).
  apply reducesPolyMO_intro with (f:= g);cbn [fst snd].
  2:{
    intros x x__valid. remember (g x) as x0 eqn:eqx0. destruct x0 as ((t0,maxSize0),steps0).
    unfold g in eqx0. injection eqx0. intros Hx0 Hsize0 Hsteps0. clear eqx0.
    cbn [GenNP restrictBy fst snd].
    unfold LHaltsOrDiverges.
    
    set (n0:= size (enc x)).
    assert (Ht0 : forall c, size (enc c) <= maxSize0 -> t0 (enc c) >(<= stepsInner n0) trueOrDiverge (enc (f x c))).
    {intros c Hc. subst t0. eapply le_redLe_proper. 2,3:reflexivity. 2:now  Lsimpl.
     cbn [fst snd]. ring_simplify.
     rewrite size_prod. cbn [fst snd]. unfold time.
     rewrite (mono__polyTC enumTerm). 2:now rewrite Hc.
     hnf in mono_t__R;erewrite mono_t__R. 
     2:{ rewrite (mono__rSP enumTerm). all:rewrite Hc. all:reflexivity. }
     unfold stepsInner. subst maxSize0. fold n0. reflexivity.
    }
    assert (Ht0' : forall c, t0 (enc c) >* trueOrDiverge (enc (f x c))).
    {intros c. subst t0. eapply redLe_star_subrelation.
     eapply le_redLe_proper. 2,3:reflexivity. 2:now Lsimpl. reflexivity.
    }
    split.
    +repeat simple apply conj.
     *now subst t0;Lproc.
     *intros c k t Ht.
      specialize (Ht0' c) as Ht0''.
      unshelve eassert (eqb := trueOrDiverge_eval _).
      3:{
        eapply equiv_eval_proper. 
        3:eapply evalIn_eval_subrelation;exact Ht. 2:reflexivity.
        rewrite Ht0'. easy.
      }
      rewrite eqb in Ht0''.
      assert (H:=eqb).
      unfold f in H. unshelve rewrite <- correct__decInTime in H. now eassumption.
      hnf in H.
      replace t with I in *. clear t.
      2:{eapply eval_unique. 2:now eapply evalIn_eval_subrelation.
         split. 2:Lproc. rewrite Ht0''. rewrite trueOrDiverge_true. easy. }
      edestruct complete__pCR with (p:=R__spec) as (tc'&HRc'&Hsizec').
      { eapply sound__pCR in H. 2:easy. eassumption. }
      (*eapply sound__pCR in HRc'. 2:easy. *) subst t0.  
      cbn [proj1_sig] in Hsizec'.
      specialize (complete__toTerm enumTerm tc') as (c'&<-&Hc').
      eexists c';split.
      2:{ Intern.infer_instances. Lsimpl. split. 2:now Lproc. rewrite <- trueOrDiverge_true. apply star_trans_r.
          enough (H':f x c' = true) by (rewrite H';reflexivity ).
          unfold f. rewrite <- correct__decInTime. hnf. easy.
      }
      subst steps0. rewrite Hc'.
      etransitivity. 1:{eapply monoIn__toTerm. eassumption. }
      subst maxSize0. subst mSize. set (size _). hnf. reflexivity.
     *intros c H' k t Ht. specialize (Ht0 c H') as (kt0&lt__j&Ht0).
      unshelve eassert (eqb := trueOrDiverge_eval _).
      3:{
        eapply equiv_eval_proper. 
        3:eapply evalIn_eval_subrelation;exact Ht. 2:reflexivity.
        eapply pow_star in Ht0;rewrite Ht0. easy.
      }
      rewrite eqb in Ht0. 
      edestruct evalIn_unique with (1:=Ht) as [eqk _].
      {clear Ht. eapply evalIn_trans. exact Ht0. split. apply trueOrDiverge_true. Lproc. }
      subst k steps0. rewrite lt__j. fold n0. unfold steps. reflexivity.
    +split.
     *intros (c&?&H')%(complete__pCR R__spec). cbn [proj1_sig] in H'. (*specialize (spec_d__R (x,c) x__valid). cbn [fst snd] in *. cbn in *. *)
      destruct (complete__toTerm enumTerm c) as (c__X&eqf__term&le_c__X).
      exists c__X. split. 
      --rewrite le_c__X. subst maxSize0.
        rewrite (monoIn__toTerm enumTerm (x:=_)). 2:exact H'.
        set (n1:=size (enc x)). unfold mSize. reflexivity.
      --exists I.
        unshelve eassert (Hc'' := Ht0 c__X _).
        {subst maxSize0. rewrite le_c__X. rewrite (monoIn__toTerm enumTerm (x:=_)). 2:exact H'. unfold mSize. reflexivity. }
        eapply evalIn_mono.
        {Lsimpl. unfold f. rewrite eqf__term.
         erewrite (complete__decInTime R__comp). 2:cbn;easy. Lsimpl. Lreflexivity. }
        subst steps0 steps. fold n0. easy.
     *intros (c&size__c&?&R'). eapply (sound__pCR R__spec).
      apply (sound__decInTime (P__dec:=R__comp) (x:=exist _ (x,_) _)). cbn.
      eapply trueOrDiverge_eval with (t:=x0).
      eapply equiv_eval_proper. 2:reflexivity.
      {unfold f in Ht0. specialize (Ht0 _ size__c). apply redLe_star_subrelation in  Ht0.  rewrite <- Ht0.
       symmetry. apply star_equiv_subrelation. eapply redLe_star_subrelation. apply R'.
      }
      destruct R'. Lreflexivity.
  }
  -unfold g. evar (f':nat -> nat). [f']:refine (fun x => _).
   eexists (fun x => f' x). 
   +unfold mSize, steps, stepsInner. extract.
    recRel_prettify2. generalize (size (enc x)). intro. unfold f'. reflexivity.
   +subst f'. cbn beta. setoid_rewrite size_nat_enc. all:smpl_inO. all:eapply inOPoly_comp. 
     all:unfold add_time; smpl_inO. all:eapply inOPoly_comp. all:smpl_inO. all:eapply inOPoly_comp. all:smpl_inO.
    all:eapply inOPoly_comp. all:smpl_inO.
   +subst f'. cbn beta. setoid_rewrite size_nat_enc. all:unfold add_time; smpl_inO.
   +unfold mSize,steps,stepsInner. eexists (fun x => _).
    *intros. 
     repeat (setoid_rewrite -> size_prod;cbn[fst snd]).
     rewrite !size_nat_enc,!size_term_enc. cbn [size]. 
     generalize (size (enc x)). intros. reflexivity.
    *smpl_inO. all:eapply inOPoly_comp. all:smpl_inO. all:eapply inOPoly_comp. all:smpl_inO. all:eapply inOPoly_comp. all:smpl_inO. 
    *smpl_inO.
Qed.


