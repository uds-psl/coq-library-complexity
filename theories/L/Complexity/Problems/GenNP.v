From Undecidability.L Require Import L.
From Undecidability.L.Datatypes Require Import LProd LTerm.
From Undecidability.L.Complexity Require Import NP Synthetic Monotonic.
From Undecidability.L.Functions Require Import Size.

Definition GenNP : term*nat*nat -> Prop:=
  fun '(s', maxSize, steps (*in unary*)) =>
    (proc s'/\exists (c:term), size (enc c) <= maxSize
                         /\ s' (enc c) ⇓(<=steps) (enc true)).

Lemma NPhard_GenNP : NPhard (unrestrictedP GenNP).
Proof.
  intros X reg__X regP__X vX Q [R R__comp [p Rsound Rcomplete p__poly p__mono]]. 
  destruct R__comp as (t__R&[d__R [comp_d__R] spec_d__R]&poly_t__R&mono_t__R).
  pose (f x := fun c => d__R (x,c)).
  assert (computableTime' f (fun x _ => (1,fun c _ => (t__R (size (enc (x, c))) + 3,tt))));cbn [timeComplexity] in *.
  {intros. subst f. extract. solverec. }
  specialize inOPoly_computable with (1:=p__poly) as (f__Rbal'&tf__Rbal'&[]&polyf__Rbal'&leq_f__Rbal'&?&?&?).
  specialize inOPoly_computable with (1:=poly_t__R) as (t__R'&tt__R'&[]&poly_t__R'&leq_t__R'&?&?&?).
  eapply reducesPolyMO_intro with  (f := fun x => (lam (extT f (enc x) 0),f__Rbal' (size (enc x)),t__R' (size (enc x) + f__Rbal' (size (enc x))+4)+5));cbn [fst snd GenNP]. 
  -evar (f':nat -> nat). [f']:refine (fun x => _).
   eexists (fun x => f' x). 
   +split. extract.
    recRel_prettify2. cbn [size].  generalize (size (enc x)). intro. unfold f'. reflexivity. 
   +subst f'. cbn beta. smpl_inO. all:eapply inOPoly_comp. all:smpl_inO.
   +subst f'. cbn beta. smpl_inO.
   + eexists (fun x => _);repeat split.
    *intros. 
     repeat (setoid_rewrite -> size_prod;cbn[fst snd]).
     rewrite !size_nat_enc,!size_term_enc. cbn [size]. 
     generalize (size (enc x)). intros. reflexivity.
    *smpl_inO. all:eapply inOPoly_comp. all:smpl_inO.
    *smpl_inO.
  -cbn [unrestrictedP]. intros x ?. exists Logic.I. split.
   +intros (c&HR & Hle)%Rcomplete. cbn - [GenNP].
    specialize (spec_d__R (x,c) Hx). apply ssreflect.iffLR with (2:=HR) in spec_d__R. 
    unfold GenNP;cbn [snd].
    split. now Lproc.
    exists c. repeat split.
    *now etransitivity;eauto.
    *eapply redLe_mono.
     {Lsimpl. unfold f. now rewrite spec_d__R. }
     cbn [fst snd]. ring_simplify. 
     rewrite <- leq_t__R'.
     rewrite size_prod. cbn [fst snd].
     hnf in mono_t__R;rewrite mono_t__R. reflexivity.
     rewrite Hle,leq_f__Rbal'. reflexivity.
    *Lproc.
   +unfold GenNP.
    intros (?&c&size__c&R'). eapply Rsound.
    specialize (spec_d__R (x,c) Hx). cbn in spec_d__R. rewrite spec_d__R. 
    eapply inj_enc.
    eapply unique_normal_forms. 1,2:now Lproc.
    eapply evalLe_eval_subrelation, eval_star_subrelation in R'.
    rewrite <- R'. symmetry. eapply star_equiv_subrelation. clear R'.
    change (extT f) with (ext f). Lsimpl.
Qed.

From Undecidability.L.Functions Require Import Proc.
From Undecidability.L.AbstractMachines.Computable Require Import EvalForTimeBool.
Import EvalForTime LargestVar.

(** * The hardness proof of GewnNPHalt is prettier *)
Lemma inNP_GenNP : inNP (unrestrictedP GenNP).
Proof.
  eexists (fun '(exist _ x _) (c:term) => exists (s':term) (maxSize steps :nat), 
               x = (s',maxSize,steps) /\ proc s' /\ size (enc c) <= maxSize 
               /\ s' (enc c) ⇓(<=steps) (enc true)).
  {
    evar (f__t : nat -> nat). [f__t]:intro n.
    eexists f__t. repeat eapply conj.
    eexists (fun '((s',maxSize,steps),c) =>
               if closedb s' && lambdab s' && (size (enc c) <=? maxSize)
               then
                 evalForTimeBool true (N.of_nat steps) (s' (enc c))
               else false). split.
    -extract. intros [[[s' maxSize] steps] c].
     remember (size (enc (s', maxSize, steps, c))) as n.
     assert (H1 : ( size (enc s') <= n)) by (subst n;rewrite !size_prod;cbn;lia).
     assert (H2 : ( size (enc maxSize) <= n)) by (subst n;rewrite !size_prod;cbn;lia).
     assert (H3 : ( size (enc steps) <= n)) by (subst n;rewrite !size_prod;cbn;lia).
     assert (H4 : ( size (enc c) <= n)) by (subst n;rewrite !size_prod;cbn;lia).
     solverec.
     unfold t__evalForTimeBool,t__evalForTime,HeapMachine.heapStep_timeBound,Unfolding.unfoldBool_time,Lookup.lookupTime.
     all:rewrite <- size_term_enc_r in H1.
     all:rewrite <- size_nat_enc_r in H2.
          
     all:rewrite !H1.
     (* all:rewrite !size_term_enc_r with (s:=c). *)
     all:rewrite !H4.
     all:rewrite !H2.
     all:rewrite Nat.min_id.
     rewrite !Nnat.N2Nat.id, !Nnat.Nat2N.id.
     rewrite !largestVar_size.
     rewrite !Nat.max_lub with (p:=n + 1);[|lia..].
     rewrite !LBinNums.N_size_nat_leq.
     unfold LBinNums.time_N_of_nat.
     rewrite Nat.log2_le_lin. 2:lia.
     all:rewrite <- size_nat_enc_r in H3.
     rewrite H3. unfold f__t.
     reflexivity.
     unfold f__t. lia.
    -intros [[[s' maxSize] steps] c]. cbn [fst snd prod_curry]. unfold proc. 
     destruct (closedb_spec s');cbn [andb]. 2:{ split;[|congruence];intros (?&?&?&[= -> -> ->]&?);tauto. }
     destruct (lambdab_spec s');cbn [andb]. 2:{ split;[|congruence];intros (?&?&?&[= -> -> ->]&?);tauto. }

     destruct (Nat.leb_spec0 (size (enc c)) maxSize);cbn [andb]. 2:{ split;[|congruence];intros (?&?&?&[= -> -> ->]&?);tauto. }
     cbn [fst GenNP]. intros [].
     eapply reflect_iff.
     eapply ssrbool.equivP. eapply evalForTimeBool_spec.
     rewrite  !Nnat.Nat2N.id.
     split.
     +cbn. intuition eauto 10. 
     +intros (?&?&?&[= -> -> ->]&?). intuition eauto 10. Lproc.
    -unfold f__t.
     smpl_inO.
    -unfold f__t.
     smpl_inO.
  }
  eexists (fun x => x). 3,4:smpl_inO.
  all:intros [((?,?),?)]. all:cbn.
  -intros ? (?&?&?&[= <- <- <-]&?&?&?). eauto 10.
  -intros (?&?&?&?). eexists.  split. eauto 10.  repeat setoid_rewrite size_prod. cbn [fst snd].
   rewrite <- !size_nat_enc_r. lia. 
Qed.

Lemma GenNP_complete :
  NPcomplete (unrestrictedP GenNP).
Proof.
  eauto using inNP_GenNP, NPhard_GenNP. 
Qed.
