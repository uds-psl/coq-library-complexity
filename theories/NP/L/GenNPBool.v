From Undecidability.L Require Import L_facts.
From Undecidability.L.Datatypes Require Import LProd LTerm LBool.
From Complexity.Complexity Require Import NP Definitions Monotonic.
From Undecidability.L.Functions Require Import Size.
Import Nat L_Notations.

#[export] Instance add_time_mono: Proper (le ==> le) add_time.
Proof. unfold add_time. solve_proper. Qed.

Definition GenNPBool : term*nat*nat -> Prop:=
  fun '(s', maxSize, steps (*in unary*)) =>
    (proc s'/\exists (c:term), size (enc c) <= maxSize
                         /\ s' (enc c) ⇓(<=steps) (enc true)).

(** * The hardness proof of GenNP is prettier *)
Lemma NPhard_GenNPBool : NPhard GenNPBool.
Proof.
  intros X reg__X regP__X Q [R R__comp' R__spec'(*[p Rsound Rcomplete p__poly p__mono]*)].
  destruct (polyCertRel_compPoly R__spec') as (R__spec&[pR__comp]);clear R__spec'.
  destruct (inTimePoly_compTime R__comp') as (timeR&[timeR__comp]&[R__comp]&poly_t__R&mono_t__R);clear R__comp'.
  pose (f x := fun c => f__decInTime R__comp (x,c)).
  assert (computableTime' f (fun x _ => (1,fun c _ => (timeR (size (enc (x, c))) + 3,tt))));cbn [timeComplexity] in *.
  {intros. subst f. extract. solverec. }
  evar (mSize : X -> nat). [mSize]:intros n0. evar (steps : X -> nat). [steps]:intros n0.
  eapply reducesPolyMO_intro with  (f := fun x => (lam (extT f (enc x) 0), mSize x (*)f__Rbal' (size (enc x))*), steps x (*time__R' (size (enc x) + f__Rbal' (size (enc x))+4)+5*)));cbn [fst snd GenNPBool].
  2:{
    intros x. split.
   +intros (c&HR & Hle)%(complete__pCR R__spec). cbn - [GenNPBool] in Hle|-*.
    unfold GenNPBool;cbn [snd].
    split. now Lproc.
    exists c. split.
    *rewrite Hle. cbn. set (size (enc x)). unfold mSize;reflexivity.
    *eapply evalIn_mono.
     {Lsimpl. unfold f. erewrite complete__decInTime. Lreflexivity. easy. }
     cbn [fst snd]. ring_simplify.
     rewrite (mono_t__R _). 2:{rewrite size_prod. cbn [fst snd]. rewrite Hle. reflexivity. }
     unfold steps. reflexivity.
   +unfold GenNPBool.
    intros (?&c&size__c&R'). eapply (sound__pCR R__spec).
    apply (correct__decInTime R__comp (x,c)).
    eapply inj_enc.
    eapply unique_normal_forms. 1,2:now Lproc.
    eapply evalLe_eval_subrelation, eval_star_subrelation in R'.
    apply star_equiv in R'. etransitivity. 2:exact R'. 
    symmetry. eapply star_equiv_subrelation. clear R'.
    change (extT f) with (ext f). now Lsimpl.
  }
  -evar (f':nat -> nat). [f']:refine (fun x => _). subst mSize steps.   
   eexists (fun x => f' x). 
   +extract.
    recRel_prettify2. cbn [size]. set (size (enc x)). unfold f'. reflexivity. 
   +subst f'. cbn beta. unfold add_time. smpl_inO. all:eapply inOPoly_comp. all: try solve_proper. all:try setoid_rewrite size_nat_enc. all:smpl_inO.
   + subst f'. cbn beta. all:try setoid_rewrite size_nat_enc. solve_proper.
   + eexists (fun x => _);repeat split.
    * intros.
      repeat (setoid_rewrite -> size_prod;cbn[fst snd]).
      rewrite !size_nat_enc,!size_term_enc. cbn [size]. 
      generalize (size (enc x)). intros. reflexivity.
    * smpl_inO. apply inOPoly_comp; [exact mono_t__R | exact poly_t__R | smpl_inO].
    * solve_proper.
Qed.

From Undecidability.L.Functions Require Import Proc.
From Complexity.L.AbstractMachines.Computable Require Import EvalForTimeBool.
Import EvalForTime LargestVar.
Import N. Import L_facts. Import Nat.

Lemma inNP_GenNPBool : inNP GenNPBool.
Proof.
  eexists (fun x (c:term) => exists (s':term) (maxSize steps :nat), 
               x = (s',maxSize,steps) /\ proc s' /\ size (enc c) <= maxSize 
               /\ s' (enc c) ⇓(<=steps) (enc true)).
  {
    evar (f__t : nat -> nat). [f__t]:intro n.
    eexists f__t. repeat eapply conj. split. 
    eexists (fun '((s',maxSize,steps),c) =>
               if closedb s' && lambdab s' && (size (enc c) <=? maxSize)
               then
                 evalForTimeBool true (N.of_nat steps) (s' (enc c))
               else false).
    -  extract. intros [[[s' maxSize] steps] c].
     remember (size (enc (s', maxSize, steps, c))) as n.
     assert (H1 : ( L_facts.size (enc s') <= n)) by (subst n;rewrite !size_prod;cbn;lia).
     assert (H2 : ( size (enc maxSize) <= n)) by (subst n;rewrite !size_prod;cbn;lia).
     assert (H3 : ( size (enc steps) <= n)) by (subst n;rewrite !size_prod;cbn;lia).
     assert (H4 : ( size (enc c) <= n)) by (subst n;rewrite !size_prod;cbn;lia).
     solverec.
     all: unfold leb_time. 
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
    -intros [[[s' maxSize] steps] c]. cbn [fst snd uncurry]. unfold proc. 
     destruct (closedb_spec s');cbn [andb]. 2:{ split;[|congruence];intros (?&?&?&[= -> -> ->]&?);tauto. }
     destruct (lambdab_spec s');cbn [andb]. 2:{ split;[|congruence];intros (?&?&?&[= -> -> ->]&?);tauto. }

     destruct (Nat.leb_spec0 (size (enc c)) maxSize);cbn [andb]. 2:{ split;[|congruence];intros (?&?&?&[= -> -> ->]&?);tauto. }
     eapply reflect_iff.
     eapply ssrbool.equivP. eapply evalForTimeBool_spec.
     rewrite  !Nnat.Nat2N.id.
     split.
     +cbn. intuition eauto 10. 
     +intros (?&?&?&[= -> -> ->]&?). intuition eauto 10. Lproc.
    -unfold f__t. smpl_inO.
    -unfold f__t. solve_proper.
  }
  eexists (fun x => x).
  3: smpl_inO.
  3: solve_proper.
  all:intros ((?,?),?). all:cbn.
  -intros ? (?&?&?&[= <- <- <-]&?&?&?). eauto 10.
  -intros (?&?&?&?). eexists.  split. eauto 10.  repeat setoid_rewrite size_prod. cbn [fst snd].
   rewrite <- !size_nat_enc_r. lia. 
Qed.

Lemma GenNPBool_complete :
  NPcomplete GenNPBool.
Proof.
  eauto using inNP_GenNPBool, NPhard_GenNPBool. 
Qed.
