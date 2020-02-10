From Undecidability.L Require Import L.
From Undecidability.L.Datatypes Require Import LProd LTerm LBool.
From Undecidability.L.Complexity Require Import NP Synthetic Monotonic GenNP.
From Undecidability.L.Functions Require Import Size.

Definition GenNPHalt : term*nat*nat -> Prop :=
  fun '(s, maxSize, steps (*in unary*)) =>
    closed s /\
    exists (c:term), size (enc c) <= maxSize
                /\ exists t, s (enc c) ⇓(<=steps) t.

Lemma NPhard_GenNP : NPhard (unrestrictedP GenNPHalt).
Proof.
  intros X reg__X ? Q [(*? ?*) R R__dec (f__Rbal&polyf__Rbal&bounds_f__Rbal&mono_f__Rbal) R__spec].
  destruct R__dec as (t__R&[d__R [comp_d__R] spec_d__R]&poly_t__R&mono_t__R).
  pose (f x := fun c => d__R (x,c)).
  assert (computableTime' f (fun x _ => (1,fun c _ => (t__R (size (enc (x, c))) + 3,tt))));cbn [timeComplexity] in *.
  {intros. subst f. extract. solverec. }
  specialize inOPoly_computable with (1:=polyf__Rbal) as (f__Rbal'&tf__Rbal'&[]&polyf__Rbal'&leq_f__Rbal'&?&?&?).
  specialize inOPoly_computable with (1:=poly_t__R) as (t__R'&tt__R'&[]&poly_t__R'&leq_t__R'&?&?&?).
  exists (fun x => (lam (trueOrDiverge (extT f (enc x) 0)),f__Rbal' (size (enc x)),t__R' (size (enc x) + f__Rbal' (size (enc x))+4)+9));cbn [fst snd GenNP]. 3:easy. 
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
  -intros x ?.
   rewrite R__spec. 2:easy. split.
   +intros (c&H'). specialize (spec_d__R (x,c)). apply ssreflect.iffLR with (2:=H') in spec_d__R. 2:easy. 
    unfold GenNPHalt.
    split. now Lproc.
    exists c. repeat split. 
    *rewrite bounds_f__Rbal. 2:eassumption. easy.
    *exists I. split. 2:Lproc. 
     eapply le_redLe_proper. 2,3:reflexivity.
     2:{eapply redLe_trans_eq.
        2:now Lsimpl.
        2:{unfold f. rewrite spec_d__R. Lsimpl.
        }
     cbn [fst snd]. reflexivity. }
     ring_simplify.
     rewrite <- leq_t__R'. cbn.
     rewrite size_prod. cbn [fst snd].
     hnf in mono_t__R;rewrite mono_t__R. reflexivity.
     rewrite bounds_f__Rbal. 2:eassumption.
     rewrite leq_f__Rbal'. reflexivity.
   +unfold GenNPHalt.
    intros (?&c&size__c&?&R'%redLe_star_subrelation&?).    
    exists c. specialize (spec_d__R (x,c)). cbn in spec_d__R. rewrite spec_d__R. 2:easy. 
    eapply trueOrDiverge_eval with (t:=x0).
    eapply equiv_eval_proper. 2:reflexivity. 2:apply eval_refl;Lproc.
    rewrite <- R'. clear R'.
    apply star_equiv.
    Lbeta. eapply redLe_star_subrelation. Lsimpl.
Qed.
