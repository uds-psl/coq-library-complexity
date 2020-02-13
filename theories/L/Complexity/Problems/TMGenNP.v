From Undecidability.TM Require Import TM.
From Undecidability.L.TM Require Import TMflat TMflatEnc TMflatFun TMEncoding TapeDecode TMunflatten TMflatFun TMflatComp TMinL.
From Undecidability.L.Datatypes Require Import LNat LProd Lists.
From Undecidability.L.Complexity Require Import NP LinTimeDecodable ONotation.
From Undecidability.L Require Import Tactics.LTactics Functions.Decoding TMflatFun.
From Undecidability Require Import L.Functions.EqBool.
From Undecidability Require Import L.Datatypes.LNat.

(* Factorise proof over GenNP? *)
Definition TMGenNP' sig n : mTM sig n * nat * nat -> Prop :=
  fun '(M, k, steps) =>
    exists tp, sizeOfmTapes tp <= k
          /\ exists f, loopM (initc M tp) steps = Some f.

Definition TMGenNP: TM*nat*nat -> Prop:=
  fun '(M,maxSize, steps (*in unary*)) =>
    (exists sig n (M':mTM sig n), isFlatteningTMOf M M' /\ TMGenNP' (M',maxSize,steps)).

Definition TM1GenNP := restrictBy (fun '(M,_,_) => M.(TMflat.tapes) = 1)
  (fun '(M,maxSize, steps (*in unary*)) => exists sig (M':mTM sig 1), isFlatteningTMOf M M' /\ TMGenNP' (M', maxSize, steps)).


Lemma inNP_TMgenericNPCompleteProblem:
  inNP (unrestrictedP TMGenNP).
Proof.
  apply inNP_intro with (R:= fun '(M,maxSize, steps (*in unary*)) t =>
                               sizeOfmTapesFlat t <= maxSize /\  
                               exists sig n (M':mTM sig n),
                                 isFlatteningTMOf M M'
                                 /\ exists t', isFlatteningTapesOf t t'
                                         /\ (exists f, loopM (initc M' t') steps = Some f)).
  now apply linDec_polyTimeComputable.
  -destruct execFlat_poly as (f''&Hf''&polyf''&monof'').
   evar (f':nat -> nat). [f']:intro x.
   exists f'. repeat eapply conj.
   {
     eexists (fun '((M,maxSize,steps),t) =>
                if (sizeOfmTapesFlat t <=? maxSize)
                then match execFlatTM M t steps with
                       Some _ => true
                      | _ => false
                     end
                else false).
     repeat eapply conj.
     2:{intros [[[M maxSize] steps] t] []. cbn.
        destruct (Nat.leb_spec0 (sizeOfmTapesFlat t) (maxSize));cbn [negb andb].
        2:{ split. 2:easy. intros (?&?&?&?&?&?&?&?). easy. }
        specialize (execFlatTM_correct M t steps) as H.
        destruct execFlatTM as [c| ] eqn:Hexec. all:split. 1,4:easy.
        -intros. specialize (H c). destruct H as [H _]. specialize (H eq_refl) as (?&?&?&?&?&?&Hc&?&?).
         split. easy.
         do 4 esplit. eauto.
         inv Hc. cbn in *.
         do 2 esplit. eauto.
         destruct x2. cbn in *.
         eexists. rewrite <- H1. unfold initc. repeat f_equal. inv H. apply injective_index. congruence.
        -intros (?&?&?&?&?&?&?&?&?). exfalso.
         edestruct H as [_ H']. discriminate H'.
         do 6 eexists. now eauto.
         split. now eauto using initFlat_correct.
         split. eauto. instantiate (1 := (_,_)).
         split;cbn. constructor.
     }
     eexists.
     extract. 
     recRel_prettify.
     intros [[[M maxSize] steps] t] [].
     split;[ |now repeat destruct _].
     rewrite sizeOfmTapesFlat_timeBySize.
     rewrite Nat.le_min_r.
     unfold sizeOfmTapesFlat_timeSize.
     remember (size (enc (M, maxSize, steps, t))) as x.

     assert (Ht : size (enc t) <= x).
     { subst x. rewrite !size_prod. cbn [fst snd]. lia. }
     rewrite Ht.

     assert (Hms : maxSize <= x).
     { subst x. rewrite !size_prod. cbn [fst snd]. rewrite <- size_nat_enc_r. lia. }
     rewrite Hms at 1.
     
     
     destruct (Nat.leb_spec (sizeOfmTapesFlat t) maxSize).
     rewrite Hf''. hnf in monof''. rewrite monof'' with (x':=x).
     2:{rewrite H. subst x. rewrite !size_prod. cbn [fst snd]. rewrite <- !size_nat_enc_r. lia. }
     destruct execFlatTM.
     all:unfold f'.
     reflexivity.
     all:lia.
   }
   all:unfold f'.
   all:smpl_inO.
  -evar (f:nat -> nat). [f]:intro x.
   exists f. repeat eapply conj.
   2:{
     intros [[TM maxSize] steps] y.
     intros (?&sig&n&M'&HM&R__tapes&?&?).
     remember (size (enc (TM, maxSize, steps))) as x eqn:Hn.
     rewrite size_flatTapes. 2:eassumption.
     rewrite !size_prod,size_TM in Hn;cbn [fst snd] in Hn.
     inversion HM. subst n.
     destruct TM. cbn in *. rewrite !size_nat_enc in Hn.
     unshelve erewrite ((_ : tapes <= x)) at 1 3. lia.
     unshelve erewrite ((_ : Cardinality.Cardinality sig <= x)) at 1 3. lia.
     erewrite <- sizeOfmTapesFlat_eq. 2:eassumption.
     rewrite H.
     unshelve erewrite ((_ : maxSize <= x)) at 1 3. nia.
     unfold f. reflexivity.
   }
   all:unfold f.
   all:smpl_inO.
  -unfold TMGenNP.
   intros [[] ].
   
   setoid_rewrite isFlatteningTapesOf_iff.
   split.
   +intros (?&?&?&?&?&?&?&?). erewrite <- ?sizeOfmTapesFlat_eq in *. eauto 10. constructor.
   +intros (?&?&?&?&?&?&?&?&?). cbn. erewrite ?sizeOfmTapesFlat_eq in *. eauto 20. subst;constructor.
Qed.
