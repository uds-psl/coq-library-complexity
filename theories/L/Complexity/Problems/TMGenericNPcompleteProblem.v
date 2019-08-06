From Undecidability.TM Require Import TM.
From Undecidability.L.TM Require Import TMflat TMflatEnc TMflatFun TMEncoding TapeDecode.
From Undecidability.L.Datatypes Require Import LNat LProd Lists.


(*** TODO: move M
  or parts of initial tape into definition? **)

Definition TMgenericNPcompleteProblem: TM*nat*nat -> Prop:=
  fun '(M,maxSize, steps (*in unary*)) =>
    exists sig n (M':mTM sig n), isFlatteningTMOf M M' /\ (exists t, (exists f, loopM (initc M' t) steps = Some f)
         /\ sizeOfmTapes t <= maxSize).

 
From Undecidability.L.Complexity Require Import NP LinTimeDecodable.
From Undecidability.L Require Import Tactics.LTactics Functions.Decoding TMflatFun.



Lemma inNP_TMgenericNPCompleteProblem:
  inNP TMgenericNPcompleteProblem.
Proof.
  apply inNP_intro with (R:= fun '(M,maxSize, steps (*in unary*)) t =>
                               exists sig n (M':mTM sig n),
                                 isFlatteningTMOf M M'
                                 /\ exists t', isFlatteningTapesOf t t'
                                         /\ (exists f, loopM (initc M' t') steps = Some f)
                                         /\ sizeOfmTapes t' <= maxSize).
  now apply linDec_polyTimeComputable.
  -evar (f':nat -> nat).
   exists f'. repeat eapply conj.
   {
     eexists (fun '((M,maxSize,steps),t) =>
                if negb (sizeOfmTapesFlat t <=? maxSize)
                then false
                else match loopMflat M (M.(start),t) steps with
                       Some _ => true
                     | _ => false
                     end).
     repeat eapply conj.
     2:{intros [[[M maxSize] steps] t]. cbn.
        destruct (Nat.leb_spec0 (sizeOfmTapesFlat t) (maxSize));cbn [negb].
        2:{ split. 2:easy.
            intros (?&?&?&?&?&?&?&?). erewrite sizeOfmTapesFlat_eq in n. 2:easy. easy.
        }
        specialize loopMflat_correct with (M:=M) (c:=(M.(start),t)) (k:=steps) as H.
        split.
        -intros (?&?&M'&?&?&?&?&?).
         specialize H with (1:=H0) (2:=initFlat_correct H0 H1).
         destruct H2.
         destruct loopMflat,loopM.
         all:try easy.
        -destruct loopMflat. 2:easy. intros _.
         
         
        term+)
     }
     all:admit.
   }
   all:admit.
  -evar (f:nat -> nat).
   exists f. repeat eapply conj.
   2:{
     intros [[TM maxSize] steps] y.
     intros (?&?&?&?&R__tapes&?&?).
     remember (size (enc (TM, maxSize, steps))) as n eqn:Hn.
     rewrite size_flatTapes. 2:eassumption.
     rewrite !size_prod,size_TM in Hn.
     destruct TM;cbn [fst snd] in Hn.
     destruct H;cbn in *. subst x0.
     unshelve erewrite ((_ : tapes <= n)) at 1 3.
     {rewrite size_nat_enc with (n:=tapes) in Hn. lia. }
     unshelve erewrite ((_ : sizeOfmTapes x2 <= n)) at 1 3.
     {rewrite size_nat_enc with (n:=maxSize) in Hn. lia. }
     unshelve erewrite ((_ : Cardinality.Cardinality x <= n)) at 1.
     {rewrite size_nat_enc with (n:=sig) in Hn. lia. }
     [f]:intros s. unfold f. reflexivity.
   }
   all:unfold f;smpl_inO.
  -unfold TMgenericNPcompleteProblem.
   intros [[] ].
   
   setoid_rewrite isFlatteningTapesOf_iff.
   split.
   +intros (?&?&?&?&?&?&?). eauto 10.
   +intros (?&?&?&?&?&?&?&?&?). eauto 10.
Admitted.
