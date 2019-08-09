From Undecidability.TM Require Import TM.
From Undecidability.L.TM Require Import TMflat TMflatEnc TMflatFun TMEncoding TapeDecode TMunflatten.
From Undecidability.L.Datatypes Require Import LNat LProd Lists.


(*** TODO: move M
  or parts of initial tape into definition? **)

Definition TMgenericNPcompleteProblem: TM*nat*nat -> Prop:=
  fun '(M,maxSize, steps (*in unary*)) =>
    exists sig n (M':mTM sig n), isFlatteningTMOf M M' /\ (exists t, (exists f, loopM (initc M' t) steps = Some f)
         /\ sizeOfmTapes t <= maxSize).

 
From Undecidability.L.Complexity Require Import NP LinTimeDecodable.
From Undecidability.L Require Import Tactics.LTactics Functions.Decoding TMflatFun.

Instance term_nat_max :
  computableTime' (Nat.max) (fun x _ => (5,fun y _ => (min x y * 15 + 8,tt))).
Proof.
  extract. solverec.
Qed.


Instance term_tapeToList sig {H:registered sig}:
  computableTime' (@tapeToList sig) (fun t _ => (sizeOfTape t*29 + 26,tt)).  
extract. solverec. all:repeat simpl_list;cbn -[plus mult]. all:solverec.
Proof.
Qed.

Instance term_length X {H:registered X}:
  computableTime' (@length X) (fun t _ => (length t * 11 + 8,tt)).  
extract. solverec.
Proof.
Qed.

Instance term_sizeOfTape sig {H:registered sig}:
  computableTime' (@sizeOfTape sig) (fun t _ => (sizeOfTape t*40 + 35,tt)).
Proof.
  extract. unfold sizeOfTape. solverec.
Qed.


Instance term_sizeOfmTapesFlat sig {H:registered sig}:
  computableTime' (@sizeOfmTapesFlat sig) (fun t _ => (sumn (map (@sizeOfTape _) t) * 55 + length t * 58 + 8,tt)).
Proof.
  assert (H' : extEq
                 (fix sizeOfmTapesFlat (ts : list (tape sig)) : nat :=
                    match ts with
                    | [] => 0
                    | t :: ts0 => Init.Nat.max (sizeOfTape t) (sizeOfmTapesFlat ts0)
                    end) (sizeOfmTapesFlat (sig:=sig))).
  { intros x. induction x;hnf;cbn. all:easy. }
  cbn [extEq] in H'.
  
  eapply computableTimeExt. exact H'.
  extract. solverec. 
Qed.

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
                if negb ((sizeOfmTapesFlat t <=? maxSize) && isValidFlatTM M && isValidFlatTapes M.(sig) M.(tapes) t)
                then false
                else match loopMflat M (M.(start),t) steps with
                       Some _ => true
                     | _ => false
                     end).
     repeat eapply conj.
     2:{intros [[[M maxSize] steps] t]. cbn.
        destruct (Nat.leb_spec0 (sizeOfmTapesFlat t) (maxSize));cbn [negb andb].
        2:{ split. 2:easy.
            intros (?&?&?&?&?&?&?&?). erewrite sizeOfmTapesFlat_eq in n. 2:easy. easy.
        }
        destruct (isValidFlatTM_spec M);cbn [negb andb].
        2:{ split. 2:easy.
            intros (?&?&?&?&?&?&?&?). eauto using isFlattening_is_valid.
        }
        destruct isValidFlatTapes eqn:eq;cbn [negb andb].
        2:{ split. 2:easy.
            intros (?&?&?&[]&?&?&?&?). destruct M;cbn in *;subst. 
            eapply flatteningTapeIsValid in H. easy.
        }
        specialize loopMflat_correct with (M:=M) (c:=(M.(start),t)) (k:=steps) as H.
        rewrite <- Card_Fint with (n:=sig M) in eq.
        eapply unflattenTM_correct in v.
        split.
        -intros (?&?&M'&?&?&?&?&?).
         specialize H with (1:=H0) (2:=initFlat_correct H0 H1).
         destruct H2.
         destruct loopMflat,loopM.
         all:try easy.
        -destruct loopMflat. 2:easy. intros _.
         eexists _,_,(unflattenTM M).
         split. now eauto using unflattenTM_correct.
         eapply isUnflattableTapes in eq as (t'&?).
         exists t'. split. easy.
         specialize H with (1:=v). split. 2:now erewrite <- sizeOfmTapesFlat_eq.
         specialize H with (c'                          :=initc (unflattenTM M) t').
         assert (H':isFlatteningConfigOf (start M, t) (initc (unflattenTM M) t')).
         {eapply initFlat_correct;easy. }
         apply H in H'. destruct loopM. 2:easy.
         eauto.
     }
     eexists.

(*
     Instance term_allSameEntry X Y {HX:registered X} {HY:registered Y}:
       computableTime' (@allSameEntry X Y) (fun _ t__X => (1,fun _ t__Y => (1, fun x _ => (1, fun y _ => (1,fun f _ => (cnst 0,tt)))))).
     Proof.
       extract. *)
     
     Print allSameEntry.
     Print isInjFinfuncTable.
     Print isValidFlatTrans.
     Print isValidFlatTM.
     Fail now extract. all:admit. 
   }
   all:admit.
  -evar (f:nat -> nat).
   exists f. repeat eapply conj.
   2:{
     intros [[TM maxSize] steps] y.
     intros (?&?&?&?&?&R__tapes&?&?).
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
