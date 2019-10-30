From Undecidability.TM Require Import TM.
From Undecidability.L.TM Require Import TMflat TMflatEnc TMflatFun TMEncoding TapeDecode TMunflatten TMflatFun TMflatComp.
From Undecidability.L.Datatypes Require Import LNat LProd Lists.


(*** TODO: move M
  or parts of initial tape into definition? **)

Definition TMgenericNPcompleteProblem: TM*nat*nat -> Prop:=
  fun '(M,maxSize, steps (*in unary*)) =>
    exists sig n (M':mTM sig n), isFlatteningTMOf M M' /\ (exists t, (exists f, loopM (initc M' t) steps = Some f)
         /\ sizeOfmTapes t <= maxSize).


From Undecidability.L.Complexity Require Import NP LinTimeDecodable.
From Undecidability.L Require Import Tactics.LTactics Functions.Decoding TMflatFun.


From Undecidability Require Import L.Functions.EqBool.

From Undecidability Require Import L.Datatypes.LNat.
Instance term_isValidFlatTM : computableTime' isValidFlatTM (fun M _ => (size (enc M) ^ 2 * (c__eqbComp nat + c__eqbComp (nat * list (option nat)) +  c__eqbComp (nat * list (option nat * move)) + 20)*9,tt)).
Proof.
  unfold isValidFlatTM. unfold Nat.ltb.
  extract.
  intros M _. 
  clear. split. 2:easy. remember mult as f' eqn:eq'. ring_simplify. subst f'.
  cbn - [plus mult].  remember mult as f' eqn:eq'. ring_simplify. subst f'.
  rewrite Nat.le_min_r. rewrite size_nat_enc_r with (n:=states M).

  assert (H1:size (enc (trans M)) <= size (enc M)) by (rewrite size_TM;destruct M;cbn;lia).
  assert (H2:size (enc (states M)) <= size (enc M)) by (rewrite size_TM;destruct M;cbn;lia).
  assert (H3:1 <= size (enc M)) by (rewrite size_TM;destruct M;cbn;lia).

  (* assert (H4:size (enc (trans M)) <= size (enc M)) by (rewrite size_TM;destruct M;cbn;lia). *)
  (* assert (H5:size (enc (trans M)) <= size (enc M)) by (rewrite size_TM;destruct M;cbn;lia). *)
  (* assert (H6:size (enc (trans M)) <= size (enc M)) by (rewrite size_TM;destruct M;cbn;lia). *)
  (* assert (H1:size (enc (trans M)) <= size (enc M)) by (rewrite size_TM;destruct M;cbn;lia). *)


  Lemma size_list_enc_r X `{registered X} (l:list X):
    length l <= size (enc l)*5 + 4.
  Proof.
    rewrite size_list. induction l;cbn. all:lia.
  Qed.

  rewrite !size_list_enc_r with (l:=trans M). Unshelve. 2:exact _.
  rewrite !H1. rewrite !H2. ring_simplify.
  nia.
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

     (* TODO: size flat TM *)
     
     
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
