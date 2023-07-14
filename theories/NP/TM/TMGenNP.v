From Undecidability.TM Require Import TM_facts.
From Undecidability.L.TM Require Import TMEncoding.
From Complexity.L.TM Require Import TMflat TMflatEnc TMflatFun TapeDecode TMunflatten.
From Undecidability.L.Datatypes Require Import LNat LProd Lists.
From Complexity.Complexity Require Import NP LinTimeDecodable ONotation.
From Undecidability.L Require Import Tactics.LTactics.
From Undecidability.L Require Import Functions.Decoding.
From Complexity.L Require Import TMflatFun TMflatComp.
From Undecidability Require Import L.Functions.EqBool.
From Undecidability Require Import L.Datatypes.LNat.

(** Using this problem to establish NP-hardness as by Cook-levin would require us to construct TMs from L-terms. We don't want to do this. Instead, we define another problem (GenNPHalt_fixed_mTM) where the machine itself and some tape content is fixed, but a single tape has arbitrary content on it. *)

(* Factorise proof over GenNP? *)
Definition TMGenNP' sig n : TM sig n * nat * nat -> Prop :=
  fun '(M, k, steps) =>
    exists tp, sizeOfmTapes tp <= k
          /\ exists f, loopM (initc M tp) steps = Some f.

Definition TMGenNP: flatTM*nat*nat -> Prop:=
  fun '(M,maxSize, steps (*in unary*)) =>
    (exists sig n (M':TM sig n), isFlatteningTMOf M M' /\ TMGenNP' (M',maxSize,steps)).

Definition TM1GenNP : {'(M,_,_) | M.(TMflat.tapes) = 1} -> Prop :=
  (fun '(exist (M,maxSize, steps (*in unary*)) _) => exists sig (M':TM sig 1), isFlatteningTMOf M M' /\ TMGenNP' (M', maxSize, steps)).

Lemma inNP_TMgenericNPCompleteProblem: inNP TMGenNP.
Proof.
  pose (R := fun '(M,maxSize, steps (*in unary*)) t =>
               sizeOfmTapesFlat t <= maxSize /\  
               exists sig n (M':TM sig n),
                 isFlatteningTMOf M M'
                 /\ exists t', isFlatteningTapesOf t t'
                         /\ (exists f, loopM (initc M' t') steps = Some f)).
  apply inNP_intro with (R:= R).
  now apply linDec_polyTimeComputable.
  -destruct execFlat_poly as (f''&Hf''&polyf''&monof'').
   evar (f':nat -> nat). [f']:intro x.
   exists f'. repeat eapply conj.
   { split. cbn. 
     eexists (fun '((M,maxSize,steps),t) =>
                if (sizeOfmTapesFlat t <=? maxSize)
                then match execFlatTM M t steps with
                       Some _ => true
                     | _ => false
                     end
                else false).
     repeat eapply conj.
     2:{intros [[[M maxSize] steps] t]. cbn.
        destruct (Nat.leb_spec0 (sizeOfmTapesFlat t) (maxSize));cbn [negb andb].
        2:{ split. 2:easy. intros (?&?&?&?&?&?&?&?). easy. }
        specialize (execFlatTM_correct M t steps) as H.
        destruct execFlatTM as [c| ] eqn:Hexec. all:split. 1,4:easy.
        -intros. specialize (H c). destruct H as [H _]. specialize H with (1:= Logic.eq_refl) as (?&?&?&?&?&?&Hc&?&?).
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
     extract. 
     recRel_prettify.
     intros [[[M maxSize] steps] t] [].
     split;[ |now repeat destruct _].
     rewrite sizeOfmTapesFlat_timeBySize.
     unfold leb_time. rewrite Nat.le_min_r.
     unfold sizeOfmTapesFlat_timeSize.
     remember (size (enc (M, maxSize, steps, t))) as x.

     assert (Ht : size (enc t) <= x).
     { subst x. rewrite !size_prod. cbn [fst snd]. lia. }
     rewrite Ht.

     assert (Hms : maxSize <= x).
     { subst x. rewrite !size_prod. cbn [fst snd]. rewrite <- size_nat_enc_r. lia. }
     rewrite Hms at 1.
     
     
     destruct (Nat.leb_spec (sizeOfmTapesFlat t) maxSize).
     rewrite Hf''.
     setoid_replace (size (enc M) + sizeOfmTapesFlat t + steps) with x
      using relation le.
     2:{rewrite H. subst x. rewrite !size_prod. cbn [fst snd]. rewrite <- !size_nat_enc_r. lia. }
     destruct execFlatTM.
     all:unfold f'.
     reflexivity.
     all:lia.
   }
   + unfold f'. smpl_inO.
   + unfold f'. solve_proper.
  -evar (f:nat -> nat). [f]:intro x.
   exists f.
   +intros [[TM maxSize] steps] y.  cbn.
    intros (?&sig&n&M'&HM&t' & Ht' & HHalt) .
    eexists _,_,_. split. easy. eexists. split. now erewrite <- sizeOfmTapesFlat_eq. easy.
   +intros [[TM maxSize] steps]. cbn.
    intros (sig&n&M'&HM&t' & Ht' & HHalt) .
    eexists _. split.
    *split. now erewrite sizeOfmTapesFlat_eq.
     eauto 10 using mkIsFlatteningTapeOf.
    *remember (size (enc (TM, maxSize, steps))) as x eqn:Hn.
     rewrite size_flatTapes. 2:now apply mkIsFlatteningTapeOf.
     rewrite Ht'.
     assert (n <= x /\ maxSize <= x /\ | elem sig | <= x) as (->&->&->).
     {inv HM;destruct TM; cbn in *. rewrite !size_prod,size_TM;cbn [fst snd].
      repeat apply conj.
      all:rewrite size_nat_enc_r at 1; subst;nia.
     }
     unfold f;reflexivity.
   + unfold f;smpl_inO.
   + unfold f. solve_proper.
Qed.
