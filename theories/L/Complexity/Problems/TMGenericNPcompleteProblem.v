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
extract. recRel_prettify2. all:repeat (simpl_list;cbn -[plus mult]). all:nia.
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

Fixpoint forallb_time {X} (fT:X -> nat) xs :=
  match xs with
    [] => 8
  | x :: xs => fT x + forallb_time fT xs + 15
  end.

Lemma forallb_time_eq X f (l:list X):
  forallb_time f l = sumn (map f l) + length l * 15 + 8.
Proof.
  induction l;cbn;nia.
Qed.

Lemma forallb_time_const X c (l:list X):
  forallb_time (fun _ =>  c) l = length l * (c+15) + 8.
Proof.
  induction l;cbn;nia.
Qed.

Instance term_forallb X {HX:registered X}:
  computableTime' (@forallb X) (fun f t__f => (1,fun l _ => (forallb_time (fun x => fst (t__f x tt)) l,tt))).
Proof.
  extract.
  solverec.
Qed.

From Undecidability Require Import L.Functions.EqBool.

Definition allSameEntry_helper {X Y} eqbX eqbY `{_:eqbClass (X:=X) eqbX} `{eqbClass (X:=Y) eqbY}
  := fun x y '(x', y') => implb (eqbX x (x':X)) (eqbY y (y':Y)).

Instance term_allSameEntry_helper {X Y} {HX:registered X} {HY:registered Y}
         `{eqbCompT X (R:=HX)} `{eqbCompT Y (R:=HY)}
  :
    computableTime' (@allSameEntry_helper X Y _ _ _ _) (fun x _ => (1,fun y _ =>(1,fun xy _ => (eqbTime x (fst xy) + eqbTime y (snd xy) + 18,tt)))).
Proof.
  unfold allSameEntry_helper. unfold implb. extract. solverec.
Qed.

Instance term_allSameEntry X Y {HX:registered X} {HY:registered Y}
         `{eqbCompT X (R:=HX)} `{eqbCompT Y (R:=HY)}:
  computableTime' (@allSameEntry X Y _ _ _ _) (
                    fun x _ => (1,
                             fun y _ => (1,
                                      fun f _ =>(
                                          length f * (size (enc x)*c__eqbComp X + size (enc y)* c__eqbComp Y + 42) + 12,tt)))).

Proof.
  unfold allSameEntry.
  change (fun (x : X) (y : Y) (f : list (X * Y)) => forallb (fun '(x', y') => implb (eqb0 x x') (eqb1 y y')) f)with
      (fun (x : X) (y : Y) f => forallb (allSameEntry_helper x y)  f).
  extract.
  recRel_prettify2. 1-2:easy.
  clear.
  rename x1 into f.
  
  change 12 with (8+4) at 3. rewrite !Nat.add_assoc. eapply plus_le_compat_r.
  
  induction f as [ | [x' y'] f].
  { easy. }
  cbn - [plus mult] . unfold eqbTime. rewrite IHf.
  nia.
Qed.

Instance term_isInjFinfuncTable X Y {HX:registered X} {HY:registered Y}
         `{eqbCompT X (R:=HX)} `{eqbCompT Y (R:=HY)}:
  computableTime' (@isInjFinfuncTable X Y _ _ _ _) (fun f _ => (length f * (size (enc f) * (c__eqbComp X + c__eqbComp Y + 5)) + 8,tt)).
Proof.
  unfold isInjFinfuncTable. cbn. extract.
  solverec. subst.
  cbn [length]. rewrite !size_list. cbn [map sumn]. rewrite !size_prod. cbn [fst snd]. nia.
Qed.

Definition isBoundRead sig := fun a : option nat => match a with
                                               | Some a0 => a0 <? sig
                                               | None => true
                                               end.
Definition isBoundWrite sig := (fun a : option nat * move => match fst a with
                                                        | Some a0 => a0 <? sig
                                                        | None => true
                                                        end).
Lemma size_option X {_:registered X} (o:option X) :
  size (enc o)= match o with
                  None => 3
                | Some x => size (enc x) + 5
                end.
Proof.
  change (enc o) with (LOptions.option_enc o).
  destruct o.
  all:cbn [LOptions.option_enc map sumn size].
  all:solverec. 
Qed.

Instance term_isBoundRead:
  computableTime' isBoundRead (fun sig _ => (1, fun s _ => (size (enc s) * 4,tt))).
Proof.
  unfold isBoundRead,Nat.ltb. extract. solverec.
  
  all:rewrite size_option.
  all:try rewrite size_nat_enc. all:solverec. 
Qed.

Instance term_isBoundWrite:
  computableTime' isBoundWrite (fun sig _ => (1, fun s _ => (size (enc s) * 4,tt))).
Proof.
  unfold isBoundWrite,Nat.ltb. extract.
  recRel_prettify2.
  all:try rewrite size_prod;cbn [fst snd] in *;subst;repeat rewrite size_option,!size_nat_enc. all:solverec. 
Qed.

Definition isBoundEntry sig n states: (nat * list (option nat) * (nat * list (option nat * move))) -> bool:= 
  (fun '(s, v, (s', v')) =>
     (s <? states)
       && (| v | =? n)
       && forallb (isBoundRead sig) v
       && (s' <? states) && (| v' | =? n) &&
       forallb (isBoundWrite sig) v').

Lemma sumn_map_add X f g (l:list X) :
  sumn (map (fun x => f x + g x) l) = sumn (map f l) + sumn (map g l).
Proof.
  induction l;cbn;nia.
Qed.
Lemma sumn_map_mult_c_r X f c (l:list X) :
  sumn (map (fun x => f x *c) l) = sumn (map f l)*c.
Proof.
  induction l;cbn;nia.
Qed.
Lemma sumn_map_c X c (l:list X) :
  sumn (map (fun _ => c) l) = length l * c.
Proof.
  induction l;cbn;nia.
Qed.

Instance term_isBoundEntry:
  computableTime' isBoundEntry (fun sig _ => (1,
                                           fun n _ => (1,
                                                    fun states _ => (1,
                                                                  fun e _ => 
                                                                    (size (enc e)* (8+c__eqbComp nat),tt))))).
Proof.
  unfold isBoundEntry, Nat.ltb. extract. 
  
  recRel_prettify2. 1-3:nia. 
  all:rewrite !size_prod;cbn [fst snd].
  all:rewrite !forallb_time_eq. 
  all:rewrite !size_list.
  
  
  all:rewrite !sumn_map_add,!sumn_map_mult_c_r,!sumn_map_c.
  all:unfold eqbTime.
  all:rewrite !Nat.le_min_l.
  all:rewrite !size_nat_enc. all:zify. all:clear; nia. 
Qed.

Instance term_isBoundTransTable:
  computableTime' isBoundTransTable (fun _ _ => (1,
                                              fun _ _ => (1,
                                                       fun _ _ => (1,
                                                                fun f _ => 
                                                                  (size (enc f)* (8+c__eqbComp nat),tt))))).
Proof.
  unfold isBoundTransTable.
  eapply computableTimeExt with (x:=fun sig n states f => forallb (isBoundEntry sig n states) f).
  {reflexivity. }
  extract.
  solverec.
  rewrite forallb_time_eq.
  rewrite !size_list.
  rewrite !sumn_map_mult_c_r.
  rewrite !sumn_map_add, !sumn_map_c.
  all:ring_simplify. zify. clear; nia.
Qed.

Instance term_isValidFlatTrans:
  computableTime' (isValidFlatTrans) (fun _ _ => (1,
                                               fun _ _ => (1,
                                                        fun states_ _ => (1,
                                                                       fun f _ => 
                                                                         (size (enc f)* (8+c__eqbComp nat + length f * (c__eqbComp (nat*(list (option nat)))
                                                                                                                    + c__eqbComp (nat*(list (option nat * move))) + 5))+ 17,tt))))).
Proof.
  unfold isInjFinfuncTable. cbn. extract.
  solverec.
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
