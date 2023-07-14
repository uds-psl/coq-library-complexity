From Undecidability.L Require Import Tactics.LTactics.
From Undecidability.L.Datatypes Require Import Lists LVector.
From Complexity.Libs Require Import PSLCompat.
From Complexity.Complexity Require Import NP Definitions Monotonic.
From Undecidability.TM Require Import TM_facts.
From Complexity.L.AbstractMachines Require Import FlatPro.Computable.LPro.
From Undecidability.L.AbstractMachines Require Import FlatPro.Programs.
From Complexity.NP Require Import LMGenNP TMGenNP_fixed_mTM M_LM2TM.

From Undecidability.TM.L Require M_LHeapInterpreter.

Set Default Proof Using "Type".

From Undecidability Require Import LSum.
From Complexity Require Import L.TM.CompCode.

From Undecidability Require Import Alphabets.

Import ProgrammingTools.

Module TrueOrDiverge.
  Import TM.TM ProgrammingTools CaseList CaseBool Code.Decode Code.DecodeList.

  Section sec.
    Variable (n:nat) (sig : finType) (M' : pTM sig bool n).

    Definition M := If M' Nop Diverge.

    Lemma Realise R' (H' : M' ⊨ R'):
      M ⊨ (fun tin out => R' tin (true,snd out)).
    Proof.
      eapply Realise_monotone.
      { eapply If_Realise. eassumption. now TM_Correct. now apply Diverge_Realise. }
      hnf. intros x [[] y]. intros [H|H].
      -cbn in H. destruct H as (?&?&<-). easy.
      -exfalso. cbn in H. firstorder.
    Qed.

    Import TM.

    Lemma Terminates R' (HR' : M' ⊨ R') T' (HT' : projT1 M' ↓ T'):
      projT1 M ↓ (fun tin k => T' tin (k-1) /\ 0 < k /\ forall tout, ~ R' tin (false,tout)).
    Proof.
      eapply TerminatesIn_monotone.
      { eapply If_TerminatesIn. 1,2:eassumption. now TM_Correct. now apply Canonical_TerminatesIn. }
      intros tin [] (HTtin&Hfalse). easy.
      do 2 eexists;repeat simple apply conj. eassumption.
      2:{ intros ? ? ?. destruct b. reflexivity. now exfalso. }
      nia.
    Qed.
  End sec.
End TrueOrDiverge.


Arguments LMtoTM.M : clear implicits.


(*move*)
Lemma initValue_sizeOfTape (sig sigX X : Type) (cX : codable sigX X) (I : Retract sigX sig) (x : X):
  sizeOfTape (initValue cX I x) = size x + 2.
Proof.
  cbn. autorewrite with list. cbn. now unfold size.
Qed.


Lemma initRight_sizeOfTape sig :
  sizeOfTape (initRight sig) = 1.
Proof.
  cbn. nia.
Qed.

Module M.
  Section M.
    Arguments LMtoTM.M : clear implicits.
    Definition sig := (finType_CS (M_LHeapInterpreter.sigStep + sigList bool)).

    Definition sig__reg : encodable sig := LFinType.encodable_finType.

    Definition Retr1 : Retract _ sig := (Retract_inl _ (Retract_id _)).
    Definition Retr2 : Retract _ sig := (Retract_inr _ (Retract_id _)).

    Let n := 11.
    Definition M : pTM _ _ n := TrueOrDiverge.M (LMtoTM.M sig Retr1 Retr2).
    Definition ts__start : Pro -> tapes (sig^+) (n-1) :=
      (fun P => CodeTM.initValue _ (@LMtoTM.retr__pro _ Retr1) P ::: Vector.const (CodeTM.initRight _) (n-2)).

    Definition Rel : pRel (sig ^+) unit 11 :=
      fun tin _ =>
        forall P t__cert, tin = t__cert:::ts__start P
                   -> exists bs : list bool,
            t__cert ≃(Retr2) bs /\
            (exists (sigma' : LM_heap_def.state) (k : nat), evaluatesIn LM_heap_def.step k (initLMGen P (compile (enc (rev bs)))) sigma').


    Definition Realise :
      M ⊨
        (fun tin _ =>
           forall P t__cert, tin = t__cert:::ts__start P
                      -> exists bs : list bool,
               t__cert ≃(Retr2) bs /\
               (exists (sigma' : LM_heap_def.state) (k : nat), evaluatesIn LM_heap_def.step k (initLMGen P (compile (enc (rev bs)))) sigma')).
    Proof.
      unfold M. eapply Realise_monotone.
      1:now eapply TrueOrDiverge.Realise, LMtoTM.Realise.
      intros ? out H P t__cert ->. hnf in H|-*. specialize (H P).
      apply H.
      -apply CodeTM.initValue_contains.
      -intros ?. cbn - [Vector.const]. rewrite Vector.const_nth. now apply CodeTM.initRight_isVoid.
    Qed.

    Definition time := @f__UpToC _ _ (projT1 (@LMtoTM._Terminates sig Retr1 Retr2)).

    Definition Terminates :
      projT1 M ↓ (fun tin k => 0 < k /\
                            exists P k__LM t__cert (bs : list bool),
                              tin = t__cert ::: ts__start P
                              /\ t__cert ≃(Retr2) bs
                              /\ (exists sigma' : LM_heap_def.state, evaluatesIn LM_heap_def.step k__LM (initLMGen P (compile (enc (rev bs)))) sigma')
                              /\ time (k__LM, sizeOfmTapes tin) <= k-1).
    Proof.
      unfold M. eapply TerminatesIn_monotone.
      {eapply TrueOrDiverge.Terminates. now apply LMtoTM.Realise. apply LMtoTM.Terminates. }
      intros tin k (HkPos&P&k__LM&t__cert&bs&->&Ht__cert&HLM&Htime). unfold LMtoTM.Ter.
      split.
      2:{ split. easy. unfold LMtoTM.Rel. intros _ H. eapply (H P).
          -apply CodeTM.initValue_contains.
          -intros ?. cbn - [Vector.const]. rewrite Vector.const_nth. now apply CodeTM.initRight_isVoid.
          -eauto.
      }
      exists P,k__LM.
      repeat simple apply conj.
      -apply CodeTM.initValue_contains.
      -intros ?. cbn - [Vector.const]. rewrite Vector.const_nth. now apply CodeTM.initRight_isVoid.
      -right. exists bs;split. all:easy.
      -eassumption.
    Qed.
  End M.

    
  Lemma sizeStart t__cert P:
    sizeOfmTapes (t__cert ::: M.ts__start P)
    = max (sizeOfTape t__cert) (size P + 2).
  Proof.
    unfold sizeOfmTapes. rewrite Vector.fold_left_right_assoc_eq. 2:nia. cbn - [Vector.const initValue initRight].
    rewrite <- Vector.fold_left_right_assoc_eq.  2:nia.
    set (tmp:= VectorDef.const _ _). change (VectorDef.fold_left _ _ _) with (sizeOfmTapes tmp).
    rewrite initValue_sizeOfTape.
    replace (sizeOfmTapes tmp) with 1. nia.
    subst tmp. clear.
    unfold sizeOfmTapes. rewrite Vector.fold_left_right_assoc_eq. 2:nia.
    generalize 8 as x. induction x.
    -reflexivity.
    -cbn in *. now rewrite <- IHx.
  Qed.
    
    
End M.


From Complexity Require Import PolyTimeComputable.

(* TODO MOVE :tidy up *)
Lemma pTC_length X `{encodable X}: polyTimeComputable (@length X).
Proof.
  evar (time:nat -> nat).
  eexists time.
  { eapply computableTime_timeLeq. 2:exact _.
    solverec. rewrite size_list_enc_r. set (n:=L_facts.size _). [time]:refine (fun n => _). unfold time. reflexivity.
  }
  - unfold time. smpl_inO.
  - unfold time. solve_proper.
  - eexists (fun n => _).
    + intros. rewrite !LNat.size_nat_enc, size_list_enc_r. set (n:= L_facts.size _). reflexivity.
    + smpl_inO.
    + solve_proper.
Qed.

Smpl Add 1 simple apply pTC_length : polyTimeComputable.


Lemma pTC_Code_size X sig `{encodable X} `{encodable sig}  (cX : codable sig X):
  polyTimeComputable cX -> polyTimeComputable (@Code.size sig X cX).
Proof.
  intros. 
  unfold size. repeat smpl polyTimeComputable.
Qed.
Smpl Add 5 simple eapply pTC_Code_size : polyTimeComputable.


Section cons.

  Lemma pTC_cons X Y `{regX:encodable X} `{regY:encodable Y} f (g : X -> list Y):
    polyTimeComputable f -> polyTimeComputable g -> polyTimeComputable (fun (x:X) => f x :: g x).
  Proof.
    intros. specialize termT_cons with (X:=Y) as H.
    eapply polyTimeComputable_composition2. 1,2:easy.
    evar (c:nat). eexists (fun _ => c).
    { extract. solverec. now unfold c. }
    1,2:now smpl_inO.
    eexists (fun n => n + 1). 2,3:now smpl_inO.
    {intros. rewrite size_list_cons. rewrite !LProd.size_prod. unfold c__listsizeCons. nia. 
    }
  Qed.
End cons.

Smpl Add 5 lazymatch goal with
             |- polyTimeComputable (fun X => _ :: _) => apply pTC_cons
           end: polyTimeComputable.

Section Vcons.
  Import Undecidability.Shared.Libs.PSL.Vectors.Vectors.
  Import Vector.
  Local Arguments VectorDef.to_list : simpl never.
  Global Instance termT_cons n X {regX : encodable X} : computableTime' (fun x => @Vector.cons X x n) (fun a aT => (1,fun A AT => (4,tt))).
  Proof. 
    computable_casted_result.
    change (fun (x : X) (x0 : Vector.t X n) => VectorDef.to_list (x ::: x0)) with (fun (x : X) (x0 : Vector.t X n) => x :: Vector.to_list x0).
    extract. solverec.
  Qed.

  Lemma pTC_Vector_cons X Y `{regX:encodable X} `{regY:encodable Y} n f (g : X -> Vector.t Y n):
    polyTimeComputable f -> polyTimeComputable g -> polyTimeComputable (fun (x:X) => f x ::: g x).
  Proof.
    intros. specialize termT_cons with (n:=n) (X:=Y) as H.
    set (cons := (fun (x :Y) => @Vector.cons _ x n)) in H.
    change (polyTimeComputable (fun x : X => cons (f x) (g x))).
    eapply polyTimeComputable_composition2. 1,2:easy.
    fold cons in H.
    evar (c:nat).
    eexists (fun _ => c).
    { extract. solverec. now unfold c. }
    1,2:now smpl_inO.
    eexists (fun n => n + 1). 2,3:now smpl_inO.
    {intros. unfold cons. rewrite enc_vector_eq.
     change (to_list (fst x ::: snd x)) with (fst x :: to_list (snd x)).
     rewrite size_list_cons. rewrite !LProd.size_prod.  rewrite <- enc_vector_eq.
     set (L_facts.size (enc (fst x))). set (L_facts.size (enc (snd x))). unfold c__listsizeCons. nia.
    }
  Qed.
End Vcons.
Smpl Add 5 lazymatch goal with
             |- polyTimeComputable (fun X => _ ::: _) => apply pTC_Vector_cons
           end: polyTimeComputable.


Lemma mono_map_time X `{encodable X} (f: nat -> nat) (xs: list X):
  Proper (le ==> le) f
  -> sumn (map (fun x => f (L_facts.size (enc x))) xs) <= length xs * f (L_facts.size (enc xs)).
Proof.
  intros Hf. 
  induction xs. reflexivity.
  cbn. rewrite size_list_cons,IHxs. hnf in Hf.
  rewrite (Hf (L_facts.size (enc a)) (L_facts.size (enc a) + L_facts.size (enc xs) + 5)). 2:nia.
  rewrite (Hf (L_facts.size (enc xs)) (L_facts.size (enc a) + L_facts.size (enc xs) + 5)). 2:nia. reflexivity.
Qed.

Lemma pTC_map X Y `{encodable X} `{encodable Y} (f:X -> Y):
  polyTimeComputable f -> polyTimeComputable (map f).
Proof.
  intros Hf.
  evar (time:nat -> nat). exists time. set (map f). extract.
  {solverec. rewrite (correct__leUpToC (mapTime_upTo _)).
   rewrite mono_map_time. 2:now apply mono__polyTC. set (L_facts.size _) as n.
   unshelve erewrite (_ : length x <= n). now apply size_list_enc_r.
   [time]:intro. unfold time. reflexivity.
  }
  { unfold time. smpl_inO. }
  { unfold time. solve_proper. }
  evar (size:nat -> nat). exists size. 
  {intros x. rewrite size_list,sumn_map_add,sumn_map_c,map_map,map_length.
   rewrite sumn_map_le_pointwise.
   2:{ intros ? _. apply (bounds__rSP Hf). }
   rewrite mono_map_time. 2:eapply mono__rSP.
   set (L_facts.size _) as n.
   unshelve erewrite (_ : length x <= n). now apply size_list_enc_r.
   [size]:intro. unfold size. reflexivity.
  }
  { unfold size. smpl_inO. }
  { unfold size. solve_proper. }
Qed.


Lemma pTC_concat X Y `{encodable X} `{encodable Y} (f:X -> list (list Y)):
  polyTimeComputable f -> polyTimeComputable (fun x => concat (f x)).
Proof.
  intros Hf.
  evar (time:nat -> nat). exists time. extract.
  {solverec. rewrite UpToC_le.
   rewrite sumn_map_le_pointwise.
   2:{ intros ? ?. apply size_list_enc_r. }
   setoid_rewrite mono_map_time with (f:=fun x => x). 2:now hnf.
   rewrite !size_list_enc_r.

   rewrite ! (bounds__rSP Hf).
   set (n:=L_facts.size _).
   [time]:intro. unfold time. reflexivity.
  }
  { unfold time. smpl_inO. }
  { unfold time. solve_proper. }
  evar (size:nat -> nat). exists size. 
  {intros x.
   rewrite size_list, sumn_map_add,sumn_map_c.
   rewrite concat_map,sumn_concat.
   rewrite length_concat.
   rewrite map_map.
   rewrite sumn_le_bound with (c:= length (concat (f x)) * resSize__rSP Hf (L_facts.size (enc x))). 
   2:{ intros ? (?&<-&HIn)%in_map_iff. rewrite sumn_le_bound with (c:=L_facts.size (enc x0)).
       2:{  intros ? (?&<-&?)%in_map_iff. now apply size_list_In. }
       rewrite map_length,length_concat. rewrite <- bounds__rSP.
       rewrite size_list_In. 2:eassumption.
       apply Nat.mul_le_mono. 2:reflexivity.
       eapply sumn_le_in. now apply in_map_iff.
   }
   rewrite length_concat,map_length.
   unshelve erewrite (_ : (sumn (map (length (A:=Y)) (f x)) <= resSize__rSP Hf (L_facts.size (enc x)))).
   { rewrite <- bounds__rSP,size_list.
     rewrite <- sumn_map_le_pointwise with (f2:=(fun x0 : list Y => L_facts.size (enc x0) + 5)) (f1:= @length _).
     2: now intros; rewrite <- size_list_enc_r. nia.
   }
    unshelve erewrite (_ : length (f x) <= resSize__rSP Hf (L_facts.size (enc x))).
   { rewrite <- bounds__rSP,size_list. rewrite sumn_map_add,sumn_map_c. unfold c__listsizeNil, c__listsizeCons. nia.
   }
   set (L_facts.size _). [size]:intros n. unfold size. reflexivity.
  }
  - unfold size. smpl_inO.
  - unfold size. solve_proper.
Qed.

Lemma pTC_app X Y `{encodable X} `{encodable Y} (f1 f2:X -> list Y):
  polyTimeComputable f1 -> polyTimeComputable f2 -> polyTimeComputable (fun x => f1 x ++ f2 x).
Proof.
  intros Hf1 Hf2.
  eapply polyTimeComputable_composition2. 1,2:eauto.
  evar (time : nat -> nat). exists time. extract.
     {solverec.
      unshelve erewrite (_: |a| <= L_facts.size (enc (a,b))).
      { rewrite LProd.size_prod,size_list_enc_r;cbn. nia. }
      set (L_facts.size _). [time]:intro. now unfold time.
     }
     { unfold time. smpl_inO. }
     { unfold time. solve_proper. }
     { evar (size : nat -> nat). exists size.
       {
         intros [a b]. rewrite LProd.size_prod, !size_list,map_app,sumn_app,!sumn_map_add,!sumn_map_c.
         cbn [fst snd].
         [size]:exact (fun x => x + 4). unfold size. lia.
       }
       - unfold size. smpl_inO.
       - unfold size. solve_proper.
     }
Qed.
  

Lemma pTC_initValue X  sig tau `{encodable X} `{encodable sig} `{encodable tau} (cX : codable sig X) (r:Retract sig tau) :
  polyTimeComputable cX -> polyTimeComputable (Retr_f (Retract:=r)) ->  polyTimeComputable (initValue cX r).
Proof.
  unfold initValue. intros cX_pTC r_pTC. 
  eapply polyTimeComputable_composition.
  2:{ refine (_ : polyTimeComputable (fun x => (midtape [] (inl START)) x)).
      exists (fun _ => 5). extract.
      Unshelve. solverec. 1,2:now smpl_inO.
      evar (size : nat -> nat). exists size. unfold enc at 1;cbn;intros x.
      set (n0:=L_facts.size (enc x)). [size]:intros n0. repeat (unfold enc,size; cbn). reflexivity.
      - unfold size. smpl_inO.
      - unfold size. solve_proper.
  }
  eapply pTC_app.
  2:now apply pTC_cnst.
  eapply polyTimeComputable_composition.
  2:{ eapply pTC_map.
      exists (fun _ => 4); [ | apply inOPoly_c | easy | ].
      - extract. solverec.
      - exists (fun x => x+4); [ | smpl_inO | solve_proper].
        intro. now rewrite size_sum.
  }
  unfold Encode_map. cbn.
  eapply polyTimeComputable_composition. assumption.
  apply pTC_map. assumption.
Qed.
Smpl Add 5 unshelve simple eapply pTC_initValue : polyTimeComputable.



Import M_LHeapInterpreter.

From Complexity Require Import PolyTimeComputable.

Lemma pTC_Encode_Com : polyTimeComputable (Encode_Com).
Proof.
  unfold Encode_Com;cbn. unfold Com_to_sum.
  change (fun x1 : sigNat => sigSum_X x1) with (@sigSum_X sigNat ACom).
  eexists (fun x => x*(11 + c__app + c__map) + 16 + c__app + c__map); [ | smpl_inO | solve_proper | ].
  {extract. solverec. rewrite map_time_const,app_length,!repeat_length,size_Tok_enc. cbn [length]. 
    nia. }
  eexists (fun x => x*5 + 33); [ | smpl_inO | solve_proper].
  intros [];cbn. 2-4:now cbv.
  rewrite size_list;unfold enc;cbn - ["+"].
  rewrite map_app,map_repeat,sumn_map_add,sumn_map_c,map_app,sumn_app,map_repeat,map_map,app_length,repeat_length,map_length,sumn_repeat.
  unfold enc. cbn;ring_simplify. rewrite LNat.size_nat_enc. unfold LNat.c__natsizeS, LNat.c__natsizeO, c__listsizeNil, c__listsizeCons.
  nia.
Qed.

Lemma pTC_Encode_Prog : polyTimeComputable (Alphabets.Encode_Prog).
Proof.
  unfold Alphabets.Encode_Prog,Encode_list. cbn.
  eapply polyTimeComputable_proper_eq_flip. hnf. now setoid_rewrite encode_list_concat at 1.
  eapply pTC_app. 2:now apply pTC_cnst.
  eapply pTC_concat,pTC_map,polyTimeComputable_composition2.
  now apply pTC_cnst.
  eapply polyTimeComputable_composition.
  exact pTC_Encode_Com. eapply pTC_map.
  {eexists (fun x => _). eapply term_sigList_X. 1,2:now smpl_inO.
   eexists (fun x => _). intros x. rewrite size_sigList. set (L_facts.size _). reflexivity.
   - smpl_inO.
   - solve_proper.
  }
  repeat smpl polyTimeComputable.
Qed.

Smpl Add 1 simple eapply pTC_Encode_Prog : polyTimeComputable.

Lemma pTC_inl X Y `{encodable X} `{encodable Y} : polyTimeComputable (@inl X Y). 
Proof. 
  eexists (fun x => _). eapply term_inl.
  - apply inOPoly_c.
  - easy.
  - eexists (fun x => _).
    + intros x. rewrite size_sum. set (L_facts.size (enc x)). reflexivity.
    + smpl_inO.
    + solve_proper.
Qed.
Smpl Add 1 eapply pTC_inl : polyTimeComputable. 

From Complexity.Complexity Require Import Subtypes.
Import Datatypes.Lists Datatypes.LBool.
Lemma LMGenNP_to_TMGenNP_mTM:
  LMGenNP (list bool) ⪯p mTMGenNP_fixed (projT1 M.M).
Proof.
  evar (f__size:nat -> nat).
  enough (Hcert_f__size : forall maxSize (bs : list bool) sig R, size (enc bs) <= maxSize -> sizeOfTape (initValue (sig:=sig) _ R bs) <= f__size maxSize).

  
  evar (f__steps:nat * Pro * nat -> nat).
  enough (Hf__steps : forall steps P maxSize t__cert k__LM,
             sizeOfTape t__cert <= f__size maxSize
             -> k__LM <= steps ->
             M.time (k__LM, sizeOfmTapes (t__cert ::: M.ts__start P)) <= f__steps (steps,P,maxSize)).

  
  
  eapply @reducesPolyMO_intro_restrictBy_both with
      (f:=fun '(P,maxSize,steps) => (M.ts__start P,f__size maxSize,S (f__steps (steps,P,maxSize)))).
  2:intros [[P maxSize] steps] H; split.
  2:{ hnf in H|-*. destruct H as ((s&->&s__proc)&HsmallCert&Hk).
      intros t__cert' k res' HM.
      specialize (M.Realise HM) as H'. hnf in H'. specialize H' with (1:=eq_refl) as (bs'&Hbs'&(sigma'&k__LM'&HbsRed')).
      specialize HsmallCert with (1:=HbsRed') as (bs&res__LM&Hbs&HbsRed&Hter__LM). clear HM k res' t__cert' bs' Hbs' sigma' k__LM' HbsRed'.
      apply star_pow in HbsRed as (k__LM&HbsRed).
      assert (Hk__LM : k__LM <= steps).
      { eapply Hk. exact Hbs. split. all:eassumption. }
      edestruct M.Terminates as (conf'&eq).
      2:{ eexists (initValue _ _ (rev bs)),_. split. 2:eassumption. eapply Hcert_f__size. rewrite size_rev. easy. }
      split. now clear;Lia.nia.
      eexists _,_,_,(rev bs).
      repeat simple apply conj.
      1:now reflexivity.
      1:now apply initValue_contains.
      2:{
        unshelve erewrite (_ : forall x, S x - 1 = x). 1:now clear;nia.
        apply Hf__steps. 2:eassumption. eapply Hcert_f__size.  rewrite size_rev. easy.
      }
      rewrite rev_involutive. unfold evaluatesIn;eauto.
  }
  3:{ intros steps P maxSize t__cert k__LM Hsize Hk__LM.
      rewrite M.sizeStart.
      unfold M.time.
      rewrite UpToC_le.
      rewrite !Hk__LM. clear Hk__LM k__LM.
      rewrite !Hsize. clear Hsize t__cert.
      [f__steps]:refine (fun '(steps,P,maxSize) => _). unfold f__steps. reflexivity.
  }
  3:{ intros maxSize bs sig R Hsize. rewrite initValue_sizeOfTape. 
      
      specialize @correct__leUpToC with (l:=BoollistEnc.boollist_size) (x:=bs) as ->.
      rewrite <- size_list_enc_r in Hsize. rewrite Hsize. 
      [f__size]:refine (fun n => _). subst f__size;cbn beta. reflexivity.
  }

  2:{
    destruct H as ((s&->&s__proc)&HsmallCert&Hsmallk).
    unfold LMGenNP, mTMGenNP_fixed.
    split.
    -intros (cert' & HcertSize' & sigma'' & k' &Hk' &HR').
     edestruct M.Terminates with (k:= S (f__steps (steps,compile s,maxSize))) as (tout&Hout).
     { split. easy. eexists _,_,_,(rev cert'). rewrite rev_involutive. repeat simple apply conj.
       1:reflexivity.
       2:eexists;exact HR'.
       1:now apply initValue_contains.
       { unshelve erewrite (_ : forall x, S x - 1 = x). 1:now clear;nia.
         apply Hf__steps. 2:eassumption.
         eapply Hcert_f__size. now rewrite size_rev.
       }
     }
     do 2 eexists.
     2:{
       eexists. eassumption. }
     eapply Hcert_f__size. now rewrite size_rev.
    -intros (t__cert&Hsize_t__cert&(res&Hres)).
     specialize (M.Realise Hres) as H'. hnf in H'. specialize H' with (1:=eq_refl) as (bs'&Hbs'&(sigma'&k__LM'&HbsRed')).
      specialize HsmallCert with (1:=HbsRed') as (bs&res__LM&Hbs&HbsRed&Hter__LM). clear Hres bs' Hbs' sigma' k__LM' HbsRed'.
      apply star_pow in HbsRed as (k__LM&HbsRed).
      assert (Hk__LM : k__LM <= steps).
      { eapply Hsmallk. exact Hbs. split. all:eassumption. }
      exists bs. repeat simple apply conj. 1:easy. unfold evaluatesIn; eauto 10.
  }
  {
    clear Hf__steps Hcert_f__size.

    nary apply pTC_destructuringToProj.
(*     specialize pTC_destructuringToProj with (domain:=[nat;nat;list Tok]) as h. cbn in h. refine ( h _ _ _ _ _). *)
    enough (polyTimeComputable f__size).
    enough (polyTimeComputable f__steps).
    repeat smpl polyTimeComputable.
    -unfold M.ts__start. 
    unfold Alphabets.Encode_Prog.
    
    repeat smpl polyTimeComputable.
    {
      unfold Retr_f. cbn. unfold retr_comp_f,retract_inl_f.
      eapply polyTimeComputable_composition.
      eapply polyTimeComputable_composition.
      eapply polyTimeComputable_composition.
      eapply polyTimeComputable_composition.
      
      now eapply pTC_id. 3, 4: smpl polyTimeComputable. 
      2:{ eexists (fun x => _). eapply term_sigList_X. 1,2:now smpl_inO.
          eexists (fun x => _). intros x. rewrite size_sigList. set (size _). reflexivity.
          - smpl_inO.
          - solve_proper.
      }
      { eexists (fun x' => _). now apply (term_sigPair_Y).
        - apply inOPoly_c.
        - easy.
        - eexists (fun x => 4 + _).
          + intros x. unfold enc;cbn. set (size _). reflexivity.
          + smpl_inO.
          + solve_proper.
      }
    }
    -unfold f__steps. nary apply pTC_destructuringToProj.
    (*     specialize pTC_destructuringToProj with (domain:=[nat;nat;list Tok]) as h. cbn in h. refine ( h _ _ _ _ _). *)
     repeat smpl polyTimeComputable.
    -unfold f__size.
     repeat smpl polyTimeComputable.
  }
Qed.
