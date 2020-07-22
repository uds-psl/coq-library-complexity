From Undecidability.L Require Import TM.TMflat Tactics.LTactics Datatypes.LNat Datatypes.Lists Functions.EqBool.

From Undecidability Require Import TM.TM TM.TMEncoding L.TM.TMunflatten.

From PslBase.FiniteTypes Require FiniteFunction.
From Undecidability Require Import Functions.FinTypeLookup.


Lemma size_flatTape (sig : finType) (t' : tape sig):
  size (enc (mapTape index t')) <= sizeOfTape t' * (Cardinality.Cardinality sig * 4+9) + 17.
Proof.
  unfold enc, registered_tape_enc,sizeOfTape,tapeToList.
  destruct t';cbn [mapTape tape_enc size length].
  all:ring_simplify. nia.
  all:setoid_rewrite size_nat_enc.
  all:simpl_list;cbn [length].
  all:change (list_enc (X:=nat)) with (@enc (list nat) _).
  all:setoid_rewrite size_list.
  
  all: rewrite !sumn_le_bound with (c:=Cardinality.Cardinality sig*4 + 9).
  
  2,4,6,7:now intros ? (?&<-&(?&<-&?)%in_map_iff)%in_map_iff;
    rewrite size_nat_enc,index_leq;
    unfold Cardinality.Cardinality; easy.
  all:rewrite !map_length.
  all:rewrite index_leq; unfold Cardinality.Cardinality.
  all:nia.
Qed.


Lemma size_flatTapes (sig : finType) (n : nat) (t:list (tape nat)) (t' : Vector.t (tape sig) n):
  isFlatteningTapesOf t t'
  -> size (enc t) <= n * sizeOfmTapes t' * (Cardinality.Cardinality sig * 4 + 9) + n * 22 + 4.
Proof.
  intro R__tapes. inv R__tapes.
  unfold sizeOfmTapes,mapTapes.
  rewrite size_list.
  rewrite Vector.fold_left_right_assoc_eq. 2:intros;nia.
  induction n.
  -rewrite !destruct_vector_nil with (v:=t').
   cbn. easy.
  -edestruct destruct_vector_cons with (v:=t') as (?&?&->).
   cbn - [mult]. fold (Vector.to_list (Vector.map (mapTape index) x0)).
   specialize (IHn x0).
   rewrite size_flatTape.
   set (a := sumn _) in *. set (b := VectorDef.fold_right _ _ _) in *. set (c := Cardinality.Cardinality _) in *.
   set (d:=sizeOfTape _).
   enough (a <= n * b * (c * 4 + 9) + n * 22) as ->. 2: nia.
   repeat eapply Nat.max_case_strong;intros ?. nia. Unset Simplex. rewrite H.  nia.
Qed.



Lemma sizeoftape_maptape_eq sig sig' (f:sig -> sig') t:
  sizeOfTape (mapTape f t) = sizeOfTape t.
Proof.
  destruct t;cbn. all:repeat (cbn;simpl_list). all:lia.
Qed.

Fixpoint sizeOfmTapesFlat sig (ts : list (tape sig)) : nat :=
  match ts with
    [] => 0
  | t::ts => max (sizeOfTape t) (sizeOfmTapesFlat ts)
  end.

Lemma sizeOfmTapesFlat_eq (sig : finType) (n : nat) (ts:list (tape nat)) (ts' : Vector.t (tape sig) n):
  isFlatteningTapesOf ts ts'
  -> sizeOfmTapesFlat ts = sizeOfmTapes ts'.
Proof.
  intro R__tapes. inv R__tapes.
  unfold sizeOfmTapes,mapTapes.
  rewrite Vector.fold_left_right_assoc_eq. 2:intros;nia.
  induction n.
  -rewrite !destruct_vector_nil with (v:=ts').
   cbn. easy.
  -edestruct destruct_vector_cons with (v:=ts') as (?&?&->).
   cbn - [mult]. fold (Vector.to_list (Vector.map (mapTape index) x0)).
   specialize (IHn x0). rewrite IHn,sizeoftape_maptape_eq. lia.
Qed.

Lemma isFlatteningTransOf_eq st sig' n trans trans' s v:
  isFlatteningTransOf (st:=st) (sig:=sig') (n:=n) trans trans' ->
  (let (s',v'):= trans' (s,v) in
  (index s', map (map_fst (option_map index)) (Vector.to_list v'))) = FinTypeLookup.lookup (index s,map (option_map index) (Vector.to_list v)) trans (index s, repeat (None,N) n).
Proof.
  intros [H1 H2].
  destruct trans' as [s' v'] eqn:eq.
  erewrite lookup_sound'.
  -reflexivity.
  -intros [s0 v0] [s1 v1] [s2 v2] T1 T2.
   apply H1 in T1 as  (?&?&?&?&Ht&->&->&->&->).
   apply H1 in T2 as  (?&?&?&?&Ht'&<-%injective_index&->&H'%map_injective&->).
   2:{intros [] [] [=];f_equal. now eapply injective_index. }
   eapply vector_to_list_inj in H' as <-.
   congruence. 
  -specialize (H2 s v) as H2'. rewrite eq in H2'.
   destruct H2' as [ | (<-&->) ]. easy.
   edestruct lookup_complete with (A:= (nat * list (option nat))%type) (B:= (nat * list (option nat * move))%type) as [H'|H'].
   2:{right. split.
      +intros ? ?.
       eapply H'. eexists. eassumption.
      +f_equal. unfold Vector.to_list.
       clear.
       induction n;cbn. all:easy.
   }
   left.
   edestruct lookup as [] eqn:eq' in H'.
   specialize H1 with (1:=H') as  (?&?&?&?&Ht&<-%injective_index&->&H'''%map_injective&->).
   2:{intros [] [] [=];f_equal. now eapply injective_index. }
   eapply vector_to_list_inj in H''' as <-. rewrite eq in Ht. inv Ht.
   eassumption.
   Unshelve.
   repeat econstructor. 
Qed.


Definition zipWith {X Y Z} (f:X -> Y->Z) :=
  fix zipWith (xs:list X) (ys:list Y) : list Z :=
  match xs,ys with
    x::xs,y::ys => f x y :: zipWith xs ys
  | _,_ => []
  end.

Lemma doAct_multiFlat (sig:finType) n acts t (t' : tapes sig n):
  isFlatteningTapesOf t t' ->
  isFlatteningTapesOf (zipWith (doAct (sig:=nat)) t (map (map_fst (option_map index)) (Vector.to_list acts))) (doAct_multi t' acts).
Proof.
  intros H. inv H. rewrite isFlatteningTapesOf_iff.
  induction n in *|-*.
  -rewrite !destruct_vector_nil with (v:=t').
   rewrite !destruct_vector_nil with (v:=acts). easy.
  -destruct destruct_vector_cons with (v:=t') as (?&?&->).
   destruct destruct_vector_cons with (v:=acts) as (?&?&->).
   
   cbn.
   setoid_rewrite IHn.  f_equal.
   destruct x,x1 as [[] []]; cbn - [tape_move_left tape_move_right]. all:try easy. 
   all:try (setoid_rewrite <- mapTape_move_right || rewrite <- mapTape_move_left). all:cbn. all:easy.
Qed.



Definition stepFlat (trans:list (nat * list (option nat) * (nat * list (option nat * move)))) (c:mconfigFlat) : mconfigFlat :=
  let (news, actions) := lookup (fst c, map (@current _) (snd c)) trans (fst c, repeat (None, N) (length (snd c)))
  in (news,(zipWith (@doAct _) (snd c) actions)).

Lemma current_charsFlat_eq (sig:finType) n t (t': tapes sig n):
  isFlatteningTapesOf t t' ->
  map (current (sig:=nat)) t = map ((option_map index)) (Vector.to_list (current_chars t')).
Proof.
  intros H. inv H. induction n in *|-*.
  -rewrite !destruct_vector_nil with (v:=t'). easy.
  -destruct destruct_vector_cons with (v:=t') as (?&?&->). cbn. setoid_rewrite IHn.
   unfold current_chars. cbn.  f_equal.
   destruct x; easy.
Qed.

Lemma stepFlat_eq sig' n (M': mTM sig' n) (trans:list (nat * list (option nat) * (nat * list (option nat * move)))) (c:mconfigFlat) c':
  isFlatteningTransOf (sig:=sig') (n:=n) trans (TM.TM.trans (m:=M')) ->
  isFlatteningConfigOf c c' -> 
  isFlatteningConfigOf (stepFlat trans c) (step (M:=M') c').
Proof.
  intros Htrans H. inv H.
  unfold stepFlat, step. cbn [fst snd cstate ctapes] in *.
  erewrite current_charsFlat_eq. 2:easy.
  replace (length t) with n.
  2:{inv Ht. destruct c'. now rewrite LVector.to_list_length. }
  erewrite <-isFlatteningTransOf_eq. 2:easy.
  destruct TM.trans. apply isFlatteningConfigOf_iff;do 2 econstructor.
  apply doAct_multiFlat;eauto. 
  now econstructor.
Qed.

Definition haltConfFlat (l : list bool) (c:mconfigFlat) : bool := nth (fst c) l false.  
  
Definition loopMflat M := loop (stepFlat M.(TMflat.trans)) (haltConfFlat M.(TMflat.halt)).

Lemma loopMflat_correct (sig : finType) (n : nat) M (M' : mTM sig n)  k c c':
  isFlatteningTMOf M M' ->
  isFlatteningConfigOf c c' ->
  match loopMflat M c k,loopM (M:=M') c' k with
    None,None => True
  | Some r,Some r' => isFlatteningConfigOf r r'
  | _,_ => False
  end.
Proof.
  intros HM Hc. unfold loopM,loopMflat.
  induction k in Hc,c,c'|-*.
  -cbn.
   destruct HM. destruct R__halt. unfold haltConfFlat,haltConf.
   inv Hc;cbn [fst snd]. 
   rewrite R__halt. destruct halt. 2:easy.
   econstructor. all:easy.
  -cbn.
    destruct HM. destruct R__halt. unfold haltConfFlat,haltConf.
   inversion Hc;cbn [fst snd]. subst.
   rewrite R__halt. destruct halt. easy.
   eapply stepFlat_eq in Hc. 2:eassumption. eapply IHk in Hc as H'.
   fold (haltConfFlat (TMflat.halt M)). fold (haltConf (M:=M')). 
   do 2 destruct loop. all:easy.
Qed.

Lemma initFlat_correct sig n M (M' : mTM sig n) t t':
  isFlatteningTMOf M M' ->
  isFlatteningTapesOf t t' ->
  isFlatteningConfigOf (M.(TMflat.start), t) (initc M' t').
Proof.
  intros. eapply isFlatteningConfigOf_iff;do 2  econstructor. eassumption.
  inv H. cbn. congruence.
Qed.

Definition execFlatTM M t n :=
  if isValidFlatTM M then
    if isValidFlatTapes M.(sig) M.(TMflat.tapes) t
    then loopMflat M (M.(TMflat.start),t) n
    else None
  else None.

Lemma execFlatTM_correct M t k c :
  execFlatTM M t k = Some c <->
  (exists sig n (M':mTM sig n) c0 c',
      isFlatteningTMOf M M'
      /\ isFlatteningConfigOf (M.(TMflat.start),t) c0
      /\ loopM (M:=M') c0 k = Some c' 
      /\ isFlatteningConfigOf c c').
Proof.
  unfold execFlatTM.
  destruct (isValidFlatTM_spec M);cbn [andb].
  2:{ cbn. split. easy. intros (?&?&?&?&?&?&?&?&?). exfalso. eauto using isFlattening_is_valid. }
  split.
  -apply unflattenTM_correct in v.
   pose (sig' := (finType_CS (Fin.t (sig M)))).
   pose (states' := states (unflattenTM M)). cbn [unflattenTM states] in states'.
   rewrite <- Fin_cardinality with (n:=sig M) at 1. fold sig'.
   destruct isValidFlatTapes eqn:H';cbn [andb]. 2:easy. apply isUnflattableTapes in H' as (t'&Ht).
   cbn [negb]. 
   assert (def : states') by (eapply (@Fin.of_nat_lt 0) ;nia).
   eapply initFlat_correct in Ht. 2:eauto.
(*   assert (H' : isFlatteningConfigOf (s,t) (mk_mconfig (nth s (elem states') def) t')).
   {constructor. 2:eauto. cbn. subst states'. now rewrite index_nth_elem_fint. }*)
   assert (H'' := loopMflat_correct k v Ht).
   intros Hloop. rewrite Hloop in H''.
   destruct loopM eqn:HloopM.
   all:now eauto 10.
  -intros (?&?&?&?&?&HM&Hinit&HloopM&?). inversion HM.
   inversion Hinit. subst. rewrite H1. 
   erewrite eq__sig,flatteningTapeIsValid. 2:eassumption. 
   destruct (Nat.ltb_spec0 (index (cstate x2)) (TMflat.states M)).
   2:{exfalso. apply n. rewrite eq__states. eapply index_le. }
   cbn. 
   eassert (H'':=loopMflat_correct k HM Hinit).
   rewrite HloopM in H''. destruct loopMflat. 2:easy.
   destruct c,m. inv Ht.
   inv H''. inv H. do 2 f_equal. 
   inv Ht0. inv Ht. easy.
Qed.
