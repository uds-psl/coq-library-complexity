From Undecidability Require Import TM.TM L.Functions.FinTypeLookup.
Require Import PslBase.FiniteTypes.
From PslBase.FiniteTypes Require Import VectorFin Cardinality.

From Undecidability Require Import L.TM.TMflat.


Definition Vector_of_list_length A n (l:list A) : option (Vector.t A n) :=
  match Nat.eq_dec (length l) n with
    Specif.left H =>
    Some (eq_rect _ (fun n => Vector.t A n) (Vector.of_list l) _ H)
  | _ => None
  end.

Lemma Vector_of_list_length_eq A (l:list A) :
  Vector_of_list_length (length l) l = Some (Vector.of_list l).
Proof.
  unfold Vector_of_list_length.
  destruct _. 2:easy.
  f_equal.
  rewrite <- Eqdep_dec.eq_rect_eq_dec. easy. decide equality.
Qed.
(*
Definition Fin_of_nat_try n i : option (Fin.t n) :=
  match Fin.of_nat i n with
    inleft x => Some x
  | _ => None
  end.*)

Definition unflatten_symb (sig:finType)  (i:option nat): option sig:=
  match i with
    None => None
  | Some i => nth i (map Some (elem _)) None
  end.

Definition unflatten_acts' (sig:finType) (l__r : list (option nat * move)): (list (option sig * move)) :=
  map (fun '(i,m) => (unflatten_symb sig i,m)) l__r.

Definition unflatten_acts (sig:finType) n (l__r : list (option nat * move)) : (Vector.t (option sig*move) n) :=
  match Vector_of_list_length n  (unflatten_acts' sig l__r) with
  | Some l__r => l__r
  | _ => Vector.const (None,N) n
  end.
  

Definition unflatten_trans (states:finType) (sig:finType) d n (f:list (nat * list (option nat) * (nat * list (option nat * move))))
  : states * Vector.t (option sig) n -> states * Vector.t (option sig * move) n :=
  fun '(st,l) =>
    let (st__o,l__r) := lookup f (index st,map (option_map (fun x => index x)) (Vector.to_list l)) (0,[]) in
    (nth st__o (elem _) d, unflatten_acts sig n l__r)
.


Definition unflatten_halt states (f: list bool) (i : (Fin.t states)) : bool :=
  nth (index i) f false.
(*
Definition from_mTM sig n (M:mTM sig n) : TM :=
  {| sig := Cardinality sig ;
     tapes := n;
     states := Cardinality (TM.states M);
     trans := flatten_trans (@TM.trans _ _ M);
     start := index (TM.start M);
     halt := flatten_halt (@TM.halt _ _ M);
  |}.*)

Local Definition def n : Fin.t (max 1 n).
Proof.
  destruct n;cbn.
  all:now constructor.
Defined.

Program Definition unflattenTM (M:TM) : mTM (finType_CS (Fin.t (sig M))) (tapes M) :=
  let d := def _ in
  {|TM.states := (finType_CS ((Fin.t (max 1 (states M)))));
    TM.trans := unflatten_trans d (trans M);
    TM.start := nth (start M) (elem _) d;
    TM.halt := unflatten_halt (halt M);
  |}.

Lemma Card_Fint n : Cardinality (finType_CS (Fin.t n)) = n.
Proof.
Admitted.


Lemma index_nth_elem (X:finType) i d:
  i < Cardinality X
  -> index (nth (A:=X) i (elem _) d) = i.
Proof.
  intros. unfold index. apply getPosition_nth.
  -eapply dupfree_elements.
  -refine (_:_ < Cardinality _). easy.
Qed.

Lemma index_nth_elem_fint i n d:
  i < n
  -> index (nth (A:=Fin.t n)i (elem _) d) = i.
Proof.
  intros. 
  eapply index_nth_elem.
  refine (_:_ < Cardinality _);setoid_rewrite Card_Fint at 1. easy.
Qed.

Definition defFin (X:finType):
  0 < Cardinality X
  -> X.
Proof.
  unfold Cardinality.
  destruct (elem X). cbn. intros. omega. easy.
Qed.
  


Definition unflatten_in (sig:finType) n (l__r : list (option nat)) : (Vector.t (option sig) n) :=
  match Vector_of_list_length n  (map (unflatten_symb sig) l__r) with
  | Some l__r => l__r
  | _ => Vector.const None n
  end.

Lemma unflatten_in_correct (sig:finType) n v:
  length v = n ->
  (forall a : nat, Some a el v -> a < Cardinality sig) ->
  map (option_map index) (Vector.to_list (unflatten_in sig n v)) = v.
Proof.
  intros <-.
  unfold unflatten_in.
  erewrite <- map_length.
  rewrite Vector_of_list_length_eq,VectorSpec.to_list_of_list_opp.
  rewrite utils.map_map_compose.
  intros. 
  erewrite map_ext_in with (g:=fun x => x). now apply map_id.
  
  intros. destruct a. 2:easy.
  apply H in H0. 
  unfold Basics.compose. cbn.
  unshelve erewrite nth_indep with (d':= Some _).
  -eapply defFin. omega.
  -rewrite map_nth. cbn.
   erewrite index_nth_elem. all:try easy.
  -rewrite map_length. easy.
Qed.

Record validFlatTrans (states sig n:nat) (f:list (nat * list (option nat) * (nat * list (option nat * move)))) : Prop :=
  {
    flatTrans_inj:
      (forall a' b1 b2 , (a', b1) el f -> (a', b2) el f -> b1 = b2);
    flatTrans_tot:
      (forall s v, (exists r, ((s,v),r) el f)  <-> s < states
                                       /\ length v = n
                                       /\ forall a, Some a el v -> a < sig);
    flatTrans_res_ok: forall x s' v',
        (x,(s',v')) el f
        -> s' < states
          /\ length v' = n
          /\ (forall a m, (Some a,m) el v' -> a < sig)   
  }.

Lemma flatTrans_in_ok states sig n f:
  validFlatTrans states sig n f ->
  forall s v r,
  ((s,v),r) el f
  -> s < states
    /\ length v = n
    /\ (forall a, Some a el v -> a < sig).
Proof.
  intros H s v r ?.
  eapply flatTrans_tot. all:eauto.
Qed. 
(*

Lemma isFlattening_inv sig n (M':mTM sig n) d trans0 s s' v v':
  isFlatteningTransOf trans0 (TM.trans (m:=M')) ->
  ((s,v),(s',v')) el trans0 ->
  s = index (nth s (elem (finType_CS (Fin.t (Cardinality (TM.states M'))))) d)
  /\ s' = index (nth s' (elem (finType_CS (Fin.t (Cardinality (TM.states M'))))) d)
  /\ v = map (option_map index) (unflatten_in (Cardinality sig) n v)
  /\ v' = map (map_fst (option_map index)) (unflatten_acts (Cardinality sig) n v').
Admitted.*)


Lemma unflatten_acts_correct (sig:finType) n v':
  length v' = n ->
  (forall a m , (Some a,m) el v' -> a < Cardinality sig) ->
  map (map_fst (option_map index)) (Vector.to_list (unflatten_acts sig n v')) = v'.
Proof.
  intros <-.
  unfold unflatten_acts,unflatten_acts'.
  erewrite <- map_length.
  rewrite Vector_of_list_length_eq,VectorSpec.to_list_of_list_opp.
  rewrite utils.map_map_compose.
  intros. 
  erewrite map_ext_in with (g:=fun x => x). now apply map_id.
  
  intros. destruct a as [[] ?]. 2:easy.
  apply H in H0. 
  unfold Basics.compose. cbn.
  unshelve erewrite nth_indep with (d':= Some ltac:(eapply defFin)).
  abstract omega.
  2:{ rewrite map_length. easy. }

  rewrite map_nth. cbn.
  rewrite index_nth_elem;easy.
Qed.

Lemma vector_to_list_length X n (l: Vector.t X n):
  length (Vector.to_list l) = n.
Proof.
  induction l;cbn. easy. rewrite IHl at 1. reflexivity.
Qed.

Lemma unflatten_trans_correct st sig n d trans0:
  validFlatTrans st sig n trans0
  -> isFlatteningTransOf trans0 (unflatten_trans (sig:=finType_CS (Fin.t sig)) (states := finType_CS (Fin.t st)) (n:=n) d trans0).
Proof.
  intros H.
  econstructor;split.
  -intros H'.
   eexists (nth s (elem _) d),(nth s' (elem _) d).
   eexists (unflatten_in _ _ v), (unflatten_acts _ _ v').
   specialize (flatTrans_res_ok H H') as (?&?&?).
   specialize (flatTrans_in_ok H H') as (?&?&?).
   unfold unflatten_trans.
   rewrite !index_nth_elem_fint. 2,3:easy.
   rewrite unflatten_in_correct. 2,3:now try rewrite Card_Fint;easy.
   erewrite lookup_sound. 3:easy. 2:eapply flatTrans_inj;eassumption.
   cbn.
   setoid_rewrite unflatten_in_correct. 2,3:now try rewrite Card_Fint;easy.
   setoid_rewrite unflatten_acts_correct. 2,3:now try rewrite Card_Fint;easy.
   repeat split.
  -intros (?&?&?&?&H'&->&->&->&->).
   unfold unflatten_trans in H'.
   edestruct (proj2 (flatTrans_tot H (index x) (map (option_map index) (Vector.to_list x1) ))).
   { repeat split.
     -rewrite <- (Card_Fint). eapply index_le.
     -clear. symmetry.  rewrite map_length,vector_to_list_length. reflexivity.
     -intros ? ([]&[= <-]&?)%in_map_iff. rewrite <- (Card_Fint). eapply index_le.
   }
   erewrite lookup_sound in H'. 3:eassumption. 2:now eapply flatTrans_inj;eassumption.
   destruct x3. inv H'.

   specialize (flatTrans_res_ok H H0) as (?&?&?).
   specialize (flatTrans_in_ok H H0) as (?&?&?).
   
   rewrite unflatten_acts_correct. 2,3:eauto.
   rewrite index_nth_elem_fint. all:now try rewrite Card_Fint;easy.
Qed.


Lemma isFlatteningTrans_validFlatTrans n sig' (M' : mTM sig' n) f:
isFlatteningTransOf f (TM.trans (m:=M'))
-> validFlatTrans (Cardinality (TM.states M')) (Cardinality sig') n f.
Proof.
  intros [H'].
  split.
  -intros [] [] [] (?&?&?&?&?&->&->&->&->)%H' (?&?&?&?&?&eq1&->&eq2&->)%H'.
   apply injective_index in eq1 as <-.
   enough (x1=x5) by congruence.
   clear - eq2.
   eapply map_injective in eq2.
   +now apply vector_to_list_inj.
   +intros [] [] [=]. 2:easy.
    f_equal;eauto using injective_index.
  -intros. split.
   +intros ([]&(?&?&?&?&?&->&->&->&->)%H').
    repeat split.
    *eapply index_le.
    *rewrite map_length,vector_to_list_length. easy.
    *intros ? ([]&[=<- ]&?)%in_map_iff. eapply index_le.
   +intros (?&<-&?).
    specialize H' with (s:=s) (v0:=v).
    pose (s0 := nth s (elem (TM.states M')) (TM.start M')).
    pose (v0 := unflatten_in sig' (length v) v).
    destruct (TM.trans (s0,v0)) as (s0',v0') eqn:eq.
    exists (index s0', map (map_fst (option_map index)) (Vector.to_list v0')). rewrite H'.
    eexists _,s0',_,v0'.
    repeat esplit.
    *eassumption.
    *subst s0. now erewrite index_nth_elem.
    *subst v0. erewrite unflatten_in_correct. all:easy.
  -intros [] ? ? (?&?&?&?&?&->&->&->&->)%H'.
   rewrite map_length. repeat split.
   +eapply index_le.
   +apply vector_to_list_length.
   +intros ? ? ([[]]&[= <- <-]&?)%in_map_iff. eapply index_le.
Qed.

Lemma unflattenTM_correct M:
  (exists sig n (M' : mTM sig n), isFlatteningTMOf M M')
  -> isFlatteningTMOf M (unflattenTM M).
Proof.
  intros (sig'&n&M'&H). destruct M. inv H.
  assert (H_st:(Init.Nat.max 1 states) = states).
  {destruct states. 2:easy.
   exfalso.
   enough (TM.start M' el []) by easy.
   unfold Cardinality in eq__states.
   symmetry in eq__states. eapply length_zero_iff_nil in eq__states.
   rewrite <- eq__states.
   eapply elem_spec.
  }
  cbn - [max] in *.
  econstructor; cbn - [max].
  -easy.
  -now rewrite Card_Fint.
  -cbn - [Cardinality max].
   rewrite H_st.
   setoid_rewrite <- Card_Fint at 1. easy.
  -eapply unflatten_trans_correct. 
   rewrite H_st. subst states sig.
   eapply isFlatteningTrans_validFlatTrans. easy.
  -cbn -[max].
   generalize (def states).
   rewrite H_st. intros ?.
   unfold index. setoid_rewrite getPosition_nth. easy.
   +apply dupfree_elements.
   +rewrite eq__start, eq__states.
    refine (_:_ < Cardinality _).
    setoid_rewrite Card_Fint at 1.
    unfold Cardinality.
    eapply index_le.
  -cbn -[max unflatten_trans]. rewrite H_st.
   econstructor. reflexivity.
Qed.

Print Assumptions unflattenTM_correct.
