Require Import Undecidability.Shared.Libs.PSL.FiniteTypes.
From Undecidability Require Import L.Functions.EqBool.
From Undecidability.Shared.Libs.PSL.FiniteTypes Require Import VectorFin Cardinality.

From Undecidability Require Import TM.Util.TM_facts.
From Complexity Require Import L.TM.TMflat.
From Undecidability Require L.TM.TMEncoding.


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
  | _ => Vector.const (None,Nmove) n
  end.
  
Definition unflatten_trans (states:finType) (sig:finType) d n (f:list (nat * list (option nat) * (nat * list (option nat * move))))
  : states * Vector.t (option sig) n -> states * Vector.t (option sig * move) n :=
  fun '(st,l) =>
    let (st__o,l__r) := lookup f (index st,map (option_map (fun x => index x)) (Vector.to_list l)) (index st,repeat (None,Nmove) n) in
    (nth st__o (elem _) d, unflatten_acts sig n l__r).


Definition unflatten_halt states (f: list bool) (i : (Fin.t states)) : bool :=
  nth (index i) f false.

Local Definition def n : Fin.t (max 1 n).
Proof.
  destruct n;cbn.
  all:now constructor.
Defined.

Program Definition unflattenTM (M:flatTM) : TM (finType_CS (Fin.t (sig M))) (tapes M) :=
  let d := def _ in
  {|TM.state := (finType_CS ((Fin.t (max 1 (states M)))));
    TM.trans := unflatten_trans d (trans M);
    TM.start := nth (start M) (elem _) d;
    TM.halt := unflatten_halt (halt M);
  |}.

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
  refine (_:_ < Cardinality _);setoid_rewrite Fin_cardinality at 1. easy.
Qed.

Definition defFin (X:finType):
  0 < Cardinality X
  -> X.
Proof.
  unfold Cardinality.
  destruct (elem X). cbn. intros. lia. easy.
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
  rewrite MCList.map_map_compose.
  intros. 
  erewrite map_ext_in with (g:=fun x => x). now apply map_id.
  
  intros. destruct a. 2:easy.
  apply H in H0. 
  unfold Basics.compose. cbn.
  unshelve erewrite nth_indep with (d':= Some _).
  -eapply defFin. lia.
  -rewrite map_nth. cbn.
   erewrite index_nth_elem. all:try easy.
  -rewrite map_length. easy.
Qed.

Record validFlatTrans (sig n states:nat) (f:list (nat * list (option nat) * (nat * list (option nat * move)))) : Prop :=
  {
    flatTrans_inj:
      (forall a' b1 b2 , (a', b1) el f -> (a', b2) el f -> b1 = b2);
    flatTrans_bound: forall s s' v v',
        ((s,v),(s',v')) el f
        -> s < states
          /\ length v = n
          /\ (forall a, Some a el v -> a < sig)
          /\ s' < states
          /\ length v' = n
          /\ (forall a m, (Some a,m) el v' -> a < sig)   
  }.

Definition validFlatTM (M:flatTM) :=
  validFlatTrans M.(sig) M.(tapes) M.(states) M.(trans)
  /\ M.(start) < M.(states).

(* Lemma flatTrans_in_ok states sig n f: *)
(*   validFlatTrans sig n states f -> *)
(*   forall s v r, *)
(*   ((s,v),r) el f *)
(*   -> s < states *)
(*     /\ length v = n *)
(*     /\ (forall a, Some a el v -> a < sig). *)
(* Proof. *)
(*   intros H s v r ?. *)
(*   eapply flatTrans_tot. all:eauto. *)
(* Qed.  *)
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
  rewrite MCList.map_map_compose.
  intros. 
  erewrite map_ext_in with (g:=fun x => x). now apply map_id.
  
  intros. destruct a as [[] ?]. 2:easy.
  apply H in H0. 
  unfold Basics.compose. cbn.
  unshelve erewrite nth_indep with (d':= Some ltac:(eapply defFin)).
  abstract lia.
  2:{ rewrite map_length. easy. }

  rewrite map_nth. cbn.
  rewrite index_nth_elem;easy.
Qed.

Lemma vector_to_list_length X n (l: Vector.t X n):
  length (Vector.to_list l) = n.
Proof.
  induction l;cbn. easy. rewrite IHl at 1. reflexivity.
Qed.

Lemma lookup_sound' (A: eqType) (B: Type) (L : list (prod A B)) a b def :
  (forall a' b1 b2, (a',b1) el L -> (a',b2) el L -> b1=b2) -> ( (a,b) el L \/ ((forall b', ~ (a,b') el L) /\ b = def) ) -> lookup L a def = b.
Proof.
  intros H1 H2. unfold lookup.
  destruct filter eqn:E.
  - destruct H2 as [H2|H2].
    +assert ((a,b) el filter (fun p : A * B => Dec (fst p = a)) L) by ( rewrite in_filter_iff ; eauto).
     now rewrite E in H.
    +easy.
  - destruct p. assert ((e,b0) el (filter (fun p : A * B => Dec (fst p = a)) L)) by now rewrite E.
    rewrite in_filter_iff in H. 
    dec; cbn in *; subst; firstorder.
Qed.

Lemma unflatten_trans_correct st sig n d trans0:
  validFlatTrans sig n st trans0
  -> isFlatteningTransOf trans0 (unflatten_trans (sig:=finType_CS (Fin.t sig)) (states := finType_CS (Fin.t st)) (n:=n) d trans0).
Proof.
  intros H.
  split.
  -intros ? ? ? ? H'.
   eexists (nth s (elem _) d),(nth s' (elem _) d).
   eexists (unflatten_in _ _ v), (unflatten_acts _ _ v').
   unfold unflatten_trans.
   specialize (flatTrans_bound H H') as (?&<-&?&?&?&?).
   rewrite !index_nth_elem_fint. 2,3:easy.
   rewrite unflatten_in_correct. 2,3:now try rewrite Fin_cardinality;easy.
   erewrite lookup_sound. 2:eapply flatTrans_inj;eassumption. 2:easy.
   cbn -[finType_CS].
   setoid_rewrite unflatten_in_correct. 2,3:now try rewrite Fin_cardinality;easy.
   setoid_rewrite unflatten_acts_correct. 2,3:now try rewrite Fin_cardinality;easy.
   repeat split.
  -intros s0 v0.
   unfold unflatten_trans.
   edestruct lookup_complete with (def := (0,@nil (option nat * move))) as [H'|H'].
   +erewrite lookup_sound. 3:eassumption. 2:eapply flatTrans_inj;eassumption.
    edestruct lookup as (st0,l__r). left.
    specialize (flatTrans_bound H H') as (?&?&?&?&?&?).
    rewrite !index_nth_elem_fint. 2:easy. cbn -[finType_CS] in *.
    replace ((index s0, map (option_map index) (Vector.to_list v0),
              (st0, map (map_fst (option_map index)) (Vector.to_list (unflatten_acts (finType_CS (Fin.t sig)) n l__r)))))
      with (index s0, map (option_map (fun x : Fin.t sig => index x)) (Vector.to_list v0), (st0, l__r)).
    2:{ repeat f_equal. symmetry. rewrite unflatten_acts_correct. 1,2:easy. rewrite Fin_cardinality. easy. }
    eassumption.
   +erewrite lookup_sound'. 2:eapply flatTrans_inj;eassumption.
    2:{right. easy. }
    cbn -[finType_CS]. right.
    setoid_rewrite index_nth. split. easy.
    clear. unfold unflatten_acts,unflatten_acts'.
    rewrite map_repeat. cbn.
    (*Set Printing Implicit.*)
    pattern n at 1 2 4 5 6 7 8.
    replace n with (length (@repeat (option (Fin.t sig) * move) (@None (Fin.t sig), Nmove) n)) at 1.
    2:now rewrite repeat_length.
    rewrite Vector_of_list_length_eq.
    induction n;cbn. easy.
    rewrite <- IHn. easy. 
Qed.

Lemma isFlatteningTrans_validFlatTrans n sig' (M' : TM sig' n) f:
isFlatteningTransOf f (TM.trans (m:=M'))
-> validFlatTrans (Cardinality sig') n (Cardinality (TM.state M')) f.
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
  -intros. eapply H' in H as (?&?&?&?&?&->&->&->&->).
   repeat split.
   +eapply index_le.
   +rewrite map_length,vector_to_list_length. easy.
   +intros ? ([]&[=<- ]&?)%in_map_iff. eapply index_le.
   +eapply index_le.
   +rewrite map_length,vector_to_list_length. easy.
   +intros ? ? ([[]]&[= <- <-]&?)%in_map_iff. eapply index_le.
Qed.

Lemma unflattenTM_correct M:
  validFlatTM M
  -> isFlatteningTMOf M (unflattenTM M).
Proof.
  intros (?&?). destruct M.
  cbn in *.
  assert (H_st:(Init.Nat.max 1 states) = states) by now destruct states.
  econstructor; cbn - [finType_CS max].
  -easy.
  -now rewrite Fin_cardinality.
  -rewrite H_st.
   setoid_rewrite <- Fin_cardinality at 1. easy.
  -eapply unflatten_trans_correct. 
   rewrite H_st. easy.
  -generalize (def states).
   rewrite H_st. intros ?.
   unfold index. setoid_rewrite getPosition_nth. easy.
   +apply dupfree_elements.
   +refine (_:_ < Cardinality _).
    setoid_rewrite Fin_cardinality at 1. easy.
  -cbn -[max]. rewrite H_st.
   econstructor. reflexivity.
Qed.

Lemma isFlattening_is_valid M sig n (M':TM sig n):
  isFlatteningTMOf M M'
  -> validFlatTM M.
Proof.
  intros []. destruct M.
  cbn in *;subst.
  split;cbn.
  -now apply isFlatteningTrans_validFlatTrans.
  -apply index_le.
Qed.

Definition allSameEntry {X Y} eqbX eqbY `{_:eqbClass (X:=X) eqbX} `{eqbClass (X:=Y) eqbY} x y (f : list (X*Y)) :=
  forallb (fun '(x',y') => implb (eqbX x x') (eqbY y y')) f.

Definition isInjFinfuncTable {X Y} eqbX eqbY `{_:eqbClass (X:=X) eqbX} `{eqbClass (X:=Y) eqbY}
  := fix isInjFinfuncTable (f : list (X*Y)) : bool :=
  match f with
    [] => true
  | (x,y)::f => allSameEntry x y f
              && isInjFinfuncTable f
  end.

Lemma allSameEntry_spec X Y eqbX eqbY `{Hx:eqbClass (X:=X) eqbX} `{Hy:eqbClass (X:=Y) eqbY} x y (f:list (X*Y)):
  reflect (forall (y' : Y), (x, y') el f -> y = y') (allSameEntry x y f).
Proof.
  unfold allSameEntry.
  apply iff_reflect. rewrite forallb_forall.
  transitivity (forall x' y',  (x',y') el f -> implb (eqbX x x') (eqbY y y') = true).
  2:{split. now intros ? [].
     intros H x' y'. specialize (H (x',y'));cbn in H. easy. }
  split.
  -intros H x' y' ?.
   destruct (Hx x x'). 2:easy.
   edestruct (Hy y y') as [ | []]. easy.
   subst. eauto.
  -intros H y' ?.
   specialize (H x y').
   destruct (Hx x x). 2:easy.
   edestruct (Hy y y') as [ | ]. easy.
   apply H in H0. easy.
Qed.

Lemma isInjFinfuncTable_spec X Y eqbX eqbY `{Hx:eqbClass (X:=X) eqbX} `{Hy:eqbClass (X:=Y) eqbY} (f:list (X*Y)):
  reflect (forall (a : X) (b b' : Y), (a, b) el f -> (a, b') el f -> b = b') (isInjFinfuncTable f).
Proof.
  induction f as [ |[x y] f].
  cbn;constructor. easy.
  cbn.
  edestruct (allSameEntry_spec x y f) as [H' | H'].
  2:{cbn. constructor.
     intros H. eapply H'.  intros.
     eapply H;[left|right].  all:easy.
  }
  cbn.
  eapply ssrbool.equivP. eassumption.
  split. 2:now firstorder.
  intros ? ? ? ? [[= -> ->]| ] [[= ->] | ]. all:subst.
  3:symmetry. all:easy.
Qed.           

Definition isBoundTransTable (sig n states : nat) (f : list (nat * list (option nat) * (nat * list (option nat * move)))) :=
  forallb (fun '((s,v),(s',v')) =>
             (s <? states)
               && (length v =? n)
               && (forallb (fun a => match a with None => true | Some a => a <? sig end) v)
               && (s' <? states)
               && (length v' =? n)
               && (forallb (fun a => match fst a with None => true | Some a  => a <? sig end) v')) f.

Lemma isBoundTransTable_spec sig n states f:
  reflect (forall (s s' : nat) (v : list (option nat)) (v' : list (option nat * move)),
              (s, v, (s', v')) el f ->
              s < states /\
          | v | = n /\
                (forall a : nat, Some a el v -> a < sig) /\
                s' < states /\ | v' | = n /\ (forall (a : nat) (m : move), (Some a, m) el v' -> a < sig))
          (isBoundTransTable sig n states f).
Proof.
  unfold isBoundTransTable.
  apply iff_reflect. rewrite forallb_forall.
  transitivity (forall (s s' : nat) (v : list (option nat)) (v' : list (option nat * move)),
                    (s, v, (s', v')) el f 
     -> (((s <? states) && (| v | =? n) && forallb (fun a : option nat => match a with
                                                                     | Some a => a <? sig
                                                                     | None => true
                                                                     end) v && (s' <? states) && (| v' | =? n) &&
     forallb (fun a : option nat * move => match fst a with
                                           | Some a => a <? sig
                                           | None => true
                                      end) v') = true)).
  2:{split. now intros H [[] []]. 
     intros H s s' v v'. specialize (H ((s,v),(s',v')));cbn in H. easy. }
  do 4 (eapply Morphisms_Prop.all_iff_morphism;intros ?).
  eapply Morphisms_Prop.iff_iff_iff_impl_morphism. easy.
  rewrite <- !andb_assoc. rewrite !andb_true_iff. 
  repeat apply Morphisms_Prop.and_iff_morphism.
  1,4:now rewrite Nat.ltb_lt.
  1,3:now rewrite Nat.eqb_eq.
  all:rewrite forallb_forall.
  {split.
   -intros ? []. rewrite Nat.ltb_lt. all:easy.
   -intros H ? ?%H. now rewrite <- Nat.ltb_lt.
  }
  {split.
   -intros ? [[] ]; cbn - [Nat.ltb]. rewrite Nat.ltb_lt. all:easy.
   -intros H ? ? ?%H. now rewrite <- Nat.ltb_lt.
  }
Qed.   

Definition isValidFlatTrans sig n states (f : list (nat * list (option nat) * (nat * list (option nat * move)))) :=
  isInjFinfuncTable  f && isBoundTransTable sig n states f.

Lemma isValidFlatTrans_spec sig n states f:
  reflect (validFlatTrans sig n states f)
          (isValidFlatTrans sig n states f).
Proof.
  unfold isValidFlatTrans.
  eapply iff_reflect.
  rewrite andb_true_iff. rewrite <- !reflect_iff.
  2:{ eapply isBoundTransTable_spec. }
  2:{ eapply isInjFinfuncTable_spec. }
  split.
  -now intros [].
  -econstructor. all:easy.
Qed.

Definition isValidFlatTM M :=
  isValidFlatTrans M.(sig) M.(tapes) M.(states) M.(trans) && (M.(start) <? M.(states)).

Lemma isValidFlatTM_spec M:
  reflect (validFlatTM M)
          (isValidFlatTM M).
Proof.
  unfold isValidFlatTM.
  eapply iff_reflect.
  destruct M; cbn -[Nat.ltb].
  rewrite andb_true_iff. rewrite <- !reflect_iff.
  2:{ apply Nat.ltb_spec0. }
  2:{ apply isValidFlatTrans_spec. }
  split;intros []. all:easy.
Qed.

(** ** unflatten Tapes *)

Definition isValidFlatTape (sig:nat) (t:tape nat):=
  forallb (fun x => Nat.ltb x sig) (tapeToList t).

Definition isValidFlatTapes (sig:nat) n (t:list (tape nat)):=
  if length t =? n then forallb (isValidFlatTape sig) t else false.

Lemma tapeToList_map_commute sig sig' (f : sig -> sig') t :
  tapeToList (mapTape f t) = map f (tapeToList t).
Proof.
  destruct t;cbn. all:simpl_list.
  all:try rewrite !map_rev. all:easy.
Qed.

Lemma flatteningTapeIsValid (sig:finType) n t (t' : TM_facts.tapes sig n):
  isFlatteningTapesOf t t' ->
  isValidFlatTapes (Cardinality.Cardinality sig) n t = true.
Proof.
  intros H. inv H.
  unfold isValidFlatTapes.
  rewrite vector_to_list_length. rewrite Nat.eqb_refl.
  induction t' as [ |t];cbn. easy.
  rewrite andb_true_iff. split.
  2:{easy. }
  unfold isValidFlatTape.
  rewrite tapeToList_map_commute.
  setoid_rewrite forallb_forall.
  intros ? (?&?&?)%in_map_iff.
  rewrite Nat.ltb_lt.
  subst. eapply index_le.
Qed.


Lemma isUnflattableTape sig t:
  isValidFlatTape (Cardinality sig) t = true -> {t' & t = (mapTape (index (F:=sig)) t')}.
Proof.
  cbn. unfold isValidFlatTape.
  intros H. rewrite forallb_forall in H. setoid_rewrite Nat.ltb_lt in H.
  destruct t;cbn - [Nat.ltb].
  -exists (niltape _). easy.
  -eexists (leftof _ _). cbn. f_equal.
   +symmetry;eapply index_nth_elem. apply H. cbn;easy.
   +erewrite MCList.map_map_compose. erewrite map_ext_in. now rewrite map_id.
    intros. cbn. unfold Basics.compose. eapply index_nth_elem. apply H. cbn;easy.
  -eexists (rightof _ _). cbn. f_equal.
   +symmetry;eapply index_nth_elem. apply H. cbn;easy.
   +erewrite MCList.map_map_compose. erewrite map_ext_in. now rewrite map_id.
    intros. cbn. unfold Basics.compose. eapply index_nth_elem. apply H. cbn. rewrite in_app_iff, <- in_rev. eauto. 
  -eexists (midtape _ _ _). cbn. f_equal.
   +erewrite MCList.map_map_compose. erewrite map_ext_in. now rewrite map_id.
    intros. cbn. unfold Basics.compose. eapply index_nth_elem. apply H. cbn. rewrite in_app_iff, <- in_rev. eauto. 
   +symmetry;eapply index_nth_elem. apply H. cbn;easy.
   +erewrite MCList.map_map_compose. erewrite map_ext_in. now rewrite map_id.
    intros. cbn. unfold Basics.compose. eapply index_nth_elem. apply H. cbn. rewrite in_app_iff, <- in_rev. eauto.
    Unshelve.
    all:cbn in H.
    all:eapply defFin.
    all:eapply Nat.le_lt_trans;[ | eapply H;easy].
    all:Lia.lia.
Qed.
   
Lemma isUnflattableTapes sig n t :
  isValidFlatTapes (Cardinality sig) n t = true -> {t' & isFlatteningTapesOf (sig:=sig) (n:=n) t t'}.
Proof.
  cbn. unfold isValidFlatTapes.
  intros H. destruct (Nat.eqb_spec (length t) n). 2:easy. subst n.
  induction t.
  -eexists [| |]. rewrite isFlatteningTapesOf_iff. easy.
  -cbn in H.
   rewrite !andb_true_iff in H. destruct H as (H'&H).
   apply IHt in H as (v'&Hv).
   apply isUnflattableTape in H' as (t0&Ht0).
   eexists (t0:::v').
   rewrite isFlatteningTapesOf_iff in *. cbn. f_equal. all: now cbv.
Qed.

(** ** unflatten Conf *)

Definition validFlatTape sig (t : tape nat) :=
  forall n, n el tapeToList t -> n < sig.

Lemma isValidFlatTape_spec sig t :
  reflect (validFlatTape sig t) (isValidFlatTape sig t).
Proof.
  unfold validFlatTape, isValidFlatTape.
  apply iff_reflect. rewrite forallb_forall. setoid_rewrite Nat.ltb_lt. easy.
Qed.
      

Definition validFlatConf M (c:mconfigFlat):=
  let (s,ts) := c in
   length ts = M.(tapes) /\ Forall (validFlatTape M.(sig)) ts /\ s < M.(states).

(*
Lemma isValidFatConf_spec M c:
  reflect (validFlatConf M c) (isFlatteningConfigOf (M.(states)) M.(sig) M.(tapes) c).
Proof.
  unfold validFlatTape, isValidFlatTape.
  apply iff_reflect. rewrite forallb_forall. setoid_rewrite Nat.ltb_lt. easy.
Qed.
*)
