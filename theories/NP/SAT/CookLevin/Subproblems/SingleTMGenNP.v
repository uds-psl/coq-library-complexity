From Undecidability.TM Require Import TM_facts.
From Undecidability.L.TM Require Import TMEncoding.
From Complexity.L.TM Require Import TMflat TMflatFun TMunflatten TMflatten.
From Complexity.Libs.CookPrelim Require Import FlatFinTypes MorePrelim.
From Complexity.NP Require Export TMGenNP_fixed_mTM. 

(** * Definition of a generic problem for single-tape Turing machines *)

Definition isValidCert (sig : finType) k' (c : list sig) := |c| <= k'.
Definition isValidInput (sig : finType) s k' (inp : list sig) := exists c, isValidCert k' c /\ inp = s ++ c. 

(** generic problem for single-tape machine whose head will always start at the leftmost position (i.e. initial tapes are niltape or leftof) *)
(** the alphabet is part of the instance, not a parameter *)
Definition SingleTMGenNP (i : { sig : finType & (TM sig 1 * list sig * nat * nat)%type } ) : Prop := 
  match i with existT sig (tm, s, k', t) => exists cert, |cert| <= k'
                                                      /\ exists f, loopM (initc tm ([|initTape_singleTapeTM (s ++ cert)|])) t = Some f
  end.

(** a flat version defined via the non-flat one *)
Definition FlatSingleTMGenNP : flatTM * list nat * nat * nat -> Prop :=
  fun '(M,s,maxSize, steps (*in unary*)) =>
    exists sig (M':TM sig 1) sfin, isFlatteningTMOf M M' /\ isFlatListOf s sfin /\ SingleTMGenNP (existT _ _ (M', sfin, maxSize, steps)). 

(** another definition via the flat semantics *)
Definition FlatFunSingleTMGenNP : flatTM * list nat * nat * nat -> Prop := 
  fun '(M, s, maxSize, steps) => 
    list_ofFlatType (sig M) s /\ tapes M = 1
    /\ exists cert f, list_ofFlatType (sig M) cert /\ |cert| <= maxSize /\ execFlatTM M [initTape_singleTapeTM (s ++ cert)] steps = Some f.  


(** the two definitions reduce to each other via the identity function *)

Lemma vec_case1 (X : Type) (v : Vector.t X 1) : exists x, v = [|x|].
Proof. 
  eapply Vector.caseS' with (v0:=v).
  intros. revert t. apply Vector.case0. easy.
Qed. 

Proposition initTape_mapTape_index (sig : finType) (tp : tape sig) s: 
  mapTape index tp = initTape_singleTapeTM s 
  -> exists s', tp = initTape_singleTapeTM s' /\ isFlatListOf s s'.
Proof. 
  intros H. destruct s; cbn in H.
  - destruct tp; cbn in H; inv H. now exists []. 
  - destruct tp; cbn in H; inv H. now exists (e :: l).
Qed. 

Lemma initTape_isFlatteningConfigOf (sig states : finType) (s : list nat) s0 (c0 : mconfig sig states 1): 
  isFlatteningConfigOf (s0, [initTape_singleTapeTM s]) c0 
  -> exists s0' s', index s0' = s0 /\ isFlatListOf s s' /\ c0 = mk_mconfig s0' [|initTape_singleTapeTM s'|].
Proof. 
  intros H. inv H. inv Ht. destruct c0. cbn -[mapTapes] in H0. 
  specialize (vec_case1 ctapes) as (tp & ->). cbn in H0.
  inv H0. apply initTape_mapTape_index in H1 as (s' & -> & H1). 
  cbn. exists cstate, s'. easy.
Qed.  

Fact isFlatListOf_app_inv (f : finType) s1 s2 (s : list f): 
  isFlatListOf (s1 ++ s2) s 
  -> exists s1' s2', s = s1' ++ s2' /\ isFlatListOf s1 s1' /\ isFlatListOf s2 s2'.
Proof. 
  unfold isFlatListOf. 
  intros H. 
  symmetry in H. apply map_eq_app in H as (s1' & s2' & -> & -> & ->). eauto.
Qed. 

Lemma FlatFunSingleTMGenNP_FlatSingleTMGenNP_equiv M s maxSize steps: 
  FlatFunSingleTMGenNP (M, s, maxSize, steps) <-> FlatSingleTMGenNP (M, s, maxSize, steps). 
Proof. 
  split. 
  - intros (H1 & H2 & (cert & f & H3 & H4 & H5)). 
    specialize (proj1 (execFlatTM_correct _ _ _ _) H5) as (fsig & n & M' & c0 & c' & F1 & F2 & F3). 
    destruct F1. 
    rewrite H2 in eq__tapes. subst. 
    exists fsig, M'. specialize (initTape_isFlatteningConfigOf F2) as (s0' & s' & F5 & F4 & ->). 
    apply isFlatListOf_app_inv in F4 as (s'' & cert' & -> & F6 & F7).
    exists s''. split; [constructor; eauto | split; [apply F6 | ]].
    cbn. exists cert'. 
    split.
    { unfold isFlatListOf in F7. apply list_eq_length in F7. rewrite map_length in F7. Lia.lia. }
    exists c'. unfold initc. enough (TM.start M' = s0') by easy. 
    rewrite <- F5 in eq__start. now apply injective_index in eq__start. 
  - intros (fsig & M' & sfin & F1 & F2 & (certfin & F3 & (f & F4))). 
    split. 
    { destruct F1. rewrite eq__sig. unfold Cardinality.Cardinality. eapply isFlatListOf_list_ofFlatType, F2. } 
    split. 
    { destruct F1. apply eq__tapes. }
    exists (map index certfin), (flattenConfig f). 
    split. 
    { destruct F1. rewrite eq__sig. unfold Cardinality.Cardinality. eapply isFlatListOf_list_ofFlatType. reflexivity. }
    split; [now rewrite map_length | ].
    apply execFlatTM_correct. 
    exists fsig, 1, M', (initc M' [|initTape_singleTapeTM (sfin ++ certfin)|]), f. 
    split; [ apply F1 | split; [ | split; [apply F4 | apply flattenConfig_isFlatteningConfigOf]]]. 
    rewrite isFlatteningConfigOf_iff.
    exists [initTape_singleTapeTM (s ++ map index certfin)].  
    destruct F1. 
    rewrite eq__start. 
    cbn. split; [ | reflexivity].
    apply isFlatteningTapesOf_iff.
    cbn. rewrite F2, <- map_app. generalize (sfin ++ certfin). intros l. 
    destruct l; cbn; easy. 
Qed.
