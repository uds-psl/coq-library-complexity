From Undecidability.Shared.Libs.PSL Require Import FiniteTypes.
Require Import Undecidability.Shared.Libs.PSL.FiniteTypes.BasicDefinitions.
Require Import Lia.
From Complexity.L.Complexity Require Import MorePrelim.
Require Export smpl.Smpl. 

(** * Representation of finite types by natural numbers *)
(** This is needed as working with the direct extraction of finite types to L is not pleasant *)

(** A finite type is represented by the number of its elements *)
Definition finRepr (X : finType) (n : nat) := n = |elem X|. 

(** We define what it means for a number to be of a flat type *)
Definition ofFlatType (k : nat) (e : nat) := e < k.

(** We just enumerate the elements starting at 0 *)
Definition finReprEl (X : finType) (n : nat) k (x : X) := finRepr X n /\ index x = k.  

(** A weaker version that does not explicitly enforce x to have a flat type *)
Definition finReprEl' (X : finType) (k : nat) (x : X) := index x = k. 

Lemma finReprEl_finReprEl' (X : finType) (n k : nat) (x : X) : finReprEl n k x -> finReprEl' k x.
Proof. unfold finReprEl, finReprEl'. easy. Qed.

Lemma finReprEl_ofFlatType (X : finType) (n k : nat) (x : X) : finReprEl n k x -> ofFlatType n k. 
Proof. 
  intros [H1 H2].
  unfold finRepr, ofFlatType in *.
  rewrite H1, <- H2. apply index_le.
Qed. 

(** For some of the proofs below, the stronger version of finReprEl is much more pleasant than the weaker version finReprEl' (e.g. for sum types)*)

(** flat type constructors *)
Definition flatOption (n : nat) := S n.
Definition flatProd (a b : nat) := a * b.
Definition flatSum (a b : nat) := a + b.

(** flat value constructors *)
Definition flatNone := 0.
Definition flatSome k := S k. 
Definition flatInl (k : nat) := k.
Definition flatInr (a: nat) k := a + k. 
Definition flatPair (a b : nat) x y := x * b + y. 

Smpl Create finRepr. 
Ltac finRepr_simpl := smpl finRepr; repeat smpl finRepr. 

Smpl Add (match goal with |- finReprEl' _ _ => eapply finReprEl_finReprEl' end) : finRepr.

Lemma finReprOption (X : finType) (n : nat) : finRepr X n -> finRepr (finType_CS (option X)) (flatOption n).
Proof. 
  intros. unfold finRepr in *. unfold flatOption; cbn -[enum]. rewrite H; cbn.
  rewrite map_length. reflexivity. 
Qed. 
Smpl Add (apply finReprOption) : finRepr.

Lemma finReprElSome (X : finType) n k x : finReprEl n k x -> @finReprEl (finType_CS (option X)) (flatOption n) (flatSome k) (Some x). 
Proof. 
  intros (H1 & H2). split;cbn in *.
  - now apply finReprOption. 
  - rewrite getPosition_map. 2: unfold injective; congruence. now rewrite <- H2. 
Qed. 

Lemma finReprElNone (X : finType) n : finRepr X n -> @finReprEl (finType_CS (option X)) (flatOption n) flatNone None. 
Proof. 
  intros. split; cbn. 
  - now apply finReprOption.
  - now unfold flatNone. 
Qed. 

Ltac finReprOption :=
  lazymatch goal with
  | |- finReprEl _ _ (Some _) => apply finReprElSome
  | |- finReprEl _ _ None => apply finReprElNone
  | |- finRepr (finType_CS (option _)) _ => apply finReprOption
   end.

Smpl Add 99 finReprOption : finRepr.

Lemma finReprSum (A B: finType) (a b : nat) : finRepr A a -> finRepr B b -> finRepr (finType_CS (sum A B)) (flatSum a b). 
Proof. 
  intros. unfold finRepr in *. unfold flatSum; cbn in *.
  rewrite app_length. rewrite H, H0.
  unfold toSumList1, toSumList2. now rewrite !map_length.
Qed. 
Smpl Add (apply finReprSum) : finRepr. 

Lemma finReprElInl (A B : finType) (a b : nat) k x : finRepr B b -> finReprEl a k x -> @finReprEl (finType_CS (sum A B)) (flatSum a b) (flatInl k) (inl x). 
Proof. 
  intros H0 (H1 & H2). split. 
  - now apply finReprSum. 
  - unfold finRepr in H1. 
    clear H0 H1. cbn. unfold toSumList1, toSumList2, flatInl. 
    rewrite getPosition_app1 with (k := k).
    + reflexivity. 
    + rewrite map_length, <- H2. apply index_le. 
    + unfold index in H2. rewrite <- getPosition_map with (f := (@inl A B)) in H2. 2: now unfold injective.
      easy. 
Qed. 

Lemma finReprElInr (A B : finType) (a b : nat) k x : finRepr A a -> finReprEl b k x -> @finReprEl (finType_CS (sum A B)) (flatSum a b) (flatInr a k) (inr x). 
Proof. 
  intros H0 (H1 & H2). split. 
  - now apply finReprSum. 
  - clear H1. cbn. unfold toSumList1, toSumList2, flatInr. 
    rewrite getPosition_app2 with (k := k). 
    + rewrite map_length. unfold finRepr in H0. now cbn. 
    + rewrite map_length, <- H2. apply index_le. 
    + intros H1. apply in_map_iff in H1. destruct H1 as (? & ? &?); congruence. 
    + unfold index in H2. rewrite <- getPosition_map with (f := (@inr A B)) in H2. 2: now unfold injective. 
      easy. 
Qed. 

Ltac finReprSum :=
  lazymatch goal with
  | |- finReprEl _ _ (inl _) => apply finReprElInl
  | |- finReprEl _ _ (inr _) => apply finReprElInr
  | |- finRepr (finType_CS (sum _ _)) _ => apply finReprSum
  end.
Smpl Add 99 finReprSum : finRepr.

Lemma finReprProd (A B : finType) (a b : nat) : finRepr A a -> finRepr B b -> finRepr (finType_CS (prod A B)) (flatProd a b).  
Proof. 
  intros. unfold finRepr in *. unfold flatProd.
  cbn. now rewrite prodLists_length. 
Qed. 
Smpl Add (apply finReprProd) : finRepr.

Lemma finReprElPair (A B : finType) (a b : nat) k1 k2 x1 x2 : finReprEl a k1 x1 -> finReprEl b k2 x2 -> @finReprEl (finType_CS (prod A B)) (flatProd a b) (flatPair a b k1 k2) (pair x1 x2).
Proof. 
  intros (H1 & H2) (F1 & F2). split. 
  - now apply finReprProd. 
  - cbn. unfold flatPair. unfold finRepr in *.
    rewrite getPosition_prodLists with (k1 := k1) (k2 := k2); eauto. 
    + rewrite <- H2; apply index_le.
    + rewrite <- F2; apply index_le.
Qed. 

Ltac finReprProd :=
  lazymatch goal with
  | |- finReprEl _ _ (pair _ _) => apply finReprElPair
  | |- finRepr (finType_CS (prod _ _)) _ => apply finReprProd
  end.
Smpl Add 99 finReprProd : finRepr.

(** flattened lists *)
Definition isFlatListOf (X : finType) (l : list nat) (l' : list X) := l = map index l'.

Lemma isFlatListOf_cons (X : finType) (A : X) a l L: isFlatListOf (a :: l) (A :: L) <-> finReprEl' a A /\ isFlatListOf l L.
Proof. 
  unfold isFlatListOf in *. cbn. split; intros. 
  - inv H. easy. 
  - destruct H as (-> & ->). easy.
Qed. 

Lemma isFlatListOf_app (X : finType) (L1 L2 : list X) l1 l2 : isFlatListOf l1 L1 -> isFlatListOf l2 L2 -> isFlatListOf (l1 ++ l2) (L1 ++ L2). 
Proof. 
  revert L1. induction l1; intros.
  - unfold isFlatListOf in H; destruct L1; [easy | cbn in *; congruence ].
  - destruct L1; [ unfold isFlatListOf in H; cbn in H; congruence | ].
    apply isFlatListOf_cons in H as (H1 & H2). cbn. 
    apply isFlatListOf_cons; split; [ apply H1 | apply IHl1; easy].
Qed. 

Lemma isFlatListOf_functional (X: finType) (L1 L2 : list X) (l : list nat) : 
  isFlatListOf l L1 -> isFlatListOf l L2 -> L1 = L2. 
Proof. 
  unfold isFlatListOf. intros. rewrite H0 in H. apply map_injective in H; [easy | ].  
  intros a b H2. now apply injective_index, H2. 
Qed. 

Lemma isFlatListOf_injective (X : finType) (L : list X) (l1 l2 : list nat) :
  isFlatListOf l1 L -> isFlatListOf l2 L -> l1 = l2. 
Proof. 
  unfold isFlatListOf. intros. easy.
Qed. 


Lemma isFlatListOf_Some1 (T : finType) (T' : nat) (a : list nat) (b : list T) (n : nat) (x : nat):
  finRepr T T' -> isFlatListOf a b -> nth_error a n = Some x -> exists x', nth_error b n = Some x' /\ finReprEl T' x x'.
Proof. 
  intros. rewrite H0 in H1. rewrite nth_error_map in H1. 
  destruct (nth_error b n); cbn in H1; [ | congruence ]. 
  inv H1. exists e.
  split; [reflexivity | repeat split]. apply H. 
Qed. 

Lemma isFlatListOf_incl1 (X : finType) (fin : list X) flat l:
  isFlatListOf flat fin -> l <<= flat -> exists l', isFlatListOf (X := X) l l' /\ l' <<= fin.
Proof.
  intros. revert fin H. induction l; cbn in *; intros. 
  - exists []; split; eauto. unfold isFlatListOf. now cbn.
  - apply incl_lcons in H0 as (H0 & H1).
    apply IHl with (fin := fin) in H1 as (l' & H2 & H3). 
    2: apply H. 
    rewrite H in H0. apply in_map_iff in H0 as (a' & H4 & H5).
    exists (a' :: l'). split. 
    + unfold isFlatListOf. cbn. now rewrite <- H4, H2. 
    + cbn. intros ? [-> | H6]; eauto.
Qed.

Lemma isFlatListOf_incl2 (X : finType) (fin : list X) flat l':
  isFlatListOf flat fin -> l' <<= fin -> exists l, isFlatListOf (X := X) l l' /\ l <<= flat.
Proof.
  intros.
  exists (map index l'). split.
  - reflexivity.
  - induction l'; cbn. 
    + eauto.
    + apply incl_lcons in H0 as (H0 & H1).
      apply IHl' in H1. intros ? [<- | H2].
      * rewrite H. apply in_map_iff; eauto. 
      * now apply H1.  
Qed.

Lemma seq_isFlatListOf (X : finType) : isFlatListOf (seq 0 (|elem X|)) (elem X).  
Proof. 
  unfold isFlatListOf. unfold index. rewrite dupfree_map_getPosition. 
  2: apply dupfree_elements. 
  now change (fun x => getPosition (elem X) x) with (getPosition (elem X)). 
Qed.

Lemma repEl_isFlatListOf (X : finType) a (A : X) n : finReprEl' a A -> isFlatListOf (repEl n a) (repEl n A).
Proof. 
  induction n; cbn; intros; [ easy | now apply isFlatListOf_cons].
Qed. 

(** lists that only contain elements which belong to the flat representation of a finite type *)
Definition list_ofFlatType (k : nat) (l : list nat) := forall a, a el l -> ofFlatType k a. 

Lemma isFlatListOf_list_ofFlatType (X : finType) (L : list X) l : isFlatListOf l L -> list_ofFlatType (|elem X|) l. 
Proof. 
  intros. unfold list_ofFlatType. rewrite H. intros a (a' & <- & H1)%in_map_iff. 
  unfold ofFlatType. apply index_le. 
Qed. 

Lemma list_ofFlatType_app (l1 l2 : list nat) (k : nat) : list_ofFlatType k (l1 ++ l2) <-> list_ofFlatType k l1 /\ list_ofFlatType k l2. 
Proof. 
  split; intros; unfold list_ofFlatType in *. 
  - setoid_rewrite in_app_iff in H. split; intros; apply H; eauto. 
  - destruct H as (H1 & H2); setoid_rewrite in_app_iff; intros a [ | ]; eauto. 
Qed. 

Lemma list_ofFlatType_cons x y k : list_ofFlatType k (x :: y) <-> ofFlatType k x /\ list_ofFlatType k y. 
Proof. 
  split; unfold list_ofFlatType; intros. 
  - split; [ apply H; eauto | intros; apply H; eauto]. 
  - destruct H0 as [-> | H0]. 
    + apply (proj1 H). 
    + apply (proj2 H), H0. 
Qed. 

Definition list_finReprEl' (f : finType) (l : list nat) (L : list f ) := 
  (forall v, v el l -> exists v', v' el L /\ v = index v') /\ (forall v, v el L -> index v el l).

Lemma isFlatListOf_list_finReprEl' (f : finType) (l : list nat) (L : list f): isFlatListOf l L -> list_finReprEl' l L.
Proof. 
  unfold isFlatListOf, list_finReprEl'.
  intros Hmap. split. 
  - intros v Hel. rewrite Hmap in Hel. apply in_map_iff in Hel as (v' & <- & Hel). eauto.
  - intros v Hel. rewrite Hmap. apply in_map_iff. eauto.
Qed. 

(** Given a representation of a finite type by natural numbers, we can restore the original elements *)
Lemma finRepr_exists (X : finType) (x : nat) (a : nat) : 
  finRepr X x -> ofFlatType x a -> sigT (fun (a' : X) => finReprEl x a a'). 
Proof. 
  intros. unfold ofFlatType in H0. 
  assert (sigT (fun a' =>nth_error (elem X) a = Some a')) as (a' & H2).
  { 
    unfold ofFlatType in H0. rewrite H in H0.
    unfold Cardinality in H0. apply nth_error_Some in H0. destruct nth_error; easy. 
  } 
  exists a'. split; [ easy | ].
  unfold index. specialize (nth_error_nth H2) as <-.
  apply getPosition_nth. 
  + apply Cardinality.dupfree_elements. 
  + eapply nth_error_Some_length, H2. 
Qed.

Lemma finReprElP_exists (X : finType) n : ofFlatType (Cardinality X) n -> { e:X | finReprEl' n e}.
Proof. 
  intros. unfold ofFlatType,Cardinality in H. apply nth_error_Some in H. destruct (nth_error (elem X) n) eqn:H1; [ | congruence ].
  exists e. unfold finReprEl'. clear H.
  specialize (nth_error_nth H1) as <-. apply getPosition_nth. 
  + apply Cardinality.dupfree_elements. 
  + eapply nth_error_Some_length, H1.
Defined. 

Lemma finRepr_exists_list (X : finType) (x : nat) (l : list nat) : 
  finRepr X x -> list_ofFlatType x l -> sigT (fun (L : list X) => isFlatListOf l L). 
Proof. 
  revert x. induction l; intros.
  - exists []. unfold isFlatListOf. now cbn. 
  - apply list_ofFlatType_cons in H0 as (H0 & (L & H1)%IHl). 2: apply H.
    specialize (finRepr_exists H H0) as (a' & (_ &  H2)). 
    exists (a' :: L). unfold isFlatListOf. 
    now rewrite H1, <- H2. 
Defined. 

(** deciders for isValidFlattening*)
Definition ofFlatType_dec (b a : nat) := leb (S a) b.
Definition list_ofFlatType_dec (t : nat)  (s : list nat) := forallb (ofFlatType_dec t) s. 

Lemma leb_iff a b : leb a b = true <-> a <= b. 
Proof. 
  split; intros. 
  - now apply leb_complete. 
  - now apply leb_correct. 
Qed.

Lemma list_ofFlatType_dec_correct s t : list_ofFlatType_dec t s = true <-> list_ofFlatType t s. 
Proof. 
  unfold list_ofFlatType_dec, list_ofFlatType. rewrite forallb_forall. 
  unfold ofFlatType_dec. setoid_rewrite leb_iff. 
  split; intros H; intros; now apply H.
Qed. 
 
(** unflattening to Fin.t *)
Lemma unflattenString (f : list nat) k : list_ofFlatType k f -> {f' : list (finType_CS (Fin.t k)) & isFlatListOf f f'}.
Proof. 
  intros H. 
  eapply finRepr_exists_list with (X := finType_CS (Fin.t k)) in H as (a' & H). 
  2: { unfold finRepr. specialize (Fin_cardinality k). unfold Cardinality. easy. }
  eauto.
Qed. 

(** extraction *)
From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Import LProd LOptions LBool LSum.
From Complexity.L.Complexity Require Import PolyBounds. 
From Undecidability.L.Functions Require Import EqBool.
Require Import Nat. 

Instance term_id (X : Type) `{encodable X}: computableTime' (@id X) (fun a _ => (1, tt)). 
Proof. 
  extract. solverec. 
Qed.

Definition c__flatPair := c__add1 + 2 + c__mult1. 
Definition flatPair_time x b := mult_time x b + add_time (x * b) + c__flatPair.
Instance term_flatPair : computableTime' flatPair (fun a _ => (1, fun b _ => (1, fun x _ => (1, fun y _ => (flatPair_time x b, tt))))). 
Proof. 
  extract. solverec. unfold flatPair_time, c__flatPair; solverec. 
Defined. 

(*ofFlatTypeDec *)
Definition c__ofFlatTypeDec := c__leb2 + 2. 
Definition ofFlatType_dec_time (sig e : nat) := leb_time (1 + e) sig + c__ofFlatTypeDec. 
Instance term_ofFlatType_dec : computableTime' ofFlatType_dec (fun sig _ => (1, fun e _ => (ofFlatType_dec_time sig e, tt))). 
Proof. 
  extract. solverec. unfold ofFlatType_dec_time, c__ofFlatTypeDec. solverec. 
Defined. 
Definition c__ofFlatTypeDecBound := c__ofFlatTypeDec + c__leb. 
Definition poly__ofFlatTypeDec n := (n +1) * c__ofFlatTypeDecBound. 
Lemma ofFlatType_dec_time_bound sig e: ofFlatType_dec_time sig e <= poly__ofFlatTypeDec (size (enc sig)). 
Proof. 
  unfold ofFlatType_dec_time. rewrite leb_time_bound_r. unfold poly__ofFlatTypeDec, c__ofFlatTypeDecBound; nia.
Qed. 
Lemma ofFlatType_dec_poly : monotonic poly__ofFlatTypeDec /\ inOPoly poly__ofFlatTypeDec. 
Proof.
  split; unfold poly__ofFlatTypeDec; smpl_inO. 
Qed. 

(*list_ofFlatType_dec *)
Definition c__listOfFlatTypeDec := 3.
Definition list_ofFlatType_dec_time (sig : nat) (l : list nat) := forallb_time (fun x1 => ofFlatType_dec_time sig x1) l + c__listOfFlatTypeDec. 
Instance term_list_ofFlatType_dec : computableTime' list_ofFlatType_dec (fun sig _ => (1, fun l _ => (list_ofFlatType_dec_time sig l, tt))). 
Proof. 
  extract. solverec. unfold list_ofFlatType_dec_time, c__listOfFlatTypeDec. solverec. 
Qed. 

Definition c__listOfFlatTypeDecBound := c__forallb + c__listOfFlatTypeDec. 
Definition poly__listOfFlatTypeDec n := ((n+1) * (poly__ofFlatTypeDec n + c__listOfFlatTypeDecBound)).
Lemma list_ofFlatType_dec_time_bound t l : list_ofFlatType_dec_time t l <= poly__listOfFlatTypeDec (size (enc t) + size (enc l)).
Proof.
  unfold list_ofFlatType_dec_time. 
  erewrite forallb_time_bound_env.
  2: {
    split; [ intros | ]. 
    - rewrite (ofFlatType_dec_time_bound y a). poly_mono ofFlatType_dec_poly.
      2: apply le_add_l with (n := size(enc a)). reflexivity.
    - apply ofFlatType_dec_poly.
  }
  rewrite list_size_length.
  replace_le (size(enc l)) with (size (enc t) + size (enc l)) by lia at 1.
  setoid_rewrite Nat.add_comm at 5.
  unfold poly__listOfFlatTypeDec, c__listOfFlatTypeDecBound. nia.
Qed. 
Lemma list_ofFlatType_dec_poly : monotonic poly__listOfFlatTypeDec /\ inOPoly poly__listOfFlatTypeDec. 
Proof.
  split; unfold poly__listOfFlatTypeDec; smpl_inO; apply ofFlatType_dec_poly.
Qed. 
