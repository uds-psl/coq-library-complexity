From Complexity.L Require Import Functions.EqBool.
From Complexity.L.Datatypes Require Import LBool LNat LOptions LProd.
From Complexity.Libs Require Import UpToC.

From Complexity.L.Datatypes.List Require Export List_enc List_basics List_eqb List_extra List_fold List_in List_nat.

Definition c__listsizeCons := 5.
Definition c__listsizeNil := 4.
Lemma size_list X `{encodable X} (l:list X):
  size (enc l) = sumn (map (fun x => size (enc x) + c__listsizeCons) l)+ c__listsizeNil.
Proof.
  unfold enc at 1;cbn. unfold c__listsizeCons, c__listsizeNil. 
  induction l.
  -easy.
  -cbn [size]. solverec.
Qed.
 

Lemma size_list_cons (X : Type) (H : encodable X) x (l : list X):
  size (enc (x::l)) = size (enc x) + size (enc l) + c__listsizeCons.
Proof.
  rewrite !size_list. cbn. lia.
Qed.

Lemma size_rev X {_:encodable X} (xs : list X): L_facts.size (enc (rev xs)) = L_facts.size (enc xs).
Proof.
  rewrite !size_list,map_rev,<- sumn_rev. easy.
Qed.

Lemma size_list_In X {R__X  :encodable X} (x:X) xs:
  x el xs -> L_facts.size (enc x) <= L_facts.size (enc xs).
Proof.
  intro H. rewrite !size_list,sumn_map_add. rewrite <- (sumn_le_in (in_map _ _ _ H)) at 1. nia.
Qed.

Lemma size_list_enc_r {X} `{encodable X} (l:list X):
  length l <= size (enc l).
Proof.
  rewrite size_list. induction l;cbn. all: unfold c__listsizeNil, c__listsizeCons in *; lia.
Qed.


Lemma list_app_size {X : Type} `{encodable X} (l l' : list X) :
  size(enc (l ++ l')) + c__listsizeNil = size(enc l) + size(enc l').
Proof.
  repeat rewrite size_list. 
  rewrite map_app. rewrite sumn_app. lia. 
Qed. 

Lemma list_size_at_least {X : Type} {H: encodable X} (l : list X) : size(enc l) >= c__listsizeNil. 
Proof. rewrite size_list. lia. Qed.

Lemma list_app_size_l {X : Type} {H : encodable X} (l l' : list X) :
  size(enc (l ++ l')) >= size (enc l). 
Proof. 
  enough (size(enc (l++l')) + c__listsizeNil >= size(enc l) + c__listsizeNil) by lia. 
  rewrite list_app_size. specialize (list_size_at_least l'). lia. 
Qed. 

Lemma list_app_size_r {X : Type} `{encodable X} (l l' : list X) :
  size(enc (l ++ l')) >= size (enc l'). 
Proof. 
  enough (size(enc (l++l')) + c__listsizeNil >= size(enc l') + c__listsizeNil) by lia. 
  rewrite list_app_size.  specialize (list_size_at_least l). lia. 
Qed. 

Lemma list_size_cons {X : Type} `{encodable X} (l : list X) (a : X) :
  size(enc (a::l)) = size(enc a) + size(enc l) + c__listsizeCons.
Proof. repeat rewrite size_list. cbn.  lia. Qed. 

Lemma list_size_app (X : Type) (l1 l2 : list X) `{encodable X} : size (enc (l1 ++ l2)) <= size (enc l1) + size (enc l2). 
Proof. 
  rewrite <- list_app_size. lia. 
Qed. 

Lemma list_size_concat (X : Type) (l : list (list X)) `{encodable X} : size (enc (concat l)) <= size (enc l). 
Proof. 
  induction l; cbn; [easy | ]. 
  now rewrite list_size_app, list_size_cons, IHl. 
Qed. 

Lemma list_size_length {X : Type} `{encodable X} (l : list X) : |l| <= size(enc l). 
Proof. 
  rewrite size_list. induction l.
  - cbn; lia. 
  - cbn. rewrite IHl. unfold c__listsizeCons; lia. 
Qed. 

Lemma list_el_size_bound {X : Type} `{encodable X} (l : list X) (a : X) :
  a el l -> size(enc a) <= size(enc l). 
Proof. 
  intros H1. 
  rewrite size_list. 
  induction l. 
  - destruct H1.
  - cbn. destruct H1. rewrite H0; clear H0. solverec. rewrite IHl. 2: assumption. 
    solverec. 
Qed. 

Definition maxSize {X : Type} `{encodable X} (l : list X) := maxl (map (fun x => size (enc x)) l). 
Lemma maxSize_enc_size {X : Type} `{encodable X} (l : list X) : maxSize l<= size (enc l). 
Proof. 
  unfold maxSize. rewrite maxl_leq_l. 
  2: { intros n (x & <- & Hel)%in_map_iff. apply list_el_size_bound, Hel. }
  easy.
Qed. 

Lemma list_size_enc_length {X : Type} `{encodable X} (l : list X) : size (enc (|l|)) <= size (enc l). 
Proof. 
  rewrite size_list. rewrite size_nat_enc. unfold c__natsizeS, c__natsizeO, c__listsizeNil, c__listsizeCons. induction l; cbn; lia. 
Qed. 

Lemma list_size_of_el {X : Type} `{encodable X} (l : list X) (k : nat) : (forall a, a el l -> size(enc a) <= k) -> size(enc l) <= (k * (|l|)) + c__listsizeCons * (|l|) +  c__listsizeNil . 
Proof.
  intros H1. induction l. 
  - cbn. rewrite size_list. cbn.  lia.
  - cbn -[c__listsizeCons]. rewrite list_size_cons. rewrite IHl; [ |now firstorder]. rewrite H1; [ |now left].
    solverec. 
Qed.

Definition rem {X: eqType} := remove (@eqType_dec X).

Lemma list_rem_size_le (X : eqType) `{H : encodable X} (l : list X) x : size (enc (rem x l)) <= size (enc l).
Proof.
  induction l. 
  - reflexivity.
  - cbn. destruct eqType_dec; cbn; rewrite !list_size_cons, IHl; lia.
Qed.

Lemma list_incl_dupfree_size (X : eqType) `{encodable X} (a b : list X) : a <<= b -> NoDup a -> size (enc a) <= size (enc b). 
Proof. 
  intros H1 H2.  revert b H1.
  induction H2 as [ | a0 a H1 H2 IH]; intros. 
  - cbn. rewrite !size_list. cbn. lia.
  - specialize (IH (rem a0 b)).
    rewrite list_size_cons.
    cbn. rewrite IH. 
    2: { 
      assert (rem a0 (a0 :: a) = a).
      { unfold rem. rewrite remove_cons. now apply notin_remove. } 
      rewrite <- H3. now apply remove_incl.
    } 
    specialize (H0 a0 (or_introl eq_refl)). apply in_split in H0 as (b1 & b2 & ->).
    unfold rem. rewrite !size_list, !remove_app, !map_app, !sumn_app. cbn. 
    destruct (eqType_dec a0 a0) as [|E]; [|now contradiction E].
    pose (elem_size := fun (x : X) => size (enc x) + c__listsizeCons). 
    fold elem_size.
    enough (sumn (map elem_size (rem a0 b1)) <= sumn (map elem_size b1) /\ sumn (map elem_size (rem a0 b2)) <= sumn (map elem_size b2)) as H0.
    { destruct H0 as [-> ->]. nia. }
    specialize (list_rem_size_le b1 a0) as F1. 
    specialize (list_rem_size_le b2 a0) as F2. 
    rewrite !size_list in F1. rewrite !size_list in F2. 
    fold elem_size in F1. fold elem_size in F2.
    split; nia.
Qed.
