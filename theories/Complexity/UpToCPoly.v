From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Complexity.Complexity Require Export Definitions.
From Undecidability.L.Complexity Require Export UpToC UpToCNary.
From Complexity.Libs.CookPrelim Require Import Tactics. 

(* Coq 8.11 or 8.10 changed lia so that it isn't able to deal with η conversion anymore; use this tactic to fix *)
Ltac simp_comp_arith := cbn -[Nat.add Nat.mul]; repeat change (fun x => ?h x) with h.

(** new definitions for UpToC *)
Notation c_of H := (@c__leUpToC _ _ _ (correct__UpToC (projT1 H))).

Tactic Notation "exists_const" ident(c):= match goal with  |- sigT  (fun (x : (UpToC ?E )) => _) => evar (c : nat); exists_UpToC (fun y => c * E y) end.

Ltac and_solve p := subst p; simp_comp_arith; try reflexivity; try lia. 
Tactic Notation "exists_poly" ident(p) := evar (p : nat -> nat); exists p. 
Tactic Notation "inst_const" := instantiate (1 := fun _ => _); cbn; reflexivity. 
Ltac set_consts := 
  repeat match goal with 
  |- context[(@c__leUpToC ?A ?B ?C (@correct__UpToC ?D ?E (@projT1 ?F ?G ?H)))] => 
      let c := fresh "C" in 
      set (c := @c__leUpToC A B C (@correct__UpToC D E (@projT1 F G H)))
  end.

(* has the intuitive semantics of instantiate (c := c'); but tries to unfold local definitions in c' first in order to make this instantiation valid (c' itself has to be a local definition)*)
Ltac inst_with c c' := 
  repeat match goal with 
  | c'' := ?h |- _ => constr_eq c' c'';
      match goal with 
      | Ce := _ |- _ => 
          lazymatch h with context[Ce] => 
            assert_fails (constr_eq c' Ce); unfold Ce in c' 
          end 
      end
  end; 
  match goal with 
  | c'' := ?h |- _ => constr_eq c' c''; instantiate (c := h)
  end; 
  try clear c'; 
  repeat match goal with 
  | c0 := _ |- _ => try fold c0 in c 
  end; 
  subst c.
Tactic Notation "inst" ident(c) "with" constr(t) := let c' := fresh "c" in set (c' := t); inst_with c c'.

Record isPoly (X : Type) `{encodable X} (f : X -> nat) : Set := 
  { 
    isP__poly : nat -> nat; 
    isP__bounds : forall x, f x <= isP__poly (size (enc x)); 
    isP__inOPoly : inOPoly isP__poly; 
    isP__mono : monotonic isP__poly;
  }. 
Arguments isP__bounds {X} {H} {_} _. 
Arguments isP__poly {X} {H} {_} _. 

Smpl Add 15 apply isP__mono : inO. 
Smpl Add 15 apply isP__inOPoly : inO. 

Tactic Notation "rewpoly" constr(s) :=
  rewrite (isP__bounds s).
Tactic Notation "rewpoly" constr(s) "at" ne_integer_list(occ) := 
  rewrite (isP__bounds s) at occ. 

Tactic Notation "monopoly" constr(H) "at" ne_integer_list(occ) := 
  setoid_rewrite (isP__mono H) at occ. 
Tactic Notation "monopoly" constr(H) := 
  erewrite (isP__mono H). 



Tactic Notation "replace_le" constr(s) "with" constr(r) "by" tactic(tac) :=
  let H := fresh in assert (s <= r) as H by tac; rewrite !H; clear H. 
Tactic Notation "replace_le" constr(s) "with" constr(r) "by" tactic(tac) "at" ne_integer_list(occ) := 
  let H := fresh in assert (s <= r) as H by tac; rewrite H at occ; clear H. 
Tactic Notation "replace_le" constr(s) "with" constr(r) :=
  let H := fresh in assert (s <= r) as H; [ | rewrite !H; clear H]. 





From Undecidability.L.Datatypes Require Import Lists LNat. 
(** useful lemmas *)
#[export]
Instance proper_lt_mul : Proper (lt ==> eq ==> le) Nat.mul. 
Proof. 
  intros a b c d e f. nia.
Qed. 

#[export]
Instance proper_lt_add : Proper (lt ==> eq ==> le) Nat.add.
Proof. 
  intros a b c d e f. nia. 
Qed. 

#[export]
Instance proper_le_pow : Proper (le ==> eq ==> le) Nat.pow.
Proof. 
  intros a b H1 d e ->. apply Nat.pow_le_mono_l, H1. 
Qed. 

#[export]
Instance mult_lt_le : Proper (eq ==> lt ==> le) mult. 
Proof. 
  intros a b -> d e H. nia. 
Qed.

#[export]
Instance add_lt_lt : Proper (eq ==> lt ==> lt) Nat.add. 
Proof. 
  intros a b -> c d H. lia.
Qed.

#[export]
Instance le_lt_impl : Proper (le --> eq ==> Basics.impl) lt. 
Proof. 
  intros a b H d e ->. unfold Basics.flip in H. unfold Basics.impl. lia. 
Qed.

#[export]
Instance lt_le_impl : Proper (lt --> eq ==> Basics.impl) le. 
Proof. 
  intros a b H d e ->. unfold Basics.flip in H. unfold Basics.impl. lia.  
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


Require Import Complexity.Libs.CookPrelim.MorePrelim. 
Lemma list_subsequence_size_bound {X : Type} `{encodable X} (l l': list X) :
  subsequence l l' -> size (enc l) <= size (enc l').
Proof. 
  intros (C & D & ->). 
  enough (size(enc l) <= size(enc (l++D))). 
  {
    rewrite H0. specialize (list_app_size_r C (l++D)). lia. 
  }
  specialize (list_app_size_l l D). lia. 
Qed. 

Lemma list_size_cons {X : Type} `{encodable X} (l : list X) (a : X) : size(enc (a::l)) = size(enc a) + size(enc l) + c__listsizeCons.
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

Lemma map_time_mono (X : Type) (f1 f2 : X -> nat) (l : list X): (forall x : X, x el l -> f1 x <= f2 x) -> map_time f1 l <= map_time f2 l. 
Proof. 
  intros H. induction l; cbn; [lia | ].
  rewrite IHl, H by easy. lia. 
Qed.

Lemma sumn_map_mono (X : Type) (f1 f2 : X -> nat) l : (forall x, x el l -> f1 x <= f2 x) -> sumn (map f1 l) <= sumn (map f2 l).
Proof. 
  intros H. induction l; cbn; [lia | ]. 
  rewrite IHl, H by easy. lia. 
Qed.

Lemma sumn_map_const (X : Type) c (l : list X) : sumn (map (fun _ => c) l) = |l| * c. 
Proof. 
  induction l; cbn; [lia | ]. 
  rewrite IHl. lia. 
Qed.

Lemma nat_size_lt a b: a < b -> size (enc a) < size (enc b). 
Proof. 
  intros H. rewrite !size_nat_enc. unfold c__natsizeS; nia. 
Qed.

Lemma nat_size_le a b: a <= b -> size (enc a) <= size (enc b). 
Proof. 
  intros H. rewrite !size_nat_enc. unfold c__natsizeS; nia. 
Qed.

(* Lemma le_add_l n m : m <= n + m. *)
(* use Nat.le_add_l *)


(** Facts we need to prove that a small assignment has an encoding size which is polynomial in the CNF's encoding size *)
Lemma list_dupfree_incl_length (X : eqType) (a b : list X) : a <<= b -> dupfree a -> |a| <= |b|. 
Proof. 
  intros H1 H2. eapply NoDup_incl_length; assumption.
Qed. 

Definition rem {X: eqType} := remove (@eqType_dec X).

Lemma list_rem_size_le (X : eqType) `{H : encodable X} (l : list X) x : size (enc (rem x l)) <= size (enc l).
Proof.
  induction l. 
  - reflexivity.
  - cbn. destruct eqType_dec; cbn; rewrite !list_size_cons, IHl; lia.
Qed.

Lemma remove_cons {X} {dec: eq_dec X} (a: X) l: remove dec a (a :: l) = remove dec a l.
Proof.
  cbn. destruct (dec a a) as [|H].
  - reflexivity.
  - now contradiction H.
Qed.

Lemma list_incl_dupfree_size (X : eqType) `{encodable X} (a b : list X) : a <<= b -> dupfree a -> size (enc a) <= size (enc b). 
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
    specialize (H0 a0 (or_introl eq_refl)). apply In_explicit in H0 as (b1 & b2 & ->).
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
