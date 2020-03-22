
From Undecidability.L.Complexity Require Export NP ONotation. 
From Undecidability.L.Tactics Require Import LTactics.
From Undecidability.L.Complexity Require Import MorePrelim.
From Undecidability.L Require Export Datatypes.LLists Datatypes.LLNat.
From Undecidability.L.Functions Require Import EqBool. 

(** why the heck isn't this in the standard library? no one knows... *)
Instance proper_lt_mul : Proper (lt ==> eq ==> le) Nat.mul. 
Proof. 
  intros a b c d e f. nia.
Qed. 

Instance proper_lt_add : Proper (lt ==> eq ==> le) Nat.add.
Proof. 
  intros a b c d e f. nia. 
Qed. 

Instance proper_le_pow : Proper (le ==> eq ==> le) Nat.pow.
Proof. 
  intros a b H1 d e ->. apply Nat.pow_le_mono_l, H1. 
Qed. 

Instance mult_lt_le : Proper (eq ==> lt ==> le) mult. 
Proof. 
  intros a b -> d e H. nia. 
Qed.

Instance add_lt_lt : Proper (eq ==> lt ==> lt) Nat.add. 
Proof. 
  intros a b -> c d H. lia.
Qed.

Instance le_lt_impl : Proper (le --> eq ==> Basics.impl) lt. 
Proof. 
  intros a b H d e ->. unfold Basics.flip in H. unfold Basics.impl. lia. 
Qed.

Instance lt_le_impl : Proper (lt --> eq ==> Basics.impl) le. 
Proof. 
  intros a b H d e ->. unfold Basics.flip in H. unfold Basics.impl. lia.  
Qed.

Lemma list_el_size_bound {X : Type} `{registered X} (l : list X) (a : X) :
  a el l -> size(enc a) <= size(enc l). 
Proof. 
  intros H1. 
  rewrite size_list. 
  induction l. 
  - destruct H1.
  - cbn. destruct H1. rewrite H0; clear H0. solverec. rewrite IHl. 2: assumption. 
    solverec. 
Qed. 

Lemma list_app_size {X : Type} `{registered X} (l l' : list X) :
  size(enc (l ++ l')) + c__listsizeNil = size(enc l) + size(enc l').
Proof.
  repeat rewrite size_list. 
  rewrite map_app. rewrite sumn_app. lia. 
Qed. 

Lemma list_size_at_least {X : Type} `{registered X} (l : list X) : size(enc l) >= c__listsizeNil. 
Proof. rewrite size_list. lia. Qed.

Lemma list_app_size_l {X : Type} `{registered X} (l l' : list X) :
  size(enc (l ++ l')) >= size (enc l). 
Proof. 
  enough (size(enc (l++l')) + c__listsizeNil >= size(enc l) + c__listsizeNil) by lia. 
  rewrite list_app_size.  specialize list_size_at_least with (l:= l'). lia. 
Qed. 

Lemma list_app_size_r {X : Type} `{registered X} (l l' : list X) :
  size(enc (l ++ l')) >= size (enc l'). 
Proof. 
  enough (size(enc (l++l')) + c__listsizeNil >= size(enc l') + c__listsizeNil) by lia. 
  rewrite list_app_size.  specialize list_size_at_least with (l:= l). lia. 
Qed. 

Lemma list_subsequence_size_bound {X : Type} `{registered X} (l l': list X) :
  subsequence l l' -> size (enc l) <= size (enc l').
Proof. 
  intros (C & D & ->). 
  enough (size(enc l) <= size(enc (l++D))). 
  {
    rewrite H0. specialize list_app_size_r with (l:= C) (l' := l++D). lia. 
  }
  specialize list_app_size_l with (l:= l) (l':=D). lia. 
Qed. 

Lemma list_size_cons {X : Type} `{registered X} (l : list X) (a : X) : size(enc (a::l)) = size(enc a) + size(enc l) + c__listsizeCons.
Proof. repeat rewrite size_list. cbn.  lia. Qed. 

Lemma list_size_app (X : Type) (l1 l2 : list X) `{registered X} : size (enc (l1 ++ l2)) <= size (enc l1) + size (enc l2). 
Proof. 
  rewrite <- list_app_size. lia. 
Qed. 

Lemma list_size_concat (X : Type) (l : list (list X)) `{registered X} : size (enc (concat l)) <= size (enc l). 
Proof. 
  induction l; cbn; [easy | ]. 
  now rewrite list_size_app, list_size_cons, IHl. 
Qed. 

Lemma list_size_length {X : Type} `{registered X} (l : list X) : |l| <= size(enc l). 
Proof. 
  rewrite size_list. induction l.
  - cbn; lia. 
  - cbn. rewrite IHl. unfold c__listsizeCons; lia. 
Qed. 

Lemma list_size_enc_length {X : Type} `{registered X} (l : list X) : size (enc (|l|)) <= size (enc l). 
Proof. 
  rewrite size_list. rewrite size_nat_enc. unfold c__natsizeS, c__natsizeO, c__listsizeNil, c__listsizeCons. induction l; cbn; lia. 
Qed. 

Lemma list_size_of_el {X : Type} `{registered X} (l : list X) (k : nat) : (forall a, a el l -> size(enc a) <= k) -> size(enc l) <= (k * (|l|)) + c__listsizeCons * (|l|) +  c__listsizeNil . 
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

Lemma concat_time_exp (X : Type) (l : list (list X)): concat_time l = sumn (map (fun l' => c__concat * length l') l) + (|l| + 1) * c__concat. 
Proof. 
  induction l; cbn -[Nat.add Nat.mul]. 
  - lia.
  - unfold concat_time in IHl. rewrite IHl. lia. 
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

Tactic Notation "replace_le" constr(s) "with" constr(r) "by" tactic(tac) :=
  let H := fresh in assert (s <= r) as H by tac; rewrite !H; clear H. 
Tactic Notation "replace_le" constr(s) "with" constr(r) "by" tactic(tac) "at" ne_integer_list(occ) := 
  let H := fresh in assert (s <= r) as H by tac; rewrite H at occ; clear H. 
Tactic Notation "replace_le" constr(s) "with" constr(r) :=
  let H := fresh in assert (s <= r) as H; [ | rewrite !H; clear H]. 

Tactic Notation "poly_mono" constr(H) "at" integer(occ) :=
  let He := fresh in specialize H as He; match type of He with
                    | _ /\ monotonic _ => unfold monotonic in He; setoid_rewrite (proj2 He) at occ
                    | monotonic _ /\ _ => unfold monotonic in He; setoid_rewrite (proj1 He) at occ
                    end; clear He. 
Tactic Notation "poly_mono" constr(H) :=
  let He := fresh in specialize H as He; match type of He with
                    | _ /\ monotonic _ => unfold monotonic in He; erewrite (proj2 He)
                    | monotonic _ /\ _ => unfold monotonic in He; erewrite (proj1 He)
                    end; clear He. 


Lemma le_add_l n m : m <= n + m. 
Proof. lia. Qed. 

Definition c__moduloBound :=  c__divmod + c__modulo + c__sub.
Lemma modulo_time_bound x y: 
  modulo_time x y <= (size (enc x) + size (enc y) + 1) * c__moduloBound. 
Proof. 
  unfold modulo_time, divmod_time. rewrite size_nat_enc_r with (n := x) at 1. rewrite size_nat_enc_r with (n := y) at 1.
  unfold c__moduloBound. nia. 
Qed. 

Lemma leb_time_bound_l a b: leb_time a b <= (size(enc a) + 1) * c__leb. 
Proof. 
  unfold leb_time. rewrite Nat.le_min_l. rewrite size_nat_enc_r with (n := a) at 1. lia.
Qed. 

Lemma leb_time_bound_r a b : leb_time a b <= (size(enc b) + 1) * c__leb. 
Proof. 
  unfold leb_time. rewrite Nat.le_min_r. rewrite size_nat_enc_r with (n:= b) at 1. lia. 
Qed. 

Lemma forallb_time_exp (X : Type) (f : X -> nat) l: forallb_time f l = sumn (map (fun x => f x + c__forallb) l) + c__forallb. 
Proof. 
  unfold forallb_time; induction l; cbn; [lia | ].
  rewrite IHl. easy.
Qed. 

Section fixXEq. 
  Context {X : Type}.
  Context {H : registered X}.
  Context (Xeqb : X -> X -> bool). 
  Context {HXeq : eqbClass Xeqb}. 
  Context {HeqbComp : eqbCompT X}. 

  Definition poly__listInDecb n := (n + 1) * (c__listInDecb + 1 + c__eqbComp X).
  Lemma list_in_decb_time_bound (l : list X) e: list_in_decb_time l e <= poly__listInDecb (size (enc l)). 
  Proof. 
    induction l; cbn. 
    - unfold poly__listInDecb. nia. 
    - rewrite IHl. unfold eqbTime. 
      rewrite Nat.le_min_l. unfold poly__listInDecb. 
      rewrite list_size_cons. unfold c__listsizeCons; leq_crossout.
  Qed.
  Lemma list_in_decb_poly : monotonic poly__listInDecb /\ inOPoly poly__listInDecb. 
  Proof. 
    unfold poly__listInDecb; split; smpl_inO. 
  Qed. 

  Definition poly__listInclDecb n := n * poly__listInDecb n + (n + 1) * c__list_incl_decb.
  Lemma list_incl_decb_time_bound (l1 l2 :list X) : list_incl_decb_time l1 l2 <= poly__listInclDecb (size (enc l1) + size (enc l2)). 
  Proof.
    induction l1; cbn. 
    - unfold poly__listInclDecb. nia. 
    - rewrite list_in_decb_time_bound. rewrite IHl1. 
      poly_mono list_in_decb_poly. 2: { instantiate (1 := size (enc (a :: l1)) + size (enc l2)). lia. }
      unfold poly__listInclDecb. rewrite list_size_cons at 2 4. 
      poly_mono list_in_decb_poly at 2. 2 : { instantiate (1 := size (enc (a :: l1)) + size (enc l2)). rewrite list_size_cons. lia. }
      unfold c__listsizeCons. nia. 
  Qed. 
  Lemma list_incl_decb_poly : monotonic poly__listInclDecb /\ inOPoly poly__listInclDecb.       
  Proof. 
    unfold poly__listInclDecb; split; smpl_inO; apply list_in_decb_poly. 
  Qed. 

  Definition poly__dupfreeb n := n * poly__listInDecb n + (n + 1) * c__dupfreeb. 
  Lemma dupfreeb_time_bound (l : list X) : dupfreeb_time l <= poly__dupfreeb (size (enc l)). 
  Proof. 
    induction l; cbn. 
    - unfold poly__dupfreeb; nia. 
    - rewrite list_in_decb_time_bound. rewrite IHl. 
      poly_mono list_in_decb_poly. 2: { instantiate (1 := size (enc (a :: l))). rewrite list_size_cons. nia. }
      unfold poly__dupfreeb. 
      poly_mono list_in_decb_poly at 2. 2: { instantiate (1 := size (enc (a :: l))). rewrite list_size_cons. nia. }
      rewrite list_size_cons at 3 5. unfold c__listsizeCons. nia. 
  Qed. 
  Lemma dupfreeb_poly : monotonic poly__dupfreeb /\ inOPoly poly__dupfreeb. 
  Proof. 
    unfold poly__dupfreeb; split; smpl_inO; apply list_in_decb_poly. 
  Qed. 
End fixXEq. 

Section fixX.
  Context {X : Type}.
  Context {H : registered X}.

  (*Elements of type Y capture the environment of higher-order functions. This allows their argument functions to be non-closed, *)
  (* i.e. their running time depends on some values in their environment *)
  Variable (Y : Type).
  Context {RY : registered Y}.

  Lemma forallb_time_bound_env (predT : Y -> X -> nat) (f : nat -> nat):
    (forall (a : X) (y : Y), predT y a <= f (size(enc a) + size(enc y))) /\ monotonic f 
    -> forall (l : list X) (y : Y), forallb_time (predT y) l <= (|l| +1) * (f(size (enc l) + size(enc y)) + c__forallb). 
  Proof. 
    intros [H1 H2]. intros. induction l. 
    - cbn. lia.   
    - cbn. rewrite IHl, H1. unfold monotonic in H2. 
      rewrite H2 with (x' := size (enc (a :: l)) + size(enc y)). 2: rewrite list_size_cons; nia. 
      setoid_rewrite H2 with (x' := size(enc (a::l)) + size(enc y)) at 2. 2: rewrite list_size_cons; nia. 
      nia.
  Qed. 

  Lemma nth_error_time_bound : 
    forall (l : list X) n, nth_error_time l n <= (min (size (enc l)) (size (enc n)) + 1) * c__ntherror.
  Proof.
    intros. unfold nth_error_time. rewrite size_nat_enc_r with (n := n) at 1. rewrite list_size_length. nia.
  Qed. 

  Lemma map_time_bound_env (fT : Y -> X -> nat) (f__bound : nat -> nat): 
    (forall (env : Y) (ele : X), fT env ele <= f__bound (size (enc env) + size (enc ele))) /\ monotonic f__bound
    -> forall (env : Y) (l : list X), map_time (fT env) l <= (|l| + 1) * (f__bound (size (enc env) + size (enc l)) + 1) * (c__map + 1). 
  Proof. 
    intros [H1 H2] env l. induction l; cbn -[c__map]. 
    - nia. 
    - rewrite IHl. rewrite H1. unfold monotonic in H2. 
      rewrite H2 at 1. 2: (replace_le (size (enc a)) with (size (enc (a::l))) by (rewrite list_size_cons; lia)); reflexivity. 
      setoid_rewrite H2 at 2. 2: (replace_le (size (enc l)) with (size (enc (a::l))) by (rewrite list_size_cons; lia)); reflexivity. 
      nia. 
  Qed. 

  Definition poly__concat n := (n + 1) * c__concat.
  Lemma concat_time_bound (l : list (list X)) : concat_time l <= poly__concat (size (enc l)). 
  Proof. 
    unfold concat_time. induction l; cbn -[Nat.add Nat.mul].
    - unfold poly__concat. nia. 
    - rewrite IHl. unfold poly__concat. rewrite list_size_cons. rewrite list_size_length. unfold c__concat, c__listsizeCons; nia.
  Qed. 
  Lemma concat_poly : monotonic poly__concat /\ inOPoly poly__concat. 
  Proof. 
    split; unfold poly__concat; smpl_inO. 
  Qed. 
End fixX.

Section fixXY.
  Context {X Y Z: Type}.
  Context {H:registered X}.
  Context {H0: registered Y}.
  Context {H1 : registered Z}.

  Lemma fold_right_time_bound_env (step : Z -> Y -> X -> X) (stepT : Z -> Y -> X -> nat) (f__arg f__size : nat -> nat): 
    (forall (acc : X) (ele : Y) (env : Z), stepT env ele acc <= f__arg (size (enc acc) + size (enc ele) + size (enc env))) /\ monotonic f__arg
    -> (forall (acc : X) (ele : Y) (env : Z), size (enc (step env ele acc)) <= size (enc acc) + f__size (size (enc ele) + size (enc env))) /\ monotonic f__size
    -> forall (l : list Y) (acc : X) (env : Z), fold_right_time (step env) (stepT env) l acc <= (|l| + 1) * f__arg (|l| * f__size (size(enc l) + size (enc env)) + size (enc acc) + size(enc l) + size (enc env)) + (|l| + 1) * c__fold_right. 
  Proof. 
    intros [G1 G2] [F1 F2] l init env. 
    (*we first show that the output size of foldr on every suffix is bounded by |l| * fsize(size(enc l) + size(enc env)) + size(enc init) *)
    assert (forall l' l'', l = l' ++ l'' -> size (enc (fold_right (step env) init l'')) <= |l''| * f__size(size (enc l'') + size (enc env)) + size (enc init)) as H3. 
    { 
      intros l' l''. revert l'. induction l''; intros.
      - cbn. lia. 
      - cbn. rewrite F1. rewrite IHl''. 2: { now rewrite app_comm_cons' in H2. } 
        unfold monotonic in F2. setoid_rewrite F2 at 2. 
        2: (replace_le (size(enc a)) with (size (enc (a::l''))) by (apply list_el_size_bound; eauto)); reflexivity. 
        rewrite F2 at 1. 2: (replace_le (size (enc l'')) with (size (enc (a::l''))) by (rewrite list_size_cons; lia)); reflexivity. 
        nia. 
    } 

    induction l. 
    - cbn -[c__fold_right]. lia. 
    - cbn -[c__fold_right]. rewrite IHl. clear IHl.
      2: { intros. specialize (H3 (a::l') l''). apply H3. rewrite H2. eauto. } 
      rewrite G1. 
      unfold monotonic in *. erewrite G2. 
      2: { rewrite H3. 2: assert (a::l = [a] ++l) as -> by eauto; easy.
           erewrite F2. 2: (replace_le (size (enc l)) with (size (enc (a::l))) by (rewrite list_size_cons; lia)); reflexivity. 
           replace_le (size (enc a)) with (size (enc (a::l))) by (rewrite list_size_cons; lia). 
           instantiate (1 := (f__size (size (enc (a :: l)) + size (enc env)) + (| l |) * f__size (size (enc (a :: l)) + size (enc env)) + size (enc init) + size (enc (a :: l)) + size (enc env))). 
           nia. 
        } 
      setoid_rewrite G2 at 2. 
      2: { 
        instantiate (1 := (f__size (size (enc (a :: l)) + size (enc env)) + (| l |) * f__size (size (enc (a :: l)) + size (enc env)) + size (enc init) + size (enc (a :: l)) + size (enc env))).
        rewrite F2. 2: (replace_le (size(enc l)) with (size (enc (a::l))) by (rewrite list_size_cons; lia)); reflexivity. 
        replace_le (size (enc l)) with (size (enc (a::l))) by (rewrite list_size_cons; lia). lia.
      } 
      nia.
  Qed. 
End fixXY.

(** Facts we need to prove that a small assignment has an encoding size which is polynomial in the CNF's encoding size *)
Lemma list_dupfree_incl_length (X : eqType) (a b : list X) : a <<= b -> dupfree a -> |a| <= |b|. 
Proof. 
  intros H1 H2. eapply NoDup_incl_length. 
  - apply dupfree_Nodup, H2.
  - apply H1. 
Qed. 

Lemma rem_app_eq (X : eqType) (l1 l2 : list X) (x : X) : rem (l1 ++ l2) x = rem l1 x ++ rem l2 x. 
Proof. 
  induction l1; cbn; [easy | ].
  destruct Dec; cbn. 
  - fold (rem (l1 ++ l2) x). rewrite IHl1. easy.
  - fold (rem (l1 ++ l2) x). now rewrite IHl1. 
Qed. 

Lemma list_rem_size_le (X : eqType) `{H : registered X} (l : list X) x : size (enc (rem l x)) <= size (enc l). 
Proof. 
  induction l. 
  - cbn. lia. 
  - cbn. destruct Dec; cbn; rewrite !list_size_cons, IHl; lia. 
Qed. 

Lemma list_incl_dupfree_size (X : eqType) `{registered X} (a b : list X) : a <<= b -> dupfree a -> size (enc a) <= size (enc b). 
Proof. 
  intros H1 H2.  revert b H1.
  induction H2 as [ | a0 a H1 H2 IH]; intros. 
  - cbn. rewrite !size_list. cbn. lia.
  - specialize (IH (rem b a0)). 
    rewrite list_size_cons.
    cbn. rewrite IH. 
    2: { 
      assert (rem (a0 :: a) a0 = a).  
      { cbn. destruct Dec; [congruence | ]. cbn. 
       fold (rem a a0). now rewrite rem_id. 
      } 
      rewrite <- H3. now apply rem_mono. 
    } 
    specialize (H0 a0 (or_introl eq_refl)). apply In_explicit in H0 as (b1 & b2 & ->).
    rewrite !size_list, !rem_app_eq, !map_app, !sumn_app. cbn. 
    destruct Dec; cbn; [congruence | ]. 
    pose (elem_size := fun (x : X) => size (enc x) + c__listsizeCons). 
    fold elem_size.
    enough (sumn (map elem_size (rem b1 a0)) <= sumn (map elem_size b1) /\ sumn (map elem_size (rem b2 a0)) <= sumn (map elem_size b2)) as H0.
    { destruct H0 as [-> ->]. nia. }
    specialize (list_rem_size_le b1 a0) as F1. 
    specialize (list_rem_size_le b2 a0) as F2. 
    rewrite !size_list in F1. rewrite !size_list in F2. 
    fold elem_size in F1. fold elem_size in F2.
    split; nia. 
Qed. 
