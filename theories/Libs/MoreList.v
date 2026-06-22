From Undecidability.Shared Require Import Libs.PSL.Base.
Require Import Lia Arith.

#[export] Hint Resolve in_eq in_nil in_cons in_or_app : core.
#[export] Hint Resolve incl_refl incl_tl incl_cons incl_appl incl_appr incl_app incl_nil_l : core.

#[export] Hint Rewrite <- app_assoc : list.
#[export] Hint Rewrite rev_app_distr map_app prod_length : list.

(* Injectivity of [map], if the function is injective *)
Lemma map_injective (X Y: Type) (f: X -> Y) :
  (forall x y, f x = f y -> x = y) ->
  forall xs ys, map f xs = map f ys -> xs = ys.
Proof.
  intros HInj. hnf. intros x1. induction x1 as [ | x x1' IH]; cbn in *.
  - now intros [|??].
  - intros [|??]; [easy|]. intros [= E1%HInj E2%IH]. now subst.
Qed.

(* allows rewriting under binder of map *)
#[export]
Instance map_ext_proper A B: Proper (@ pointwise_relation A B (@eq B) ==> (@eq (list A)) ==> (@eq (list B))) (@map A B).
Proof.
  intros f f' Hf a ? <-. induction a;cbn;congruence.
Qed.

Lemma app_comm_cons' (A : Type) (x y : list A) (a : A) :
  x ++ a :: y = (x ++ [a]) ++ y.
Proof. rewrite <- app_assoc. cbn. trivial. Qed.

(* Nats smaller than n *)

Fixpoint natsLess n : list nat :=
  match n with
    0 => []
  | S n => n :: natsLess n
  end.

Lemma natsLess_in_iff n m:
  n el natsLess m <-> n < m.
Proof.
  induction m in n|-*;cbn. lia.
  split.
  -intuition. destruct n; intuition lia. apply IHm in H0. lia.
  -intros. decide (m=n). intuition lia. right. apply IHm. lia.
Qed.


Lemma natsLess_S n :
  natsLess (S n) = map S (natsLess n)++[0].
Proof.
  induction n;cbn in *;congruence.
Qed.


(* Sum *)

Fixpoint sumn (A:list nat) :=
  match A with
    [] => 0
  | a::A => a + sumn A
  end.

Lemma sumn_app A B : sumn (A++B) = sumn A + sumn B.
Proof.
  induction A;cbn;lia.
Qed.

#[export] Hint Rewrite sumn_app : list. 

Lemma length_concat X (A : list (list X)) :
  length (concat A) = sumn (map (@length _) A).
Proof.
  induction A;cbn. reflexivity. autorewrite with list in *. lia.
Qed.

Lemma sumn_rev A :
  sumn A = sumn (rev A).
Proof.
  enough (H:forall B, sumn A + sumn B = sumn (rev A++B)).
  {specialize (H []). cbn in H. autorewrite with list in H. cbn in H. lia. }
  induction A as [|a A];intros B. reflexivity.
  cbn in *. specialize (IHA (a::B)). autorewrite with list in *. cbn in *. lia.
Qed.

Lemma sumn_map_natsLess f n :
  sumn (map f (natsLess n)) = sumn (map (fun i => f (n - (1 + i))) (natsLess n)).
Proof.
  rewrite sumn_rev. f_equal.
  rewrite <- map_rev.
  rewrite <- map_map with (g:=f) (f:= fun i => (n - (1+i))).
  f_equal.
  induction n;intros;autorewrite with list in *. reflexivity.
  rewrite natsLess_S at 2. cbn. rewrite map_app. cbn.
  rewrite map_map. cbn in IHn.
  rewrite IHn. rewrite Nat.sub_0_r. reflexivity.
Qed.


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

Lemma sumn_le_in n xs: n el xs -> n <= sumn xs.
Proof.
  induction xs. easy. intros [ | ]. now cbn;nia.
  cbn;etransitivity. apply IHxs. easy. nia.
Qed.

Lemma sumn_concat xs: sumn (concat xs) = sumn (map sumn xs).
Proof.
  induction xs;cbn. easy. etransitivity. apply sumn_app. nia.
Qed.


Lemma sumn_repeat c n: sumn (repeat c n) = c * n.
Proof.
  induction n;cbn. all:nia.
Qed.

Definition maxl := fold_right max 0.
Lemma maxl_leq n l: n el l -> n <= maxl l.
Proof.
  induction l;cbn.
  -easy.
  -intros [->|]. all:apply Nat.max_case_strong;try intuition Lia.lia.
Qed.

Lemma maxl_leq_l c l :
  (forall n, n el l -> n <= c) -> maxl l <= c.
Proof.
  induction l;cbn. Lia.lia. 
  intros H. eapply Nat.max_lub_iff;split. all:eauto.  
Qed.

Lemma maxl_app l l': maxl (l++l') = max (maxl l) (maxl l').
Proof.
  induction l;cbn;Lia.lia.
Qed.

Lemma maxl_rev l: maxl (rev l) = maxl l.
Proof.
  unfold maxl. rewrite fold_left_rev_right. rewrite fold_symmetric. 2,3:now intros;Lia.lia.
  induction l;cbn;try Lia.lia.
Qed.

(* TODO: is there a better place for these lemmas? *)
Lemma Dec_true P {H : dec P} : dec2bool (Dec P) = true -> P.
Proof.
  decide P; easy.
Qed.

Lemma Dec_false P {H : dec P} : dec2bool (Dec P) = false -> ~P.
Proof.
  decide P; easy.
Qed.

Lemma Dec_true' (P : Prop) (d : dec P) : P -> dec2bool (Dec P) = true.
Proof. intros H. decide P; cbn; tauto. Qed.

Lemma Dec_false' (P : Prop) (d : dec P) : (~ P) -> dec2bool (Dec P) = false.
Proof. intros H. decide P; cbn; tauto. Qed.

#[export] Hint Extern 4 =>
match goal with
  [ H : dec2bool (Dec ?P) = true  |- _ ] => apply Dec_true in  H
| [ H : dec2bool (Dec ?P) = false |- _ ] => apply Dec_false in H
| [ |- dec2bool (Dec ?P) = true] => apply Dec_true'
| [ |- dec2bool (Dec ?P) = false] => apply Dec_false'
end : core.

#[export]
Instance list_exists_dec X A (p : X -> Prop) :
  (forall x, dec (p x)) -> dec (exists x, x el A /\ p x).
Proof.
  intros p_dec.
  destruct (find (fun x => Dec (p x)) A) eqn:Eq. (* New: eta expansion needed *)
  - apply find_some in Eq as [H0 H1]. firstorder. (* New: Need firstorder here *)
  - right. intros [x [E F]]. apply find_none with (x := x) in Eq; auto. eauto. (* New: Why can't auto solve this? *)
Qed.

Lemma cfind X A (p: X -> Prop) (p_dec: forall x, dec (p x)) :
  {x | x el A /\ p x} + {forall x, x el A -> ~ p x}.
Proof.
  destruct (find (fun x => Dec (p x)) A) eqn:E.
  - apply find_some in E. firstorder.
  - right. intros. eapply find_none in E; eauto.
Qed.

Arguments cfind {X} A p {p_dec}.
Lemma list_cc X (p : X -> Prop) A : 
  (forall x, dec (p x)) -> 
  (exists x, x el A /\ p x) -> {x | x el A /\ p x}.
Proof.
  intros D E. 
  destruct (cfind A p) as [[x [F G]]|F].
  - eauto.
  - exfalso. destruct E as [x [G H]]. apply (F x); auto.
Qed.

(* ** Lemmas about [hd], [tl] and [removelast] *)

Lemma tl_map (A B: Type) (f: A -> B) (xs : list A) :
  tl (map f xs) = map f (tl xs).
Proof. now destruct xs; cbn. Qed.

(* Analogous to [removelast_app] *)
Lemma tl_app (A: Type) (xs ys : list A) :
  xs <> nil ->
  tl (xs ++ ys) = tl xs ++ ys.
Proof. destruct xs; cbn; congruence. Qed.

Lemma tl_rev (A: Type) (xs : list A) :
  tl (rev xs) = rev (removelast xs).
Proof.
  induction xs; cbn; auto.
  destruct xs; cbn in *; auto.
  rewrite tl_app; cbn in *.
  - now rewrite IHxs.
  - intros (H1&H2) % app_eq_nil; inv H2.
Qed.
