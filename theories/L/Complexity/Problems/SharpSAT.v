From Undecidability.L.Complexity.Problems Require Export SharedSAT SAT.
Require Import Lia. 

From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Import  LProd LOptions LBool LLNat LLists LUnit.
From Undecidability.L.Functions Require Import EqBool. 
From Undecidability.L.Complexity Require Import PolyBounds MorePrelim SharpP. 

(** * #SAT *)
(** #SAT counts the number of satisfying assignments to a CNF *)
(** Of course, "equivalent" assignments shouldn't be counted twice if they are written down a bit differently. 
  Therefore, we define an equivalence relation on assignments (for a fixed CNF N): 
  a1 ≈ a2 := (a1 ⊧ N) <-> (a2 ⊧ N)
  This relation depends on the concrete CNF we are considering. For each equivalence class, we have a unique canonical representative a satisfying the following properties: 
  - assignment_small N a
  - assignment_ordered a, 
  where assignment_ordered a := ∀ v1 v2 ∈ a, getPosition a v1 <= getPosition a v2 <-> v1 <= v2.
  
  #SAT is defined to count the number of canonical satisfying assignments.
  *)

Section fixEqType. 
  Variable (X : Type). 
  Variable (eqX : X -> X -> bool). 

  Fixpoint getPosition (l : list X) (x : X) := match l with 
    | [] => 0 
    | (h :: l) => if eqX h x then 0 else S (getPosition l x)
  end.  

  Lemma getPosition_le l x: getPosition l x <= |l|. 
  Proof. 
    induction l; cbn; [lia | ]. 
    destruct eqX; lia. 
  Qed.
End fixEqType. 

Definition assignment_ordered (a : assgn) := forall v1 v2, v1 el a -> v2 el a -> (v1 <= v2 <-> getPosition Nat.eqb a v1 <= getPosition Nat.eqb a v2). 
Definition assignment_canonical (N : cnf) (a : assgn) := assignment_small N a /\ assignment_ordered a. 


(** We now build a verifier that accepts only canonical assignments *)
Definition verifier (N : cnf) (a : assgn) := satisfies a N /\ assignment_canonical N a. 

Definition order_respectful_decb (l : list nat) (p : nat * nat) := let (x1, x2) := p in 
  Bool.eqb (leb x1 x2) (leb (getPosition Nat.eqb l x1) (getPosition Nat.eqb l x2)). 

Lemma bool_equiv_reflect p1 p2 (a b : bool): reflect p1 a -> reflect p2 b -> reflect (p1 <-> p2) (Bool.eqb a b).
Proof. 
  intros H1%reflect_iff H2%reflect_iff. apply iff_reflect. 
  rewrite H1, H2. destruct a, b; cbn; firstorder.
Qed.

Lemma order_respectful_decb_spec l x1 x2 : reflect (x1 <= x2 <-> getPosition Nat.eqb l x1 <= getPosition Nat.eqb l x2) (order_respectful_decb l (x1, x2)). 
Proof. 
  apply bool_equiv_reflect. 
  - apply Nat.leb_spec0. 
  - apply Nat.leb_spec0. 
Qed.

Definition assignment_ordered_decb (a : assgn) := forallb (order_respectful_decb a) (list_prod a a). 

Lemma forallb_spec (X : Type) (l : list X) (p : X -> Prop) pb : (forall x, reflect (p x) (pb x)) -> reflect (forall x, x el l -> p x) (forallb pb l).
Proof.
  intros H. apply iff_reflect. rewrite forallb_forall. now setoid_rewrite (reflect_iff _ _ (H _)). 
Qed.

Lemma assignment_ordered_decb_spec a : reflect (assignment_ordered a) (assignment_ordered_decb a). 
Proof. 
  unfold assignment_ordered, assignment_ordered_decb. 
  eapply ssrbool.equivP. 
  - eapply forallb_spec. intros (x1 & x2). 
    instantiate (1 := fun '(x1, x2) => x1 <= x2 <-> getPosition Nat.eqb a x1 <= getPosition Nat.eqb a x2). 
    cbn -[order_respectful_decb]. eapply order_respectful_decb_spec. 
  - split. 
    + intros H v1 v2 Hel1 Hel2. specialize (H (v1, v2) ). cbn in H. apply H. now apply in_prod_iff.
    + intros H (v1 & v2) (Hel1 & Hel2)%in_prod_iff. now apply H. 
Qed. 

Definition assignment_canonical_decb (N : cnf) (a : assgn) := assignment_small_decb N a && assignment_ordered_decb a. 

Lemma assignment_canonical_decb_spec N a : reflect (assignment_canonical N a) (assignment_canonical_decb N a). 
Proof. 
  unfold assignment_canonical, assignment_canonical_decb. 
  apply iff_reflect. rewrite andb_true_iff. 
  rewrite (reflect_iff _ _ (assignment_ordered_decb_spec a)). now rewrite assignment_small_decb_iff. 
Qed.

Definition verifier_bool N a := evalCnf a N && assignment_canonical_decb N a. 

Lemma verifier_bool_spec N a : reflect (verifier N a) (verifier_bool N a). 
Proof. 
  apply iff_reflect. unfold verifier_bool, verifier. 
  rewrite andb_true_iff. unfold satisfies. 
  rewrite (reflect_iff _ _ (assignment_canonical_decb_spec N a)). easy.
Qed.

(** Definition of #SAT *)
Definition SharpSATP (N : cnf) := cardOf (fun a => satisfies a N /\ assignment_canonical N a). 
(* TODO: this is somewhat ugly : we have to define the function computing the number of assignments explicitly, i.e. enumerate canonical assignments.. *)

Fixpoint all_subsequences (X : Type) (l : list X) := match l with 
    | [] => [[]]
    | (x :: l) => (map (fun l => x :: l) (all_subsequences l)) ++ all_subsequences l 
    end. 

Inductive isSubsequence (X : Type) : list X -> list X -> Prop := 
  | isSubsequenceB : isSubsequence [] []
  | isSubsequenceS1 l' s' a : isSubsequence l' s' -> isSubsequence (a :: l') (a :: s') 
  | isSubsequenceS2 l' s' a : isSubsequence l' s' -> isSubsequence (a :: l') s'. 
Hint Constructors isSubsequence.

Lemma all_subsequences_isSubsequence (X : Type) (l : list X) : forall s, s el all_subsequences l <-> isSubsequence l s. 
Proof. 
  split.
  - revert s; induction l; cbn; intros s H.
    + destruct H as [<- | []]; auto.
    + apply in_app_iff in H. rewrite in_map_iff in H.
      destruct H as [(x & <- & H) | H]. 
      * constructor. now apply IHl. 
      * constructor 3. now apply IHl. 
  - induction 1. 
    + cbn. eauto.
    + cbn. apply in_app_iff. left. apply in_map_iff. eauto.
    + cbn. apply in_app_iff. right. eauto.
Qed.

(** the assignment from which we start taking subsequences *)
Definition baseAssgn (N : cnf) :=
  let vars := varsOfCnf N in 
  filter (list_in_decb Nat.eqb vars) (seq 0 (cnf_maxVar N)). 

Definition allCanonical (N : cnf) := all_subsequences (baseAssgn N).
Definition allSatisfyingCanonical (N : cnf) := filter (fun a => evalCnf a N) (allCanonical N). 

Lemma dupfree_seq a b : dupfree (seq a b).  
Proof. 
  revert a. induction b; cbn; intros; constructor.
  - intros (H1 & H2)%in_seq. lia. 
  - apply IHb. 
Qed.

Lemma baseAssgn_canonical N : assignment_canonical N (baseAssgn N).
Proof. 
  split. 
  - unfold assignment_small. split. 
    + unfold baseAssgn. intros v Hel. 
      apply in_filter_iff in Hel as (H1 & H2). 
      apply list_in_decb_iff in H2; [ | symmetry; apply Nat.eqb_eq]. 
      easy.
    + unfold baseAssgn. apply dupfree_filter, dupfree_seq. 
  - unfold assignment_ordered. intros v1 v2. 
    unfold baseAssgn. rewrite !in_filter_iff, !in_seq, !list_in_decb_iff. 
    2, 3: symmetry; apply Nat.eqb_eq. 
    intros ((_ & H1) & H2)  ((_ & H3) & H4). 



(* ... *)

(*[> a better way might be to inject into term and only enumerate terms; + establish a bound on the encoding size <]*)
(*Axiom (PI : forall (X : Prop), forall (x1 x2 : X), x1 = x2). *)

(*Definition dep_map (X Y : Type) (l : list X) (f : forall x, x el l -> Y) : list Y. *)
(*Proof. *)
  (*induction l. *)
  (*- exact []. *)
  (*- specialize (IHl ltac:(easy)). exact (f a ltac:(now left) :: IHl). *)
(*Defined.*)

(*[>Lemma in_dep_map_iff (X Y : Type) (l : list X) (f : forall x, x el l -> Y) : forall y, y el dep_map f <-> exists x (Hx : x el l), y = f x Hx. <]*)
(*[>Proof. <]*)
  (*[>intros y. induction l. <]*)
  (*[>- cbn. split; [intros [] | intros (x & [] & _)]. <]*)
  (*[>- unfold dep_map. rewrite (IHl (fun x Hel => f x ltac:(easy))). <]*)

(*Check Prelim.Injective. *)
(*Print bijective. *)

(*Lemma bijection_cardOf_imp (X Y : eqType) (pX : X -> Prop) (pY : Y -> Prop) (f : {x : X | pX x} -> {y : Y | pY y}) (fInv : { y : Y | pY y} -> {x : X | pX x}): *)
  (*inverse f fInv -> forall n, cardOf pX n -> cardOf pY n.*)
(*Proof. *)
  (*intros H n. unfold cardOf, listOf. intros (l & [H1  H2] & H3).*)
  (*revert l H1 H2 H3. *)
  (*enough (forall l1 l2, dupfree (l1 ++ l2) -> (forall x : X, pX x /\ not (x el l1) <-> x el l2) -> n = (|l1|) + (|l2|) -> exists (l1' l2' : list Y), (dupfree (l1' ++ l2') /\ (forall y : Y, pY y /\ (not (y el l1')) <-> y el l2') /\ n = (|l1'|) + (|l2'|))) as H0. *)
  (*{ intros l H1 H2 H3. specialize (H0 [] l). edestruct H0 as (l1' & l2' & F1 & F2 & F3). *)
    (*- cbn. apply H1. *)
    (*- intros x. rewrite <- H2. easy.*)
    (*- cbn. apply H3. *)
    (*- exists (l1' ++ l2'). repeat split. *)
      (*+ apply F1. *)
      (*+ intros Hy. rewrite in_app_iff. destruct (List.in_dec (@eqType_dec Y) x l1') as [Hel | Hnel]. *)
        (** now left. *)
        (** right; now apply F2. *)
      (*+ intros [Hel | Hel]%in_app_iff; *)
  (*assert (forall x : X, pX x /\ not (x el []) <-> x el l*)
  (*exists (fun *)



  (*assert (exists (f' : {x : X | x el l} -> {y : Y | pY y}) (fInv' : {y : Y | pY y} -> {x : X| x el l}), inverse f' fInv') as (f' & fInv' & Hinv). *)
  (*{ eexists (fun x => match x with exist _ x Hx => f (exist pX x (proj2 (H2 x) Hx)) end).*)
    (*eexists (fun y => match fInv y with exist _ x Hx => exist _ x (proj1 (H2 x) Hx) end). *)
    (*destruct H as (Hinv1 & Hinv2). *)
    (*split; unfold left_inverse, right_inverse. *)
    (*- intros (x & Hx). destruct fInv as (x' & Hx') eqn:Heq1. *)
      (*unfold left_inverse in Hinv1. rewrite Hinv1 in Heq1. *)
      (*assert (x' = x) by congruence. *)
      (*inv Heq1. now rewrite (PI (proj1 (H2 x) Hx') (Hx)). *)
    (*- intros (y & Hy). destruct fInv as (x & Hx) eqn:Heq1. *)
      (*rewrite (PI (proj2 (H2 x) (proj1 (H2 x) Hx)) (Hx)). *)
      (*change (fun x => pX x) with pX in Heq1. rewrite <- Heq1. *)
      (*unfold right_inverse in Hinv2. now rewrite Hinv2. *)
  (*} *)
  (*clear f fInv H H2 pX. *)
  (*revert n H3. *)
  (*induction l; intros. *)
  (*- exists []. repeat split.*)
    (*+ eauto.*)
    (*+ intros Hy. destruct (fInv' (exist pY x Hy)). easy.  *)
    (*+ intros []. *)
    (*+ easy.*)
  (*- edestruct IHl. *)
    (*+ now inv H1. *)
    (*+ apply Hinv. *)


(** extraction *)
Section fixEqTypegetp. 
  Variable (X : Type). 
  Variable (eqX : X -> X -> bool). 
  Context (Heqb : eqbClass eqX). 
  Context `{registered X}. 
  Context (Heqbcomp : eqbCompT X).

  Definition c__getPosition := 20.
  Definition getPosition_time (l : list X) (x : X):= (|l| + 1) * (size (enc x)) * c__eqbComp X + c__getPosition * (|l| + 1).
  Global Instance term_getPosition : computableTime' (@getPosition X eqX) (fun l _ => (5, fun x _ => (getPosition_time l x, tt))). 
  Proof. 
    extract. solverec. all: unfold getPosition_time.   
    - unfold c__getPosition; cbn; lia. 
    - rewrite eqbTime_le_r. cbn. unfold c__getPosition. nia. 
    - rewrite eqbTime_le_r. cbn. unfold c__getPosition. nia. 
  Qed.

  Definition poly__getPosition n := (n + 1) * n * c__eqbComp X + c__getPosition * (n + 1). 
  Lemma getPosition_time_bound l x: getPosition_time l x <= poly__getPosition (size (enc l) + size (enc x)). 
  Proof. 
    unfold getPosition_time. rewrite list_size_length.
    unfold poly__getPosition. leq_crossout. 
  Qed. 
  Lemma getPosition_poly : monotonic poly__getPosition /\ inOPoly poly__getPosition. 
  Proof. 
    unfold poly__getPosition; split; smpl_inO. 
  Qed.
End fixEqTypegetp. 

(** order_respectful_decb *) 
Definition c__orderRespectful := 2 * c__leb2 + c__eqbBool + 16. 
Definition order_respectful_decb_time (l : list nat) (p : nat * nat) := 
  let (x, y) := p in 
  leb_time x y + getPosition_time LNat.eqbComp_nat l x + getPosition_time LNat.eqbComp_nat l y + leb_time (getPosition Nat.eqb l x) (getPosition Nat.eqb l y) + c__orderRespectful.
Instance term_order_respectful_decb : computableTime' order_respectful_decb (fun l _ => (1, fun p _ => (order_respectful_decb_time l p, tt))). 
Proof. 
  unfold order_respectful_decb. 
  extract. solverec. 
  unfold c__orderRespectful. nia. 
Qed.
  
Definition poly__orderRespectful n := (n + 1) * c__leb * 2 + 2 * poly__getPosition LNat.eqbComp_nat n + c__orderRespectful. 
Lemma order_respectful_decb_time_bound l p : order_respectful_decb_time l p <= poly__orderRespectful (size (enc l) + size (enc p)). 
Proof. 
  unfold order_respectful_decb_time. destruct p as (x & y). 
  rewrite !getPosition_time_bound. 
  poly_mono (getPosition_poly (X := nat) _) at 1. 2 : instantiate (1 := size (enc l) + size (enc (x, y))); rewrite size_prod; cbn; lia. 
  poly_mono (getPosition_poly (X := nat) _) at 2. 2 : instantiate (1 := size (enc l) + size (enc (x, y))); rewrite size_prod; cbn; lia. 
  rewrite !leb_time_bound_l. 
  setoid_rewrite nat_size_le at 2. 2: apply getPosition_le. 
  rewrite list_size_enc_length.
  replace_le (size (enc x)) with (size (enc (x, y))) by (rewrite size_prod; cbn; lia) at 1. 
  unfold poly__orderRespectful. nia.  
Qed.
Lemma order_respectful_decb_poly : monotonic poly__orderRespectful /\ inOPoly poly__orderRespectful. 
Proof. 
  unfold poly__orderRespectful; split; smpl_inO; apply getPosition_poly. 
Qed.

(** assignment_ordered_decb *)
Definition c__assignmentOrdered := 8. 
Definition assignment_ordered_decb_time (a : assgn) :=  prodLists_time a a + forallb_time (order_respectful_decb_time a) (list_prod a a) + c__assignmentOrdered.
Instance term_assignment_ordered_decb : computableTime' assignment_ordered_decb (fun a _ => (assignment_ordered_decb_time a, tt)). 
Proof.
  extract. solverec.  
  unfold assignment_ordered_decb_time, c__assignmentOrdered. nia. 
Qed.

Definition poly__assignmentOrdered n :=
  poly__prodLists (2 * n) + n * n * (poly__orderRespectful (n * 3 + 4) + c__forallb) + c__forallb + c__assignmentOrdered.
Lemma assignment_ordered_decb_time_bound a: assignment_ordered_decb_time a <= poly__assignmentOrdered (size (enc a)). 
Proof. 
  unfold assignment_ordered_decb_time. 
  rewrite prodLists_time_bound.
  instantiate (1 := LNat.registered_nat_enc).
  instantiate (1 := LNat.registered_nat_enc).
  rewrite forallb_time_exp, sumn_map_mono. 
  2: { intros (x1 & x2) (Hel1 & Hel2)%in_prod_iff. 
    instantiate (1 := fun _ => _). cbn -[order_respectful_decb_time].
    rewrite order_respectful_decb_time_bound. 
    poly_mono order_respectful_decb_poly. 
    2: { rewrite size_prod. cbn. setoid_rewrite list_el_size_bound at 2; [ | apply Hel1]. 
      setoid_rewrite list_el_size_bound at 3; [ | apply Hel2]. 
      instantiate (1 := size (enc a) * 3 + 4). lia. 
    } 
    reflexivity. 
  } 
  rewrite sumn_map_const. rewrite prod_length, list_size_length.
  unfold poly__assignmentOrdered. cbn [Nat.mul]. rewrite Nat.add_0_r.
  nia.  
Qed.
Lemma assignment_ordered_decb_poly : monotonic poly__assignmentOrdered /\ inOPoly poly__assignmentOrdered. 
Proof. 
  unfold poly__assignmentOrdered; split; smpl_inO; try apply inOPoly_comp; smpl_inO. 
  all: first[apply prodLists_poly | apply order_respectful_decb_poly]. 
Qed.

(** verifier_bool *)
Definition c__verifierBool := 17.
Definition verifier_bool_time (N : cnf) (a : assgn) := evalCnf_time a N + assignment_small_decb_time N a + assignment_ordered_decb_time a + c__verifierBool.
Instance term_verifier_bool : computableTime' verifier_bool (fun N _ => (1, fun a _ => (verifier_bool_time N a, tt))). 
Proof. 
  unfold verifier_bool, assignment_canonical_decb. 
  extract. solverec. 
  unfold verifier_bool_time, c__verifierBool; solverec. 
Qed.

Definition poly__verifierBool n := poly__evalCnf n + poly__assignmentSmallDecb n + poly__assignmentOrdered n + c__verifierBool.
Lemma verifier_bool_time_bound N a: verifier_bool_time N a <= poly__verifierBool (size (enc N) + size (enc a)). 
Proof. 
  unfold verifier_bool_time. rewrite evalCnf_time_bound.
  rewrite assignment_small_decb_time_bound. rewrite assignment_ordered_decb_time_bound. 
  setoid_rewrite Nat.add_comm with (n := size (enc a)) at 1. 
  poly_mono assignment_ordered_decb_poly. 2: { instantiate (1 := size (enc N) +size (enc a)). lia. }
  unfold poly__verifierBool. lia. 
Qed.
Lemma verifier_bool_poly : monotonic poly__verifierBool /\ inOPoly poly__verifierBool. 
Proof. 
  unfold poly__verifierBool; split; smpl_inO. 
  all: first [apply evalCnf_poly | apply assignment_small_decb_poly | apply assignment_ordered_decb_poly ]. 
Qed.


(** #P inclusion *)
Lemma SharpSAT_in_SharpP : inSharpP (unrestrictedF SharpSAT). 
Proof. 
