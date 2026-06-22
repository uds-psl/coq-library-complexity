From Undecidability.L Require Export Computability.Seval.
From Complexity.Libs Require Import MoreList.
From Complexity.L Require Import ComputableTime.
Import L_Notations.

(* Utilities for reconstructing, given [eval s t] (in Prop), a reduction
 * path from [s] to [t], but in Type.
 *)

Require Import Coq.Logic.ConstructiveEpsilon.
Definition cChoice := constructive_indefinite_ground_description_nat_Acc.

Fixpoint stepf (s : term) : list term :=
  match s with
  | (lam _) => []
  | var x => []
  | app (lam s) (lam t) => [subst s 0 (lam t)]
  | app s t => map (fun x => app x t) (stepf s) ++ map (fun x => app s x) (stepf t)
  end.

Ltac stepf_tac := 
  match goal with
  | [ H : app _ _ ≻ ?t |- ?P ] => inv H
  | [ H : var _ ≻ ?t |- ?P ] => inv H
  | [ H : lam _ ≻ ?t |- ?P ] => inv H

  | [ H : exists x, _ |- _ ] => destruct H
  | [ H : _ /\ _ |- _ ] => destruct H
  end + subst.

Lemma stepf_spec s t : t el stepf s <-> s ≻ t.
Proof.
  revert t; induction s; intros; try now (firstorder; inv H). cbn.
  destruct s1, s2.
  all:cbn - [stepf].
  all:try rewrite !in_app_iff;try rewrite !in_map_iff.
  1-8:setoid_rewrite IHs1.
  1-8:try setoid_rewrite IHs2.
  all:intuition idtac.
  all:repeat stepf_tac.
  all:eauto using step.
Qed.

Fixpoint stepn (n : nat) s : list term :=
  match n with
  | 0 => [s]
  |  S n => flat_map (stepn n) (stepf s)
  end.

Lemma stepn_spec n s t : t el stepn n s <-> s >(n) t.
Proof.
  revert s t; induction n; intros.
  - cbn. firstorder.
  - cbn. rewrite in_flat_map. firstorder; exists x; firstorder using stepf_spec.
Qed.         
  
Lemma informative_eval s t: eval s t -> {l | s >(l) t}.
Proof.
  intros H. destruct H. eapply star_pow in H. apply cChoice; eauto.
  intros. eapply dec_transfer.
  eapply stepn_spec. exact _.
Qed.

Lemma informative_eval2 s : (exists t, eval s t) -> {t | eval s t}.
Proof.
  intros H.
  edestruct cChoice with (P:=fun n => exists t, t el stepn n s /\ lambda t).
  -intros.
   decide (exists t, t el stepn n s /\ lambda t). all:eauto.
  -destruct H as (?&H&?). eapply star_pow in H as [? H].
   eapply stepn_spec in H. eauto.
  -apply list_cc in e. 2: intros; exact _.
   destruct e as (?&H'&?). unfold eval. apply stepn_spec,pow_star in H'. eauto.
Qed.

Lemma informative_seval s t: eval s t -> {l | seval l s t}.
Proof.
  intros H%eval_seval.
  eapply cChoice. 2:easy.
  intro. eapply dec_transfer. now rewrite <- eva_seval_iff.
  exact _.
Qed. 

Lemma informative_seval2 s: (exists t, eval s t) -> {t & {l | seval l s t}}.
Proof.
  intros (?&?)%informative_eval2. eexists. eapply informative_seval. eauto.
Qed. 


Lemma informative_evalIn s t: eval s t -> {l | s ⇓(l) t}.
Proof.
  intros H'. specialize (informative_eval H') as (l&H).
  destruct H'. firstorder.
Qed.

Lemma seval_rect (P : nat -> term -> term -> Type)
  (HR : forall (n : nat) (s : term), P n (lam s) (lam s))
  (HS : forall (n : nat) (s t u v w : term),
      seval n s (lam u) ->
        P n s (lam u) ->
        seval n t (lam v) ->
        P n t (lam v) ->
        seval n (subst u 0 (lam v)) w ->
        P n (subst u 0 (lam v)) w -> P (S n) (s t) w):
  forall n s t, seval n s t -> P n s t.
Proof.
  intros n. induction n as [n IHn]using lt_wf_rect.
  intros s t H'.
  eapply seval_eva in H'. destruct n.
  { cbn in H'. destruct s;inv H'. easy. }
  cbn in H'. destruct s. 1,3:now inv H'.
  destruct eva eqn:H1. 2:easy.
  destruct t0. 1,2:easy.
  destruct eva eqn:H2 in H'. 2:easy.
  specialize (eva_lam H2) as H''.
  destruct t1. 1,2:now exfalso;inversion H''. clear H''.
  specialize (eva_lam H') as H''.
  destruct t. 1,2:now exfalso;inversion H''.
  eapply HS. all:eauto using eva_seval.
Qed.


Lemma eval_rect (P : term -> term -> Type) (HR : forall s : term, P (lam s) (lam s))
(HS : forall s u t t' v : term,
    eval s (lam u) ->
      P s (lam u) ->
      eval t t' ->
      P t t' -> eval (subst u 0 t') v -> P (subst u 0 t') v -> P (s t) v):
  forall s t : term, eval s t -> P s t.
Proof.
  intros ? ? H. 
  eapply informative_seval in H as (?&H).
  induction H using seval_rect. easy.
  eapply HS. all:  eauto.
Qed.
