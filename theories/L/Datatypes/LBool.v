From Undecidability.L.Datatypes Require Export LBool.
From Complexity.L Require Export ComputableTime.
From Complexity.L Require Import Functions.EqBool.

#[global]
Instance termT_negb : computableTime' negb (fun _ _ => (4,tt)).
Proof.
  extract. solverec.
Qed.

#[global]
Instance termT_andb : computableTime' andb (fun _ _ => (1,fun _ _ => (4,tt))).
Proof.
  extract. solverec.
Qed.

#[global]
Instance termT_orb : computableTime' orb (fun _ _ => (1,fun _ _ => (4,tt))).
Proof.
  extract. solverec.
Qed.

Definition c__sizeBool := 4.
Lemma size_bool (b : bool) : size(enc b) <= c__sizeBool. 
Proof.  destruct b; cbv; lia. Qed. 

Lemma size_bool_enc (b:bool): size (enc b) = if b then 4 else 3.
Proof.
  now destruct b;cbv.
Qed.

Definition OmegaLift := lam Omega.

Lemma OmegaLift_proc : proc OmegaLift.
Proof.  unfold OmegaLift.  Lproc. Qed.
#[export] Hint Resolve OmegaLift_proc : LProc.

Import L_Notations.

Definition trueOrDiverge := lam (var 0 I OmegaLift I).

Lemma trueOrDiverge_proc : proc trueOrDiverge.
Proof.  unfold trueOrDiverge. Lproc. Qed.
#[export] Hint Resolve trueOrDiverge_proc : LProc.

Lemma trueOrDiverge_true : trueOrDiverge (enc true) >(4) I.
Proof.
  unfold trueOrDiverge. cbv - [pow]. Lsimpl.
Qed.

#[export] Hint Resolve trueOrDiverge_true : Lrewrite.

Lemma Omega_diverge t: ~ eval Omega t.
Proof.
  intros (?&?). remember Omega as s eqn:HO. induction H;subst.
  -inv H0. easy.
  -unfold Omega in H. inv H. cbn in *. eauto. all:easy.
Qed.

Lemma trueOrDiverge_eval t b: trueOrDiverge (enc b) ⇓ t -> b = true.
Proof.
  destruct b. easy.
  unfold trueOrDiverge. intros (R&l).
  edestruct Omega_diverge with (t:=t).  
  assert (H':t == Omega).
  {rewrite <- R. apply star_equiv. unfold enc;cbn. etransitivity. now Lbeta. apply step_star. constructor. }
  now rewrite <- H'.
Qed.

#[global]
Instance eqbComp_bool : eqbCompT bool.
Proof.
  evar (c:nat). exists c. unfold Bool.eqb.
  unfold enc;cbn.
  extract.
  solverec.
  [c]:exact 3.
  all:unfold c;try lia.
Qed.

Lemma eqbTime_le_l X {R : encodable X} (eqb : X -> X -> bool) {H : eqbClass eqb}
      {H' : eqbCompT X} x n':
  eqbTime (X:=X) x n' <= x * c__eqbComp X.
Proof.
  unfold eqbTime. rewrite Nat.le_min_l. easy.
Qed.

Lemma eqbTime_le_r X (R : encodable X) (eqb : X -> X -> bool) (H : eqbClass eqb)
      (eqbCompT : eqbCompT X) x n':
  eqbTime (X:=X) n' x <= x * c__eqbComp X.
Proof.
  unfold eqbTime. rewrite Nat.le_min_r. easy.
Qed.
