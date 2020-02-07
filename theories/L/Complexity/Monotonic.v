From smpl Require Import Smpl.
From Undecidability Require Import L.Prelim.MoreBase.
Definition monotonic (f:nat -> nat) : Prop :=
  forall x x', x <= x' -> f x <= f x'.

Lemma monotonic_c c: monotonic (fun _ => c).
Proof.
  hnf.
  intros **. easy.
Qed.


Lemma monotonic_add f1 f2: monotonic f1 -> monotonic f2 -> monotonic (fun x => f1 x + f2 x).
Proof.
  unfold monotonic.
  intros H1 H2 **.
  rewrite H1,H2. reflexivity. all:eassumption.
Qed.

Lemma monotonic_mul f1 f2: monotonic f1 -> monotonic f2 -> monotonic (fun x => f1 x * f2 x).
Proof.
  unfold monotonic.
  intros H1 H2 **.
  rewrite H1,H2. reflexivity. all:eassumption.
Qed.

Require Import Nat.
Lemma monotonic_pow_c f1 c: monotonic f1  -> monotonic (fun x => (f1 x) ^ c).
Proof.
  intros **. 
  unfold monotonic.
  intros H1 **. eapply PeanoNat.Nat.pow_le_mono_l. apply H. easy.
Qed.

Lemma monotonic_x: monotonic (fun x => x).
Proof.
  unfold monotonic. easy.
Qed.

Lemma monotonic_comp f1 f2: monotonic f1 -> monotonic f2 -> monotonic (fun x => f1 (f2 x)). 
Proof.
  unfold monotonic.
  intros H1 H2 **.
  rewrite H1. reflexivity. eauto.
Qed.

Smpl Create monotonic.
Smpl Add 10 (first [ simple eapply monotonic_add | simple eapply monotonic_mul | simple eapply monotonic_c | simple eapply monotonic_x | simple eapply monotonic_pow_c] )  : monotonic.

Smpl Add 20 (lazymatch goal with
               |- monotonic (fun x => ?f (@?g x)) =>
               (lazymatch g with
               | fun x => x => fail
               | _ => simple eapply monotonic_comp
               end)
             end) : monotonic.

(*
Inductive TTnat: Type -> Type :=
  TTnatBase : TTnat nat
| TTnatArr X Y (ttx : TTnat X) (tty : TTnat Y) : TTnat (X -> Y).

Arguments TTnatArr _ _ {_ _}.
Existing Class TTnat.
Existing Instances TTnatBase TTnatArr.


Fixpoint leHO {ty} {tt : TTnat ty} : ty -> ty -> Prop :=
  match tt with
    TTnatBase => le
  | TTnatArr X Y => respectful (@leHO X _) (@leHO Y _)
  end.
Arguments leHO : simpl never.

(*
Instance leHO_Pointwise_le X Y (ttx : TTnat X) (tty : TTnat Y) (f g : X -> Y):
  Proper 
  Pointwise (@leHO _ ttx ==> leqHO _ tty).*)

Notation "'monotonicHO'" := (Proper leHO) (at level 0).

(*)
Lemma leHO_monotonic (f : nat -> nat) :
  monotonic f <-> monotonicHO f.
Proof.
  reflexivity.
Qed.

Module test.
  Variable f : nat -> nat -> nat.
  Context {Hf : monotonicHO f}.

  Goal forall x y y', y <= y' -> f x y <= f x y'.
  Proof.
    pose Hf.
    intros. now setoid_rewrite H.
  Qed.
End test.

*)*)
