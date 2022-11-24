Require Export Complexity.L.Datatypes.LDepPair.
From Undecidability Require Import LTactics.
From Complexity Require Import Definitions NP PolyTimeComputable.

(* this notion allows to restrict a problem of a subset of the domain*)
Definition restrictBy {X} (validX P:X->Prop) : { x:X | validX x} -> Prop := fun '(exist x _) => P x.
Arguments restrictBy {_} _ _ !_.




Lemma polyTimeComputable_sig_in X Y `(encodable X) `(encodable Y) P f' (f:{x:X|P x} -> Y):
  (forall x Hx, f' x = f (exist P x Hx))
  -> polyTimeComputable f'
  -> polyTimeComputable f.
Proof.
  intros Hext [time Hcomp]. exists (fun x => time x +2).
  - apply computableTimeExt with (x:=fun x => f' (proj1_sig x)) (x':=f).
    + intros []; cbn. apply Hext.
    + extract. solverec. reflexivity.
  - smpl_inO.
  - solve_proper.
  - eexists (resSize__rSP resSize__polyTC).
    + intros []. rewrite <- Hext. rewrite bounds__rSP, enc_sig_exist_eq. reflexivity.
    + apply poly__rSP.
    + apply mono__rSP.
Qed.

Lemma polyTimeComputable_sig_out X Y {RX: encodable X} {RY:encodable Y} validY (f : X -> {y:Y | validY y}):
  polyTimeComputable (fun x => proj1_sig (f x))
  -> polyTimeComputable f.
Proof.
  intros H. exists (time__polyTC H).
  - computable_casted_result. eauto.
  - apply poly__polyTC.
  - apply mono__polyTC.
  - exists (resSize__rSP H). 2,3:now smpl_inO.
    intro. rewrite <- bounds__rSP, enc_sig_eq. reflexivity.
Qed.

Lemma reducesPolyMO_intro_restrictBy_out X Y `{RX: encodable X} `{RY:encodable Y}
  (P : X -> Prop) (validY Q:Y->Prop) (f:X -> Y):
    polyTimeComputable f
    -> (forall x , {Hfx : validY (f x) | P x <-> Q (f x)})
    -> P ⪯p restrictBy validY Q.
Proof.
  intros H H'. exists (fun x => exist _ (f x) (proj1_sig (H' x))).
  - now apply polyTimeComputable_sig_out.
  - intros x. all: now destruct H'.
Qed.

Lemma reducesPolyMO_intro_restrictBy_in X Y `{RX: encodable X} `{RY:encodable Y}
  (validX P : X -> Prop) Q (f:X -> Y):
    polyTimeComputable f
    -> (forall x (H : validX x) , P x <-> Q (f x))
    -> restrictBy validX P ⪯p Q.
Proof.
  intros H H'. unshelve eexists (fun x => f (proj1_sig x)).
  - eapply polyTimeComputable_sig_in. 2:easy. reflexivity.
  - unfold restrictBy. intros []. now apply H'.
Qed.

Lemma reducesPolyMO_intro_restrictBy_both X Y `{RX: encodable X} `{RY:encodable Y}
  (validX P : X -> Prop) (validY Q:Y->Prop) (f:X -> Y):
    polyTimeComputable f
    -> (forall x (H : validX x) , {Hfx : validY (f x) | P x <-> Q (f x)})
    -> restrictBy validX P ⪯p restrictBy validY Q.
Proof.
  intros H H'. eapply reducesPolyMO_intro_restrictBy_out with (f := fun '(exist x _) => f x).
  - eapply polyTimeComputable_sig_in. reflexivity. easy.
  - unfold restrictBy. intros []. easy.
Qed.