From Undecidability.L Require Import Tactics.LTactics Prelim.MoreList Prelim.MoreBase Datatypes.LNat.
From Complexity.L.Datatypes Require Import LBinNums.
From Complexity.Complexity Require Export Monotonic ONotation LinTimeDecodable.

(** * Basics of decision problems *)

Record decInTime {X} `{R :encodable X} P (fT : nat -> nat) :Type :=
  decInTime_intro
  {
    f__decInTime : X -> bool ;
    compIn__decInTime : computableTime (ty:=TyArr (TyB X) (TyB bool)) f__decInTime (fun x _ => (fT (size (enc x)),tt)) ;
    correct__decInTime : forall x, P x <-> f__decInTime x  = true
  }.

#[export]
Hint Extern 1 (computableTime (f__decInTime _) _) => solve [unshelve (simple apply @compIn__decInTime)] :typeclass_instances.

Lemma complete__decInTime {X} `{R :encodable X} P (fT : nat -> nat) (P__dec:decInTime P fT) :
  forall (x:X), P x -> f__decInTime P__dec x  = true.
Proof.
  apply correct__decInTime.
Qed.

Lemma sound__decInTime X {R : encodable X} (P : X -> Prop) (fT : nat -> nat) (P__dec:decInTime P fT) :
  forall x, f__decInTime P__dec x = true -> P x.
Proof.
   apply correct__decInTime.
Qed.


Lemma decInTime_equiv X `{R :encodable X} (P : X -> Prop) (Q:X -> Prop) (fT : nat -> nat) :
  (forall (x:X), Q x <-> P x)
  -> decInTime P fT
  -> decInTime Q fT.
Proof.
  intros Hx dP. eexists. now apply compIn__decInTime with (d:=dP).
  intros x. now specialize (correct__decInTime dP x) as <-.
Qed.

Definition inTimeO {X} `{R :encodable X} `(P: X -> Prop) f :=
  exists f', inhabited (decInTime P f') /\ f' ∈O f.

Notation "P ∈TimeO f" := (inTimeO P f) (at level 70).

Definition inTimeo {X} `{R :encodable X} `(P: X -> Prop) f :=
  exists f', inhabited (decInTime P f') /\ f' ∈o f.

Notation "P ∈Timeo f" := (inTimeo P f) (at level 70).


(** Properties *)

(** Inclusion *)
Lemma inTime_mono f g X (_ : encodable X):
  f ∈O g -> forall `(P:X -> Prop), P ∈TimeO f -> P ∈TimeO g.
Proof.
  intros H P (?&?&?). unfold inTimeO.
  eexists _. split. eassumption. now rewrite H1.
Qed.

(** *** Time Constructibility *)
(** TODO: As we might want to project out the term, we don't use inTimeO to avoid the elim-restriction... *)
Definition timeConstructible (f:nat -> nat) := Eval cbn [timeComplexity] in
      { f' : nat -> nat &
                 (f' ∈O f)
                 * computableTime' (fun n => N.of_nat (f n)) (fun n _ => (f' n,tt))}%type.

Definition timeConstructible_computableTime' f (H:timeConstructible f) :
  computableTime' (fun n => N.of_nat (f n)) (fun n _ => (projT1 H n,tt))
  := snd (projT2 H).

Definition timeConstructible_inO f (H:timeConstructible f) :
  projT1 H ∈O f := fst (projT2 H).

Record resSizePoly X Y `{encodable X} `{encodable Y} (f : X -> Y) : Type :=
  {
    resSize__rSP : nat -> nat;
    bounds__rSP : forall x, size (enc (f x)) <= resSize__rSP (size (enc x));
    poly__rSP : inOPoly resSize__rSP;
    mono__rSP : Proper (le ==> le) resSize__rSP;
  }.

Smpl Add 10 (simple apply poly__rSP) : inO.

#[global]
Instance monotonic_rSP X Y `{encodable X} `{encodable Y} (f : X -> Y) (rsp: resSizePoly f):
  Proper (le ==> le) (resSize__rSP rsp).
Proof. apply mono__rSP. Qed.

Record polyTimeComputable X Y `{encodable X} `{encodable Y} (f : X -> Y) :=
  polyTimeComputable_intro
  {
    time__polyTC : nat -> nat;
    comp__polyTC : computableTime' f (fun x (_ : unit) => (time__polyTC (size (enc x)),tt));
    poly__polyTC : inOPoly time__polyTC ;
    mono__polyTC : Proper (le ==> le) time__polyTC;
    resSize__polyTC :> resSizePoly f;
  }.

#[global]
Instance monotonic_polyTC X Y `{encodable X} `{encodable Y} (f : X -> Y) (ptc: polyTimeComputable f):
  Proper (le ==> le) (time__polyTC ptc).
Proof. apply mono__polyTC. Qed.

#[export]
Hint Extern 1 (computableTime _ _) => unshelve (simple apply @comp__polyTC);eassumption :typeclass_instances.

Smpl Add 10 (simple apply poly__polyTC) : inO.

Import Nat.

Definition c__powBound := c__pow2 + c__mult. 
Lemma pow_time_bound x y : pow_time x y <= (S y) * x^y * c__powBound + y * S x * 2 * c__powBound.
Proof. 
  induction y as [ | y IH]; cbn -[Nat.add Nat.mul].
  - unfold c__powBound. lia. 
  - rewrite IH. 
    destruct x; cbn -[Nat.add Nat.mul]. 
    + unfold mult_time, c__powBound. destruct y; cbn -[c__pow2 c__mult]; nia. 
    + unfold mult_time, c__powBound. cbn [pow]. lia. 
Qed.

Lemma inOPoly_computable (f:nat -> nat):
  inOPoly f ->
  exists f':nat -> nat, inhabited (polyTimeComputable f') /\
                        (forall x, f x <= f' x) /\ inOPoly f' /\ Proper (le ==> le) f'.
Proof.
  intros (i&Hf).
  eapply inO__bound in Hf as (c&Hf).
  exists (fun n => c + c*n^i). split.
  -evar (time : nat -> nat). [time]:intros n0.
   split. exists time.
   {extract. solverec. rewrite pow_time_bound. 
     unfold mult_time. 
    rewrite Nat.pow_le_mono_l. 2:now apply LNat.size_nat_enc_r.
    rewrite (LNat.size_nat_enc_r x) at 2.
    set (n0:= (size (enc x))). unfold time. reflexivity.
   }
   + unfold time. smpl_inO.
   + unfold time. solve_proper.
   + eexists.
     * intro x. rewrite (LNat.size_nat_enc) at 1.
       rewrite Nat.pow_le_mono_l by apply (LNat.size_nat_enc_r).
       set (size (enc x)). instantiate (1:= fun n0 => _). cbn beta;reflexivity.
     * smpl_inO.
     * solve_proper.
   - repeat split.
     + easy.
     + smpl_inO.
     + solve_proper.
Qed.

Lemma resSizePoly_compSize X Y `{encodable X} `{encodable Y} (f: X -> Y):
  resSizePoly f -> exists H : resSizePoly f, inhabited (polyTimeComputable (resSize__rSP H)).
Proof.
  intros R__spec. destruct (inOPoly_computable (poly__rSP R__spec)) as (p'&[?]&Hbounds&?&?).
  unshelve eexists.
  exists p'.
  2-4:now eauto using resSize__polyTC. intros. rewrite bounds__rSP. easy.
Qed.

Lemma polyTimeComputable_compTime X Y `{encodable X} `{encodable Y} (f: X -> Y):
  polyTimeComputable f -> exists H : polyTimeComputable f, inhabited (polyTimeComputable (time__polyTC H))
                                                     /\ inhabited (polyTimeComputable (resSize__rSP H)).
Proof.
  intros R__spec. destruct (inOPoly_computable (poly__polyTC R__spec)) as (p'&[?]&Hbounds&?&?).
  destruct (resSizePoly_compSize R__spec) as (?&[]).
  unshelve eexists.
  exists p'.
  2-5:now eauto. eexists. eapply computesTime_timeLeq. 2:now apply extTCorrect.
  intros ? ?;cbn. now rewrite Hbounds.
Qed.

Import Functions.Decoding LTerm LOptions.
Lemma linDec_polyTimeComputable  X `{_:linTimeDecodable X}: polyTimeComputable (decode X).
Proof.
  evar (time:nat -> nat). [time]:intro n.
  exists time.
  -eexists _. 
   eapply computesTime_timeLeq.
   2:now eapply comp_enc_lin.
   intros x _;cbn [fst snd]. split.
   2:easy.
   rewrite size_term_enc_r. generalize (size (enc x)) as n;intros.
   unfold time. reflexivity.
  - unfold time. smpl_inO.
  - unfold time. solve_proper.
  -{evar (resSize : nat -> nat). [resSize]:intro n.
    exists resSize.
    -intros t.
     specialize (decode_correct2 (X:=X) (t:=t)) as H'.
     destruct decode.
     specialize (H' x Logic.eq_refl). rewrite <- H'.
     *rewrite size_option,LTerm.size_term_enc_r.
      generalize (size (enc (enc x))). unfold resSize. reflexivity.
     *unfold enc at 1. cbn. unfold resSize. nia.
    - unfold resSize. smpl_inO.
    - unfold resSize. solve_proper.
   }
Qed.
