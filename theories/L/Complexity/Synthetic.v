From Undecidability.L Require Import Tactics.LTactics Prelim.MoreList Prelim.MoreBase Datatypes.LBinNums Datatypes.LNat.
From Undecidability.L.Complexity Require Export Monotonic ONotation LinTimeDecodable.

Global Generalizable Variable vX.

(** * Basics of decision problems *)

(** Semantics for [[restrictedP]]: fst is the subset of X which is an admsisable input, second is the Problem itself. *)
Definition restrictedP {X} vX := ({x:X | vX x} -> Prop).
(* Notation "vX '@With' P" := (restrPWhere vX P) (at level 0, P at level 0). *)

Definition restrictBy {X} vX (P:X->Prop) : restrictedP vX := fun '(exist x _) => P x.
Arguments restrictBy : clear implicits.
Arguments restrictBy {_} _ _ !_.

Definition unrestrictedP {X} (P:X->Prop) : restrictedP (fun _ => True) := restrictBy _ P.
Arguments unrestrictedP X P !x.

Record decInTime {X} `{R :registered X} `(P : restrictedP vX) (fT : nat -> nat) :Type :=
  decInTime_intro
  {
    f__decInTime : X -> bool ;
    compIn__decInTime : computableTime (ty:=TyArr (TyB X) (TyB bool)) f__decInTime (fun x _ => (fT (L.size (enc x)),tt)) ;
    correct__decInTime : forall x (Hx : vX x), P (exist _ x Hx) <-> f__decInTime x  = true
  }.

Hint Extern 1 (computableTime (f__decInTime _) _) => solve [unshelve (simple apply @compIn__decInTime)] :typeclass_instances.

Lemma complete__decInTime {X} `{R :registered X} `{P : restrictedP vX} (fT : nat -> nat) (P__dec:decInTime P fT) :
  forall (x:X) (Hx : vX x), P (exist _ x Hx) -> f__decInTime P__dec x  = true.
  apply correct__decInTime.
Qed.

Lemma sound__decInTime {X} `{R :registered X} `(P : restrictedP vX) (fT : nat -> nat) (P__dec:decInTime P fT) :
  forall (x:sig (A:=X) vX), f__decInTime P__dec (proj1_sig x)  = true -> P x.
  intros []. apply correct__decInTime.
Qed.


Lemma decInTime_restriction_antimono X `{R :registered X} vP vQ (P : restrictedP vP) (Q:restrictedP vQ) (fT : nat -> nat) :
  (forall (x:X), vQ x -> vP x)
  -> (forall x H__P H__Q, P (exist vP x H__P) <-> Q (exist vQ x H__Q))
  -> decInTime P fT
  -> decInTime Q fT.
Proof.
  intros Hv Hx dP. eexists. apply compIn__decInTime with (d:=dP).
  intros x HQ. rewrite <- Hx with (H__P:=Hv _ HQ). apply correct__decInTime.
Qed.

Lemma decInTime_restriction_antimono_restrictBy X `{R :registered X} (vX vX' P : X -> Prop) (fT : nat -> nat):
  (forall x, vX' x -> vX x)
  -> decInTime (restrictBy vX  P) fT
  -> decInTime (restrictBy vX' P) fT.
Proof.
  intros ?. apply decInTime_restriction_antimono. easy. cbn. easy.
Qed.

Definition inTimeO {X} `{R :registered X} `(P:restrictedP (X:=X) vX) f :=
  exists f', inhabited (decInTime P f') /\ f' ∈O f.

Notation "P ∈TimeO f" := (inTimeO P f) (at level 70).

Definition inTimeo {X} `{R :registered X} `(P:restrictedP (X:=X) vX) f :=
  exists f', inhabited (decInTime P f') /\ f' ∈o f.

Notation "P ∈Timeo f" := (inTimeo P f) (at level 70).


(** Properties *)

(** Inclusion *)
Lemma inTime_mono f g X (_ : registered X):
  f ∈O g -> forall `(P:restrictedP (X:=X) vX), P ∈TimeO f -> P ∈TimeO g.
Proof.
  intros H P ? (?&?&?). unfold inTimeO.
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

Record resSizePoly X Y `{registered X} `{registered Y} (f : X -> Y) : Type :=
  {
    resSize__rSP : nat -> nat;
    bounds__rSP : forall x, size (enc (f x)) <= resSize__rSP (size (enc x));
    poly__rSP : inOPoly resSize__rSP;
    mono__rSP : monotonic resSize__rSP;
  }.

Smpl Add 10 (simple apply poly__rSP) : inO.
Smpl Add 10 (simple apply mono__rSP) : inO.

Record polyTimeComputable X Y `{registered X} `{registered Y} (f : X -> Y) :=
  polyTimeComputable_intro
  {
    time__polyTC : nat -> nat;
    comp__polyTC : computableTime' f (fun x _ => (time__polyTC (L.size (enc x)),tt));
    poly__polyTC : inOPoly time__polyTC ;
    mono__polyTC : monotonic time__polyTC;
    resSize__polyTC :> resSizePoly f;
  }.

Hint Extern 1 (computableTime _ _) => unshelve (simple apply @comp__polyTC);eassumption :typeclass_instances.

Smpl Add 10 (simple apply poly__polyTC) : inO.
Smpl Add 10 (simple apply mono__polyTC) : inO.

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
  inOPoly f -> exists f':nat -> nat , inhabited (polyTimeComputable f') /\ (forall x, f x <= f' x) /\ inOPoly f' /\ monotonic f'.
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
   3:eexists.
   3:{intros. rewrite (LNat.size_nat_enc) at 1. rewrite Nat.pow_le_mono_l. 2:now apply (LNat.size_nat_enc_r). set (size (enc x)). instantiate (1:= fun n0 => _). cbn beta;reflexivity.
   }
   all:unfold time;smpl_inO.
   -repeat apply conj. easy. all:smpl_inO.
Qed.


Lemma resSizePoly_compSize X Y `{registered X} `{registered Y} (f: X -> Y):
  resSizePoly f -> exists H : resSizePoly f, inhabited (polyTimeComputable (resSize__rSP H)).
Proof.
  intros R__spec. destruct (inOPoly_computable (poly__rSP R__spec)) as (p'&[?]&Hbounds&?&?).
  unshelve eexists.
  exists p'.
  2-4:now eauto using resSize__polyTC. intros. rewrite bounds__rSP. easy.
Qed.

Lemma polyTimeComputable_compTime X Y `{registered X} `{registered Y} (f: X -> Y):
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
  -unfold time. smpl_inO.
  -unfold time. smpl_inO.
  -{evar (resSize : nat -> nat). [resSize]:intro n.
    exists resSize.
    -intros t.
     specialize (decode_correct2 (X:=X) (t:=t)) as H'.
     destruct decode.
     setoid_rewrite <- H'. 2:reflexivity.
     *rewrite size_option,LTerm.size_term_enc_r.
      generalize (size (enc (enc x))). unfold resSize. reflexivity.
     *unfold enc at 1. cbn. unfold resSize. nia.
    -unfold resSize. smpl_inO.
    -unfold resSize. smpl_inO.
   }
Qed.
