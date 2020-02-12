From Undecidability.L Require Import Tactics.LTactics Prelim.MoreList Prelim.MoreBase Datatypes.LBinNums.
From Undecidability.L.Complexity Require Export Monotonic ONotation.

Inductive is_computable_time {A} {t : TT A} (a : A) fT : Prop :=
  C : computableTime a fT -> is_computable_time a fT.

(* TODO: It would be interesting to understand why we can't use sigma types.*)

(** Semantics for [[restrictedP]]: fst is the subset of X which is an admsisable input, second is the Problem itself. *)
Definition restrictedP X := (X -> Prop*Prop).
Definition restrictBy {X} vX P : restrictedP X:= fun (x:X) => (vX x,P x).
(* Notation "vX '@With' P" := (restrPWhere vX P) (at level 0, P at level 0). *)


Definition unrestrictedP {X} P : restrictedP X := restrictBy (fun _ => True) P.

Local Set Warnings "-cannot-define-projection".
Record decInTime {X} `{R :registered X} (P : restrictedP X) (fT : nat -> nat) :Prop :=
  decInTime_intro
  {
    decInTime_decP : X -> bool ;
    decInTime_compIn : is_computable_time (t:=TyArr (TyB X) (TyB bool)) decInTime_decP (fun x _ => (fT (L.size (enc x)),tt)) ;
    decInTime_correct : forall x, fst (P x) -> snd (P x) <-> decInTime_decP x  = true
  }.


Lemma decInTime_restriction_antimono X `{R :registered X} (P Q:restrictedP X) (fT : nat -> nat) :
  (forall x, fst (Q x) -> fst (P x))
  -> (forall x, fst (Q x) -> snd (P x) <-> snd (Q x))
  -> decInTime P fT
  -> decInTime Q fT.
Proof.
  intros Hf Hs [decO compIn correct]. eexists. eauto.
  intros ? ?. rewrite <- correct.
  -now rewrite Hs.
  -now apply Hf.
Qed.

Definition inTimeO {X} `{R :registered X} P f :=
  exists f', decInTime P f' /\ f' ∈O f.

Notation "P ∈TimeO f" := (inTimeO P f) (at level 70).

Definition inTimeo {X} `{R :registered X} P f :=
  exists f', decInTime P f' /\ f' ∈o f.

Notation "P ∈Timeo f" := (inTimeo P f) (at level 70).


(** Properties *)

(** Inclusion *)
Lemma inTime_mono f g X (_ : registered X):
  f ∈O g -> forall P, P ∈TimeO f -> P ∈TimeO g.
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


Class computableInO {X Y} `{registered X} `{registered Y} (f:X -> Y) (g: nat -> nat) : Type:=
  {
    fT_inO : nat -> nat;
    compO : computableTime' f (fun x _ => (fT_inO (size (enc x)),tt));
    lin_t__enc : fT_inO ∈O g;
    mono_t__enc : monotonic fT_inO;
  }.

Smpl Add (simple apply mono_t__enc) : monotonic.

Lemma smpl_fT_inO X Y `{registered X} `{registered Y} (f: X -> Y) (g:nat -> nat) {H':computableInO f g} h:
  g ∈O h -> (fT_inO ∈O h).
Proof.
  intros <-. apply lin_t__enc. 
Qed.

Smpl Add simple eapply smpl_fT_inO : inO.



Lemma smpl_inOPoly_fT_inO X Y `{registered X} `{registered Y} (f: X -> Y) (g:nat -> nat) {H':computableInO f g}:
  inOPoly g -> inOPoly fT_inO.
Proof.
  intros. now rewrite lin_t__enc.
Qed.

Lemma inOPoly_computable (f:nat -> nat):
  inOPoly f -> exists (f':nat -> nat) f__T, is_computable_time (t:=TyArr _ _) f' (fun n _ => (f__T n,tt)) /\ inOPoly f__T /\ (forall x, f x <= f' x) /\ inOPoly f' /\ monotonic f' /\ monotonic f__T.
Proof.
  intros (i&Hf).
  eapply inO__bound in Hf as (c&Hf).
  exists (fun n => c + c*n^i),(fun n => 19 * i * n + 11 * i * n ^ i + 19 * i + 11 * n ^ i * c + 30 * c + 29).
  split;split. 3:split;[easy|repeat split].
  1:{ extract. solverec. }
  all:smpl_inO.
  all: eexists i; easy.
Qed.


Smpl Add 12 simple eapply smpl_inOPoly_fT_inO : inO.


Record polyTimeComputable X Y `{registered X} `{registered Y} (f : X -> Y): Prop :=
  polyTimeComputable_intro
  {
    polyTimeC__t : nat -> nat;
    polyTimeC__comp : is_computable_time (t:=TyArr _ _) f (fun x _ => (polyTimeC__t (L.size (enc x)),tt));
    polyTimeC__polyTime : inOPoly polyTimeC__t ;
    polyTimeC__mono : monotonic polyTimeC__t;
    polyTimeC__polyRes : exists f', (forall x, size (enc (f x))
                                             <= f' (size (enc x)) ) /\ inOPoly f' /\ monotonic f'
  }.
