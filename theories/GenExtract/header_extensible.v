(** * Chapter 7 : Modular Syntax *)

Require Import String List Omega.

Require Import Equations.Equations.
Set Implicit Arguments.
Unset Strict Implicit.

Arguments eq_refl {A x}, {A} x.


(** ** Tools for modular syntax with binders *)

(** *** Basic definitions  *)

Lemma size_ind (P : nat -> Prop) :
  (forall x, (forall y, y < x -> P y) -> P x) -> forall x, P x.
Proof.
  intros H x. apply H.
  induction x.
  - intros y. omega.
  - intros y. intros [] % le_lt_or_eq.
    + apply IHx; omega.
    + apply H. injection H0. now intros ->.
Qed.

Class retract X Y :=
  {
    retract_I : X -> Y ;
    retract_R : Y -> option X;
    retract_works : forall x, retract_R (retract_I x) = Some x;
    retract_tight : forall x y, retract_R y = Some x -> retract_I x = y
  }.

Arguments Build_retract {X} {Y}.

Lemma retract_inj {X Y} {R : retract X Y} x y :
  retract_I x = retract_I y -> x = y.
Proof.
  intros. enough (Some x = Some y) by congruence.
  now rewrite <- !retract_works, H.
Qed.

Instance retract_option X Y : retract X Y -> retract (option X) (option Y).
Proof.
  intros. unshelve eexists.
  - intros []. exact (Some (retract_I x)). exact None.
  - intros []. destruct (retract_R y). exact (Some (Some x)). exact None. exact (Some None).
  - intros []. cbn. now rewrite retract_works. reflexivity.
  - intros. cbn in *. destruct y.  destruct x.
    + destruct (retract_R y) eqn:E. inversion H. subst. clear H.
      eapply retract_tight in E. congruence. inversion H.
    + destruct (retract_R y) eqn:E. inversion H. inversion H.
    + inversion H. reflexivity.
Defined.

Definition lift {X Y Y'} `{retract Y Y'} (f : X -> Y) := (fun n => retract_I (f n)).
Notation inj := (retract_I).
Notation retr := (retract_R).

Notation included F T := (retract (F T) T)%type.

Class Bundle (func : Type -> Type) (In : forall X, X -> func X -> Prop) := make_Bundle {}.
Existing Instance make_Bundle.

Definition get_In {func In} {bundle : @Bundle func In} := In.

Lemma congr_inj {X Y} `{retract X Y} {x y}:
  x = y -> inj x = inj y.
Proof.
  congruence.
Qed.

Lemma Some_inj {X} {x y : X} :
  Datatypes.Some x = Datatypes.Some y -> x = y.
Proof. congruence. Qed.

Lemma some_none_explosion {X : Type} {x : X} {H : Prop} :
  Datatypes.None = Datatypes.Some x  -> H.
Proof. intros A. congruence. Qed.
