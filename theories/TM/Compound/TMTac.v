From Undecidability.TM Require Export Compound.TMTac.
From Complexity.TM Require Import Lifting.LiftTapes Code.CodeTM Code.ChangeAlphabet. (* these define tactics we want to call *)
From Complexity.TM Require Export TM_facts.
Tactic Notation "TMSimp" := TMSimp (simpl_not_in; cbn in *).
Ltac destruct_tapes := unfold tapes in *; destruct_vector.

(* This tactic automatically solves/instantiates premises of a hypothesis. If the hypothesis is a conjunction, it is destructed. *)
Ltac modpon' H :=
  simpl_surject;
  once lazymatch type of H with
  | forall (i : Fin.t _), ?P => idtac
  | forall (x : ?X), ?P =>
    once lazymatch type of X with
    | Prop =>
      tryif spec_assert H by
          (simpl_surject;
           solve [ eauto
                 | contains_ext
                 | isVoid_mono
                 ]
          )
      then idtac (* "solved premise of type" X *);
           modpon' H
      else (spec_assert H;
            [ idtac (* "could not solve premise" X *) (* new goal for the user *)
            | modpon' H (* continue after the user has proved the premise manually *)
            ]
           )
    | _ =>
      (* instantiate variable [x] with evar *)
      let x' := fresh "x" in
      evar (x' : X); specialize (H x'); subst x';
      modpon' H
    end
  | ?X /\ ?Y =>
    let H' := fresh H in
    destruct H as [H H']; modpon' H; modpon' H'
  | _ => idtac
  end.

Ltac modpon H := progress (modpon' H).

(* DO NOT USE THE FOLLOWING (deprecated) TACTICS, except in [TM.Compound]! *)

Tactic Notation "TMBranche" :=
  (
    match goal with
    | [ H : context [ match ?x with _ => _ end ] |- _ ] => let E := fresh "E" in destruct x eqn:E
    | [   |- context [ match ?x with _ => _ end ]     ] => let E := fresh "E" in destruct x eqn:E
    | [ H : _ \/ _ |- _] => destruct H
    | [ IH : ?P -> ?Q |- _] =>
      match type of P with
      | Prop => spec_assert IH; [ clear IH | ]
      end

    | [ x : bool        |- _ ] => destruct x
    | [ x : option _ |- _ ] => destruct x

    | [   |- ex ?P    ] => eexists
    | [ H : _ \/ _ |- _] => destruct H
    end
  ).

Tactic Notation "TMSolve" int_or_var(k) :=
  repeat progress first [
           match goal with
           | [ |- (_ ::: _) = (_ ::: _) ] => f_equal
           | [ |- Some _ = Some _ ] => f_equal
           | [ |- _ /\ _ ] => split
           end
           || congruence
           || eauto k
         ].

Tactic Notation "TMCrush" tactic(T) :=
  repeat progress
         (
         TMSimp (simpl_not_in; cbn in *; T);
           try TMBranche
         ).

Tactic Notation "TMCrush" :=
  repeat progress
         (
           TMSimp;
           try TMBranche
         ).
