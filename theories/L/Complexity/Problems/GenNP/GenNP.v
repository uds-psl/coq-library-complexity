From Undecidability.L Require Import L.
From Undecidability.L.Datatypes Require Import LProd LTerm LBool.
From Undecidability.L.Complexity Require Import NP Synthetic Monotonic.
From Undecidability.L.Functions Require Import Size.

Local Unset Implicit Arguments.
Import L_Notations.

Section GenNP.
  Context (X__cert : Type) `{R__cert : registered X__cert}.

  Definition LHaltsOrDiverges : term*nat*nat -> Prop :=
    fun '(s, maxSize, steps (*in unary*)) =>
      proc s /\ forall (c:X__cert), size (enc c) <= maxSize -> forall k t, s (enc c) ⇓(k) t -> k <= steps.

  Definition GenNP : term*nat*nat -> Prop :=
               (fun '(s, maxSize, steps (*in unary*)) =>
                  exists (c:X__cert), size (enc c) <= maxSize
                               /\ exists t, app s (enc c) ⇓(<=steps) t).

End GenNP.

